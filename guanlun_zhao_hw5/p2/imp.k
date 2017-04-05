// Copyright (c) 2014-2016 K Team. All Rights Reserved.

module IMP-SYNTAX
  syntax ES    ::= AExp | BExp | Stmt
  syntax AExp  ::= Int | String | Id
                 | "++" Id
                 | "read" "(" ")"
                 > AExp "/" AExp              [left, strict, division]
                 > AExp "+" AExp              [left, strict]
                 > "spawn" Block
                 | "atomic" Block
                 > Id "=" AExp                [strict(2)]
                 | "(" AExp ")"               [bracket]
  syntax BExp  ::= Bool
                 | AExp "<=" AExp             [seqstrict, latex({#1}\leq{#2})]
                 | "!" BExp                   [strict]
                 > BExp "&&" BExp             [left, strict(1)]
                 | "(" BExp ")"               [bracket]
  syntax Block ::= "{" Stmts "}"
  syntax Stmt  ::= Block
                 | AExp ";"                   [strict]
                 | "if" "(" BExp ")"
                   Block "else" Block         [strict(1)]
                 | "while" "(" BExp ")" Block
                 | "int" Ids ";"
                 | "print" "(" AExps ")" ";"
                 | "halt" ";"
                 > "join" AExp ";"            [strict]
                 | "hold" ";"
                 | "break-atomic" ";"
                 | "atomic-end" ";"

  syntax Ids   ::= List{Id,","}
  syntax AExps ::= List{AExp,","}
  syntax Stmts ::= List{Stmt,""}
endmodule

module IMP
  imports IMP-SYNTAX
  syntax KResult ::= Int | Bool | String

  configuration <T color="yellow">
                  <threads color="orange">
                    <thread multiplicity="*" color="blue">
                      <k color="green"> $PGM:Stmts </k>
                      <env color="LightSkyBlue"> .Map </env>
                      <id color="black"> 0 </id>
                    </thread>
                  </threads>

                  // Initialize Atomic to -1 to indicate there's no atomic thread
                  // at the beginning
                  <store color="red"> .Map["Atomic" <- -1] </store>

                  // The main thread (with ID 0)
                  <lookup> .Map[0 <- -1] </lookup>
                  <in color="magenta" stream="stdin"> .List </in>
                  <out color="Orchid" stream="stdout"> .List </out>
                </T>
// Insert a "hold" statement before any program construct in all the threads when an atomic
// thread is running.
  rule <thread>...
        <k> S => hold; ~> S ...</k>
        <id> T </id>
        ...
       </thread>
       <store>... "Atomic" |-> A ...</store>
       <lookup>... T |-> (J => A) ...</lookup>
       // Here T is the ID of the current thread, A is the ID of the atomic thread and
       // W is the ID of the thread the current thread is waiting for
       // Conditions:
       //   1. (A =/=Int -1)
       //   2. (A =/=Int T): Current thread is not the atomic thread
       //   3. (W =/=Int A) Current thread is not already waiting for that atomic thread
       requires (A =/=Int T) andBool (J =/=Int A) andBool (A =/=Int -1)
       
// AExp
  rule <k> X:Id => I ...</k>
       <env>... X |-> N ...</env>
       <store>... N |-> I ...</store>  [lookup]
  rule <k> ++X => I +Int 1 ...</k>
       <env>... X |-> N ...</env>
       <store>... N |-> (I => I +Int 1) ...</store>  [increment]
  rule <k> read() => I ...</k>
       <in> ListItem(I:Int) => .List ...</in>  [read]
  rule I1 / I2 => I1 /Int I2  requires I2 =/=Int 0
  rule I1 + I2 => I1 +Int I2
  rule Str1 + Str2 => Str1 +String Str2
// BExp
  rule I1 <= I2 => I1 <=Int I2
  rule ! T => notBool T
  rule true && B => B
  rule false && _ => false
// Block
  rule <k> {Ss} => Ss ~> Rho ...</k> <env> Rho </env>  [structural]
  rule <k> Rho => . ...</k> <env> _ => Rho </env>    [structural]
// Stmt
  rule _:Int; => .
  rule <k> X = I:Int => I ...</k>
       <env>... X |-> N ...</env>
       <store>... N |-> (_ => I) ...</store>  [assignment]
  rule if (true)  S else _ => S
  rule if (false) _ else S => S
  rule while (B) S => if (B) {S while (B) S} else {.Stmts}  [structural]

  rule <k> int (X,Xs => Xs); ...</k>
       <env> Rho => Rho[X <- !N:Int] </env>
       <store>... .Map => !N |-> 0 ...</store>
  rule int .Ids; => .  [structural]

  syntax Printable ::= Int | String
/* currently it is necessary to subsort Printable to AExp,
  but future K should be able to infer that automatically. */
  syntax AExp ::= Printable
  context print(HOLE:AExp, AEs:AExps);
  rule <k> print(P:Printable,AEs => AEs); ...</k>
       <out>... .List => ListItem(P) </out>  [print]
  rule print(.AExps); => .  [structural]

  rule <thread>...
        <k> hold; => . ...</k>
        <id> T </id>
        ...
       </thread>
       <store>... "Atomic" |-> A ...</store>
       <lookup>... T |-> J ...</lookup>
       requires (A ==Int -1)

  // When creating a new thread, insert an entry with the thread ID to the atomic lookup table.
  // This later allows us to track which thread is waiting for the atomic operations to finish.
  rule <k> spawn S => !T:Int ...</k>
       <env> Rho </env>
       <lookup>... .Map => !T |-> -1 ...</lookup>
       (.Bag => <thread>... <k> S </k> <env> Rho </env> <id> !T </id> ...</thread>) [spawn]
  rule <k> join(T:Int); => . ...</k>
       <thread>... <k> . </k> <id> T </id> ...</thread>

  // Creating an atomic operation is similar to creating a new thread.
  // First, mark the atomic thread ID flag with the ID of the atomic thread.
  // Then, store the contents of the current "store" and save it to "BackupStore" in case
  // we need to break the atomic action and restore the previous state.
  // Also, insert an "atomic-end" statement at the end of the atomic action to restore the
  // flags set here.
  rule <k> atomic S => !T:Int ...</k>
       <env> Rho </env>
       <store> Store => Store["Atomic" <- !T] </store>
       <lookup> Lookup => Lookup["SavedStore" <- Store] </lookup>
       (.Bag => <thread>... <k> S ~> atomic-end; </k> <env> Rho </env> <id> !T </id> ...</thread>) [atomic]

  // When ending the atomic operation, set the Atomic flag back to -1 to indicate no
  // atomic operation is going on anymore.
  rule <k> atomic-end; => . ...</k>
       <store>... "Atomic" |-> (_ => -1) ...</store>

  // "break-atomic" should end the current atomic operation and restore the previous saved
  // state.
  rule <k> break-atomic; ~> _ => . </k>
       <lookup>... "SavedStore" |-> O ...</lookup>
       <store> _ => O </store>

// Stmts
  rule .Stmts => .                 [structural]
  rule S:Stmt Ss:Stmts => S ~> Ss  [structural]

// verification ids
  syntax Id ::= "n"     [token]
              | "sum"   [token]

endmodule
