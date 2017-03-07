// Copyright (c) 2012-2016 K Team. All Rights Reserved.

require "substitution.k"

module LAMBDA
  imports SUBSTITUTION
  syntax Val ::= Id
               | "lambda" Id "." Exp  [binder, latex(\lambda{#1}.{#2})]
  syntax Exp ::= Val
               | Exp Exp              [strict, left]
               | "(" Exp ")"          [bracket]
  syntax KVariable ::= Id
  syntax KResult ::= Val

  rule (lambda X:Id . E:Exp) V:Val => E[V / X]

  syntax Val ::= Int | Bool
  syntax Exp ::= Exp "*" Exp          [strict, left]
               | Exp "/" Exp          [strict]
               > Exp "+" Exp          [strict, left]
               > Exp "<=" Exp         [strict]
  rule I1 * I2 => I1 *Int I2
  rule I1 / I2 => I1 /Int I2
  rule I1 + I2 => I1 +Int I2
  rule I1 <= I2 => I1 <=Int I2

  syntax Exp ::= "if" Exp "then" Exp "else" Exp  [strict(1)]
  rule if true  then E else _ => E
  rule if false then _ else E => E

  syntax Exp ::= "let" Id "=" Exp "in" Exp
  rule let X = E in E':Exp => (lambda X . E') E                        [macro]

  syntax Exp ::= "letrec" Id Id "=" Exp "in" Exp
               | "mu" Id "." Exp                 [binder, latex(\mu{#1}.{#2})]
  rule letrec F:Id X = E in E' => let F = mu F . lambda X . E in E'    [macro]
  rule mu X . E => E[(mu X . E) / X]

  syntax Exp ::= "callcc" Exp [strict]
  syntax Exp ::= "callCC" Exp [strict]

  syntax Val ::= cc(K)
  syntax Val ::= CC(K)

  rule <k> (callcc V:Val => V cc(K)) ~> K </k>
  rule <k> cc(K) V:Val ~> _ => V ~> K </k>
  rule <k> V:Val cc(K) ~> _ => V ~> K </k>

  rule <k> (callCC V:Val) ~> K => V CC(K) </k>
  rule <k> CC(K) V:Val ~> _ => callcc V ~> K </k>
endmodule
