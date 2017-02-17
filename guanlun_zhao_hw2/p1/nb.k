module NB-SYNTAX
  syntax Term         ::= Val
                      | "if" Term "then" Term "else" Term           [strict(1)]
                      | "succ" Term                                 [strict(1)]
                      | "pred" Term                                 [strict(1)]
                      | "iszero" Term                               [strict(1)]
                      | "(" Term ")"                                [bracket]
  syntax Val          ::= Bool
                      | NV
  syntax NV           ::= "0"
                      | "succ" NV                                   [strict(1)]
endmodule

module NB
  imports NB-SYNTAX
  syntax KResult ::= Val

  rule iszero 0 => true
  rule iszero succ I => false
  rule pred 0 => 0
  rule pred succ I => I

  rule if true then T2 else T3 => T2
  rule if false then T2 else T3 => T3
endmodule
