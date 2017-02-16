module NB-SYNTAX
  syntax Term         ::= Val
                      | "if" Term "then" Term "else" Term
                      | "succ" Term                                 [left, strict]
                      | "pred" Term                                 [left, strict]
                      | "iszero" Term                               [left, strict]
                      | "(" Term ")"                                [bracket]
  syntax Val          ::= Bool
                      | NV
  syntax NV           ::= "0"
                      | "succ" NV                                   [strict]
endmodule

module NB
  imports NB-SYNTAX
  syntax KResult ::= Val

  rule iszero 0 => true
  rule iszero succ I => false
  rule pred 0 => 0

  rule if true then T2 else T3 => T2
  rule if false then T2 else T3 => T3
endmodule
