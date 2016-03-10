requires domains.k

module IMP-SYNTAX-COMMON
  import DOMAINS
  syntax AExp  ::= Int | Id
                 | AExp "/" AExp              [left, strict]
                 > AExp "+" AExp              [left, strict]
                 | "(" AExp ")"               [bracket]
  syntax BExp  ::= Bool
                 | AExp "<=" AExp             [seqstrict, latex({#1}\leq{#2})]
                 | "!" BExp                   [strict]
                 > BExp "&&" BExp             [left, strict(1)]
                 | "(" BExp ")"               [bracket]
  syntax Block ::= "{" "}"
                 | "{" Stmt "}"
  syntax Stmt  ::= Block
                 | Id "=" AExp ";"            [strict(2)]
                 | "if" "(" BExp ")"
                   Block "else" Block         [strict(1)]
                 | "while" "(" BExp ")" Block
                 > Stmt Stmt                  [left]
  syntax Pgm ::= "int" Ids ";" Stmt
  syntax Ids
endmodule

module IMP-SYNTAX-PROGRAM-PARSING
  import ID-PROGRAM-PARSING
  import IMP-SYNTAX-COMMON
  syntax Ids ::= "" | NeIds
  syntax NeIds ::= Id | NeIds "," Id
endmodule

module IMP-SYNTAX
  import IMP-SYNTAX-COMMON
  syntax Ids ::= .Ids | Id | Ids "," Ids [assoc, unit(.Ids)]
endmodule

module IMP-SYNTAX-TRANSLATE
  import IMP-SYNTAX-PROGRAM-PARSING
  import IMP-SYNTAX
  syntax Ids ::= translate(Ids)
  rule translate() => .Ids
  rule translate(X:Id) => X
  rule translate(Xs:NeIds, X:Id) => translate(Xs), X
endmodule

module IMP
  imports IMP-SYNTAX
  syntax KResult ::= Int | Bool

  rule #krun(Init:Map) => initTopCell(Init)  [macro]
  // previously, we had another attribute, "topcell".  I prefer the above, though,
  // because it reduces the syntax of KORE on the one hand, and gives us more
  // flexibility on the other hand.  For example, we may have multiple rules like
  // above, depending upon the arguments passed to krun.

  syntax TopCell ::= "<T>" KCell StateCell "</T>"  [structural, color(yellow)]
                   | initTopCell(Map)
  rule initTopCell(Init:Map) => <T> initKCell(Init:Map) initStateCell </T>

  syntax KCell ::= "<k>" K "</k>"  [maincell, structural, color(green)]
  // instead of "maincell" above, we may want to define arbitrary contexts,
  // somewhat similar to strict; e.g.: syntax K ::= K "~>" K [structural(0,2)]
  // meaning that the operation itself (0) and the second argument (2) are inferred,
  // so they need not be mentioned.
                 | initKCell(Map)
  rule initKCell(Init:Map) => <k> #rewrite(IMP-SYNTAX-TRANSLATE,
                                           #parse(IMP-SYNTAX-PARSING,
                                                  Init[$PGM])) </k>
  syntax StateCell ::= "<state>" Map "</state>"  [structural, color(red)]
                     | "initStateCell"
  rule initStateCell => <state> .::Map </state>

// AExp
  rule <k> X:Id => I ...</k> <state>... X |-> I ...</state>
  rule I1 / I2 => I1 /Int I2  requires I2 =/=Int 0
  rule I1 + I2 => I1 +Int I2
// BExp
  rule I1 <= I2 => I1 <=Int I2
  rule ! T => notBool T
  rule true && B => B
  rule false && _ => false
// Block
  rule {} => .   [structural]
  rule {S} => S  [structural]
// Stmt
  rule <k> X = I:Int; => . ...</k> <state>... X |-> (_ => I) ...</state>
  rule S1:Stmt S2:Stmt => S1 ~> S2  [structural]
  rule if (true)  S else _ => S
  rule if (false) _ else S => S
  rule while (B) S => if (B) {S while (B) S} else {}  [structural]
// Pgm
  rule <k> int (X,Xs => Xs);_ </k> <state> Rho:Map (.Map => X|->0) </state>
    requires notBool (X in keys(Rho))
  rule int .Ids; S => S  [structural]
endmodule

