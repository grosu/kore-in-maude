
Working
=======

```maude
fmod CONSTRAINED-TERMS is
    protecting STRING .

    sorts Var KTerm Formula ConstrainedTerm .
    subsort Var < KTerm < ConstrainedTerm .
    sort REWTerm ConstrainedREWTerm .
    subsort REWTerm < ConstrainedREWTerm .

    op _==_ : ConstrainedTerm ConstrainedTerm -> Formula .
    op _=>_ : KTerm KTerm -> REWTerm .
    op _=>_ : ConstrainedTerm ConstrainedTerm -> ConstrainedREWTerm .

    ops tt ff : -> Formula .
    op  -_    : Formula -> Formula .
    op  _/\_  : Formula Formula -> Formula .
    op  _\/_  : Formula Formula -> Formula .
    op  _->_  : Formula Formula -> Formula .
    op  _<->_ : Formula Formula -> Formula .
    op  E_._  : Var Formula -> Formula .
    op  A_._  : Var Formula -> Formula .

    op _|_ : ConstrainedTerm Formula -> ConstrainedTerm .
    var CT : ConstrainedTerm . vars F1 F2 : Formula .
    -------------------------------------------------
    eq (CT | F1) | F2 = CT | (F1 /\ F2) .

    op _|_ : REWTerm Formula -> ConstrainedREWTerm .
    var CRT : ConstrainedREWTerm .
    eq (CRT | F1) | F2 = CRT | (F1 /\ F2) .

endfm

fmod DECLARATIONS is
    protecting CONSTRAINED-TERMS .
    protecting NAT .

    sorts KSort Regex .
    sorts ProductionItem Production .
    subsorts Regex String KSort < ProductionItem .
    sorts SortDeclaration SubSortDeclaration SyntaxDeclaration RuleDeclaration .
    sorts Declaration Declarations .
    subsorts SortDeclaration SubSortDeclaration SyntaxDeclaration RuleDeclaration < Declaration < Declarations .
    ------------------------------------------------------------------------------------------------------------

    op r_ : String -> Regex [ctor prec 25] .
    op #Sort : String -> KSort [ctor] .
    op [_] : String -> Production .
    op __ : ProductionItem Production -> Production [prec 40] .

    op syntax_ : KSort -> SortDeclaration [ctor prec 50] .
    op syntax_::=_ : KSort KSort -> SubSortDeclaration [ctor prec 50] .
    op syntax_::=_ : KSort Production -> SyntaxDeclaration [ctor prec 50] .
    op rule_ : ConstrainedREWTerm -> RuleDeclaration [ctor prec 50] .

    op .Declarations : -> Declarations .
    op __ : Declarations Declarations -> Declarations [assoc id: .Declarations prec 80 format(d ni d)] .

endfm

fmod KMOD is
    protecting DECLARATIONS .

    sorts KImport KImports KMod .
    subsort KImport < KImports .

    op imports_ : String -> KImport .
    op .KImports : -> KImports .
    op __ : KImports KImports -> KImports [assoc id: .KImports prec 80 format(d ni d)] .

    op kmod__endkm  : String KImports -> KMod [prec 90 format(nn d n++i n n)] .
    op kmod__endkm  : String Declarations -> KMod [prec 90 format(nn d n++i n n)] .
    op kmod___endkm : String KImports Declarations -> KMod [ctor prec 90 format(nn d n++i nni n n)] .
    ------------------------------------------------------------------------------------------------
    var NAME : String . var DECS : Declarations . var IMPS : KImports .
    eq kmod NAME DECS endkm = kmod NAME .KImports DECS endkm .
    eq kmod NAME IMPS endkm = kmod NAME IMPS .Declarations endkm .

endfm

fmod KMOD-PROJECTIONS is
    protecting KMOD .

    sorts Extractor Extractable .
    subsort Declaration KSort < Extractable .

    var NAME : String . var IL : KImports .
    var DECLS : Declarations . var DECL : Declaration .
    var KMOD : KMod . vars SSTR SSTR' : String .
    var KSORT : KSort . var PROD : Production .
    var EXT : Extractor . var EXTABLE : Extractable .

    op mtExt  : -> Extractable .
    op _;;_  : Extractable Extractable -> Extractable [assoc comm id: mtExt prec 60] .
    ----------------------------------------------------------------------------------
    eq DECL  ;; DECL  = DECL .
    eq KSORT ;; KSORT = KSORT .

    op _[_] : Extractor Declaration -> Extractable .
    op map : Extractor Declarations -> Extractable .
    ------------------------------------------------
    eq map( EXT , DECL DECLS    ) = EXT[DECL] ;; map( EXT , DECLS ) .
    eq map( EXT , .Declarations ) = mtExt .

    op overDeclarations : Extractor KMod -> Extractable .
    -----------------------------------------------------
    eq overDeclarations( EXT , kmod NAME IL DECLS endkm ) = map( EXT , DECLS ) .

    op getSort : -> Extractor .
    op getSorts : KMod -> Extractable .
    -----------------------------------
    eq getSorts( KMOD ) = overDeclarations( getSort , KMOD ) .
    eq getSort[ syntax #Sort(SSTR)           ] = #Sort(SSTR) .
    eq getSort[ syntax #Sort(SSTR) ::= KSORT ] = #Sort(SSTR) .
    eq getSort[ syntax #Sort(SSTR) ::= PROD  ] = #Sort(SSTR) .

    op getSubSort : -> Extractor .
    op getSubSorts : KMod -> Extractable .
    --------------------------------------
    eq getSubSorts( KMOD ) = overDeclarations( getSubSort , KMOD ) .
    eq getSubSort[ syntax #Sort(SSTR) ::= #Sort(SSTR') ] = syntax #Sort(SSTR) ::= #Sort(SSTR') .

    eq EXT[ DECL ] = mtExt [owise] .
endfm

fmod TESTING-MODULES is
    extending KMOD .
    op MYMOD : -> KMod .

    eq MYMOD =
    kmod "BASIC-ARITH"

        syntax #Sort("Nat")
        syntax #Sort("Nat") ::= "0" ["zero"]
        syntax #Sort("Nat") ::= "s" #Sort("Nat") ["succ"]
        syntax #Sort("Nat") ::= #Sort("Nat") "+" #Sort("Nat") ["plus"]

        syntax #Sort("Int")
        syntax #Sort("Int") ::= #Sort("Nat")
        syntax #Sort("Int") ::= "s" #Sort("Int") ["succ"]
        syntax #Sort("Int") ::= "p" #Sort("Int") ["prec"]
        syntax #Sort("Int") ::= #Sort("Int") "+" #Sort("Int") ["plus"]
        syntax #Sort("Int") ::= #Sort("Int") "-" #Sort("Int") ["plus"]

    endkm
    .
endfm

fmod TESTING is
    protecting TESTING-MODULES .
    protecting KMOD-PROJECTIONS .
endfm

reduce MYMOD .
reduce getSorts( MYMOD ) .
reduce getSubSorts( MYMOD ) .

q
```

```
fmod KMOD is
    protecting SORT-AND-SYNTAX-DECLARATIONS .

    sorts Import ImportList .
    subsort Import < ImportList .

    sorts Declaration DeclarationList .
    subsorts Declaration < DeclarationList .
    subsorts Sort SubSort Syntax < Declaration .
    sort KMod .

    op imports_ : String -> Import .
    op .ImportList : -> ImportList .
    op __ : Import ImportList -> ImportList [prec 60 format(d ni d)] .

    op .DeclarationList : -> DeclarationList .
    op __ : Declaration DeclarationList -> DeclarationList [prec 60 format(d ni d)] .
    ---------------------------------------------------------------------------------
    var SYN : Syntax . var SSORT : SubSort . var SORT : Sort .

    op kmod____endkm : String ImportList SortDeclarationList SyntaxList -> KMod .

    op kmod___endkm : String ImportList DeclarationList -> KMod
                      [ctor prec 80 format(nn d n++i nni n n)] .
    op kmod__endkm  : String DeclarationList -> KMod [prec 80] .
    op kmod__endkm  : String ImportList -> KMod [prec 80] .

    var STR : String .
    var DL : DeclarationList .
    var IL : ImportList .
    eq kmod STR DL endkm = kmod STR .ImportList DL endkm .
    eq kmod STR IL endkm = kmod STR IL .DeclarationList endkm .
endfm

reduce

kmod "MYMOD"
    imports "MYOTHERMOD"
    imports "MYOTHEROTHERMOD"

    syntax #Sort("Nat") ::= "0" [#Label("zero")]
    syntax #Sort("Nat") ::= "s" #Sort("Nat") [#Label("zero")]

    syntax #Sort("Exp") ::= #Sort("Nat")
    syntax #Sort("Exp") ::= #Sort("Exp") "+" #Sort("Exp") [#Label("zero")]
    syntax #Sort("Exp") ::= #Sort("Exp") "*" #Sort("Exp") [#Label("zero")]
    syntax #Sort("Exp") ::= #Sort("Exp") "/" #Sort("Exp") [#Label("zero")]
    syntax #Sort("Exp") ::= #Sort("Exp") "-" #Sort("Exp") [#Label("zero")]
endkm

.

q

```


Rest
====


```maude
mod KORE is
  including STRING .  --- the only external syntax

  sorts Label Token Variable Application Item K KList . --- we call these "K Label", etc.
  subsorts Token Variable Application < Item < K < KList .
  op #Label : String -> Label .
  op #Token : String Sort -> Token .
  op #Variable : String Sort -> Variable .
  op _`(_`) : Label KList -> Application . --- Maude requires ` to escape parentheses
  op .K : -> K .  --- .::K instead of .K gives a parsing error
  op _~>_ : K K -> K .
```

--- We are defining the KORE syntax for parsing here; in a KORE syntax for the
--- semantics of K we may want this operation to be associative, like below
---  op _~>_ : K K -> K [assoc id: .K] .
--- Note that we cannot define it as `_~>_ : Item K -> K` because we still want
--- to allow to match an Item in the middle of a K sequence.

--- gather attribute makes _,_ parse as right associative
--- Same comment like for ~> above; in a syntax for semantics, we probably want:
---  op _,_ : KList KList -> KList [assoc id: .KList prec 100] .

```maude
  op .KList : -> KList .
  op _,_ : KList KList -> KList [gather(e E) prec 100] .  --- prec seems to be required ...

  sort Sort .
  op #Sort : String -> Sort .

--- No support yet for external variables/constants

*** K rewriting
--- Rewrite relation => can be nested and binds as weakly as possible.
--- With => we also need brackets: K1 ~> (K2 ~> K3 => K4 ~> K5) ~> K6
  op _=>_ : K K -> K .  --- macro for "_ -> next _" with the matching logic notation (below)
---  op `(_`) : K -> K .  --- Maude uses parentheses for grouping already

*** Matching logic
--- We can delay implementing these for now if they raise issues.
  op _/\_ : K K -> K .
  op not_ : K -> K .
  op next_ : K -> K .
  op exists__ : Variable K -> K .
--- No requires/ensures anymore; these are just syntactic sugar, which we do not
--- encourage or support anymore:
--- "C[K1 => K2] requires K3 ensures K4" is "C[K1 /\ K3 => K2 /\ K4]"

*** Attributes
--- In the past, I proposed to just use KList for Attributes, but my proposal was rejected.
--- While I'd like you to reconsider, here is a syntax mimicking the current one.
  sorts AttributeKey Attribute AttributeList Attributes .
  op #AttributeKey : String -> AttributeKey .
  op _`(_`) : AttributeKey String -> Attribute .
  op .AttributeList : -> AttributeList .
  op _,_ : Attribute AttributeList -> AttributeList [format(d d s d)] .
  op [_] : AttributeList -> Attributes .

*** Outer
  sort Definition .
  op __ : RequireList ModuleList -> Definition .
```

--- Maude does not allow and empty constant, so for now we assume explicit .Sort
--- constants for optional parameters.  An alternative can be to use subsorting,
--- for example, subsort ModuleList < Definition, but that can be awkward when
--- you have multiple empty constants of different sorts next to each other.
--- When defining sequences of elements, we prefer a left-recursive grammar for
--- now.

```maude
  sorts Require RequireList .
  op require_ : String -> Require [format(n d d)] .
  op .RequireList : -> RequireList [format(n n)] .
  op __ : Require RequireList -> RequireList .

  sorts ModuleName Module ModuleList .
  op module___endmodule_ : ModuleName ImportList SentenceList Attributes -> Module [format(n d ++i d --in d n)] .
  op .ModuleList : -> ModuleList [format(n d)] .
  op __ : Module ModuleList -> ModuleList .

  op #ModuleName : String -> ModuleName .

  sorts Import ImportList .
  op import_ : ModuleName -> Import [format(ni d d)] .
  op .ImportList : -> ImportList [format(ni d)] .
  op __ : Import ImportList -> ImportList .

  sorts Sentence SentenceList .
  op .SentenceList : -> SentenceList [format(ni d)] .
  op __ : Sentence SentenceList -> SentenceList .

  op syntax__ : Sort Attributes -> Sentence .
  op syntax_::=__ : Sort Production Attributes -> Sentence [format(ni d d d n++i-- d)] .
  op syntax`priority_>__ : Label Label Attributes -> Sentence .
  op syntax`left__ : Label Attributes -> Sentence .
  op syntax`right__ : Label Attributes -> Sentence .
  op syntax`non-assoc__ : Label Attributes -> Sentence .

  sorts ProductionItem Production .
  subsorts Sort String < ProductionItem < Production .
  op r_ : String -> ProductionItem .
  op __ : ProductionItem Production -> Production .

  op rule__ : K Attributes -> Sentence [format(ni d n++i-- d)] .

endm
```

```maude
mod EXAMPLES is
  including KORE .
  ops EMPTY IMP : -> Definition .

  eq EMPTY =
.RequireList
module #ModuleName("EMPTY")
  .ImportList
  .SentenceList
endmodule [.AttributeList]
.ModuleList
  .

  eq IMP =
require "domains.k"
.RequireList


module #ModuleName("IMP-SYNTAX-COMMON")
  import #ModuleName("DOMAINS")
  .ImportList

  syntax #Sort("AExp") ::= #Sort("Int") [.AttributeList]
  syntax #Sort("AExp") ::= #Sort("Id") [.AttributeList]
  syntax #Sort("AExp") ::= #Sort("AExp") "/" #Sort("AExp")
    [#AttributeKey("left")(""), #AttributeKey("strict")(""), #AttributeKey("klabel")("_/_ : AExp * AExp ->  AExp"), .AttributeList]
  syntax #Sort("AExp") ::= #Sort("AExp") "+" #Sort("AExp")
    [#AttributeKey("left")(""), #AttributeKey("strict")(""), #AttributeKey("klabel")("_+_ : AExp * AExp ->  AExp"), .AttributeList]
  syntax #Sort("AExp") ::= "(" #Sort("AExp") ")"
    [#AttributeKey("bracket")(""), #AttributeKey("klabel")("(_) : AExp -> AExp"), .AttributeList]
  syntax priority #Label("_/_ : AExp * AExp ->  AExp") > #Label("_+_ : AExp * AExp ->  AExp")
    [.AttributeList]

  syntax #Sort("BExp") ::= #Sort("Bool") [.AttributeList]
  syntax #Sort("BExp") ::= #Sort("AExp") "<=" #Sort("AExp")
    [#AttributeKey("seqstrict")(""), #AttributeKey("latex")("{#1}\leq{#2}"), #AttributeKey("klabel")("_<=_"), .AttributeList]

--- more to come here, but let's first converge on details

  .SentenceList
endmodule [.AttributeList]


module #ModuleName("IMP-SYNTAX-PROGRAM-PARSING")
  import #ModuleName("ID-PROGRAM-PARSING")
  import #ModuleName("IMP-SYNTAX-COMMON")
  .ImportList

--- more to come here, but let's first converge on details
  .SentenceList
endmodule [.AttributeList]


module #ModuleName("IMP-SYNTAX")
  import #ModuleName("IMP-SYNTAX-COMMON")
  .ImportList

  syntax #Sort("Ids") ::= ".Ids"
    [#AttributeKey("klabel")(".Ids : -> Ids"), .AttributeList]
  syntax #Sort("Ids") ::= #Sort("Id")
    [.AttributeList]
  syntax #Sort("Ids") ::= #Sort("Ids") "," #Sort("Ids")
    [#AttributeKey("assoc")(""), #AttributeKey("unit")(".Ids : -> Ids"), .AttributeList]

--- more to come here, but let's first converge on details
  .SentenceList
endmodule [.AttributeList]


module #ModuleName("IMP-SYNTAX-TRANSLATE")
  import #ModuleName("IMP-SYNTAX-PROGRAM-PARSING")
  import #ModuleName("IMP-SYNTAX")
  .ImportList
--- more to come here, but let's first converge on details
  .SentenceList
endmodule [.AttributeList]


module #ModuleName("IMP")
  import #ModuleName("IMP-SYNTAX")
  .ImportList

--- more to come here, but let's first converge on details

--- We need to discuss the rule below before we can continue.
---  rule <k> X = I:Int; => . ...</k> <state>... X |-> (_ => I) ...</state>
  rule #Label("...")(
         #Label("<k>_</k> : K -> KCell") (
           (#Label("_=_; : Id * AExp -> Stmt")(
              #Variable("X", #Sort("Id")), #Variable("I", #Sort("Int")))
            => .K),
           #Label("...")(.KList)
         ),
         #Label("<state>_</state> : Map -> StateCell")(
           #Label("...")(.KList),
           #Label("_|->_ : Id * Int -> Map")(
             #Variable("X", #Sort("Id")),
             #Variable("_", #Sort("Int")) => #Variable("I", #Sort("Int"))
           ),
           #Label("...")(.KList)
         )
       )
    [.AttributeList]

--- more to come here, but let's first converge on details
  .SentenceList
endmodule [.AttributeList]

.ModuleList

  .

endm

---rewrite EMPTY .
rewrite IMP .

---set print mixfix off .

q
```

Questions about this definition:
- do we really need ~> as a K construct?  Can it be a label and thus the way K
  deal with evaluation contexts just a particular methodology and not an
  intrisic part of K ? Same question for =>.
- rename .::K and .::KList to . ?  if we get rid of ~> as above, then we may
  only need .::KList.
- Should we allow empty productions instead of sort declarations?  A pro
  argument is that we have fewer syntactic constructs.  A cons argument is
  that a sort declaration may be regarded as a different entityr, with
  different kinds of attributes.
- Should we add constant AttributeKeys which have special semantics, like
  "strict", as constants?
- Brackets and disappearing injections are the same thing, arent's they?  A
  production which only has one non-terminal and the production disappears
  from the AST.
- Should #Label contain more structured information than just a String?

Comments about old kast.k and e-kore.k:
- Stop having particular module names mean particular things in KORE!  You may do that in full K.
- Why do you call ATTRIBUTES a module which only defines one attribute?
- We agree on separating the attrbute listsand arguments  with commas, not spaces.
- The current attributes are a mixture of K (you use the "token" attribute) and something
  else.  I continue to believe that attributes can be just a KList.
- #emptyKProduction was never defined anywhere, but used in KProduction
