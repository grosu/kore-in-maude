KMaude

```maude
fmod KMAUDE is
    extending META-MODULE .

    sorts KTerminal KNonTerminal KProduction .
    subsort Sort < KNonTerminal .
    subsorts KTerminal KNonTerminal < KProduction .

    sorts KAttributes KSyntax KSentence KSentences .
    subsort AttrSet < KAttributes .
    subsort KSyntax < KSentence < KSentences .

    var H : Header . var IL : ImportList .
    vars S S' : Sort . var SS : SortSet . var SDS : SubsortDeclSet .
    var ODS : OpDeclSet . var MAS : MembAxSet .
    var ES : EquationSet . var RS : RuleSet .
    var KA : KAttributes . var KP : KProduction . var KS : KSentences .

    op <Strings> : -> KTerminal .
    op __ : KProduction KProduction -> KProduction [ctor ditto] .

    op syntax_     : Sort             -> KSyntax [prec 30] .
    op syntax_::=_ : Sort KProduction -> KSyntax [prec 30] .
    op _[_] : KSyntax KAttributes -> KSentence [right id: none prec 60] .
    ---------------------------------------------------------------------

    op .KSentences : -> KSentences .
    op __ : KSentences KSentences -> KSentences [ctor assoc comm id: .KSentences prec 80 format(d ni d)] .

    op kmod_is_sorts_.______endkm : Header ImportList SortSet SubsortDeclSet
            OpDeclSet MembAxSet EquationSet RuleSet KSentences -> SModule
            [ctor gather (& & & & & & & & &)
             format (d d s n++i ni d d ni ni ni ni ni ni n--i d)] .
    ---------------------------------------------------------------

    op opQid : KProduction -> Qid .
    op args  : KProduction -> TypeList .

    eq kmod H is IL sorts SS . SDS ODS MAS ES RS .KSentences endkm
     = mod  H is IL sorts SS . SDS ODS MAS ES RS             endm  .

    eq kmod H is IL sorts SS     . SDS ODS MAS ES RS syntax S KS endkm
     = kmod H is IL sorts SS ; S . SDS ODS MAS ES RS          KS endkm .

    eq kmod H is IL sorts SS     . SDS ODS                                     MAS ES RS syntax S ::= KP [KA] KS endkm
     = kmod H is IL sorts SS ; S . SDS ODS op opQid(KP) : args(KP) -> S [KA] . MAS ES RS                      KS endkm .
endfm


reduce

kmod 'Test is nil
    sorts none . none
    none
    none
    none
    none
    syntax 'Int
    syntax 'Int ::= 'Nat [none]
    .KSentences
endkm

.


q







```
