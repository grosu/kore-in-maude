******************************
*** KORE design principles ***
******************************

- attributes have no semantic meaning (they may have in frontends)
-- they only give additional info to backends
- no semantic loss when translating to KORE
-- same amount of "true concurrency", in particular

Remember the core syntax of matching logic (ML):

  Pattern ::= Variable
            | sigma(Pattern,...,Pattern)  // sigma in Sigma
            | \not Pattern
            | Pattern \and Pattern
            | \exists Variable . Pattern

Additionally, we extend the above to dynamic matching logic (DML), which
essentially means adding one more unary construct \next to the above:

  Pattern ::= \next Pattern

We are going to allow as much syntactic sugar as needed to the above.
In particular, we allow "P1 => P2" for "P1 \implies \next P2".

Syntax of matching logic is sorted in theory, but we prefer to work
with unsorted in KORE, to give us more freedom.
Sorts can be recovered using membership patterns.
We may also allow sugar "Var:Sort" for "Var \and isSort(Var) = true"

Recall that our objective is to define a DML theory, that is, a pair
(Sigma, F), where Sigma is an ML signature and F is a set of DML patterns.
Also as syntactic sugar, we allow modules and module imports.

It is important to understand the distinction between symbols and
values/elements.
The symbols, which are part of the signature Sigma, are used to build
patterns, that is, they are syntactic entities.
The values are elements in the hypothetical model, that is, semantic
entities.
Nevertheless, when debugging/proving or in general when displaying
results of various user-driven actions, we may need to see concrete
values in patterns.
For that reason, we allow each domain to display its values as strings,
following whatever encoding convention they choose to.
To distinguish values from some domains from values from other domains,
we wrap the corresponding strings with the sort they belong to.
For example, Int("123") can encode the integer value 123, and Bool("true")
can encode the Boolean value true.
The above implies, in particular, that there is a sharp distinction between
constant symbols and values.
It is easy to connect them, though, if one wants to do so for some
(finite number) of them.
For example, one may want to have symbols like 0 and true in one's signature,
and link them to their desired values with axioms like:

  axiom 0 = Int("0")
  axiom true = Bool("true")


*******************************
*** Thoughts on IMP in KORE ***
*******************************

- Not sure how to deal with the sort K:
  Is it a super syntactic category of everything, with actual injections into
  it from each other user-defined syntactic category, or consider it a special
  sort where each user-defined sort is a subosort in the order-sorted sense?
  Note 2 days later: I think we should go with the former; see last rule,
  which rewrites a Pgm into a Stmt.
  Note 4 days later: Hm, we definitely need some way to allow polymorphic
  symbols; for example, the #context can have any sort as its second argument.
  One idea could be to consider K to be a polymorphic sort.
- Should variables be sorted, i.e., X:Id, or we should use isSort membership
  patterns?  If we want to stay minimal, then the latter.  If we want
  to keep the KORE definitions human readable, then the former.  Also, note
  that almost any language used to implement backends should be able to deal
  with normal sorts / syntactic categories (as opposed to subsorts).
- Somewhat related to the above.  Should we enforce a strict sort discipline?
  I think we should.  That is, we should always enforce an operation f that
  takes arguments of sorts S1, S2, ... Sn to always take arguments of these
  sorts.  Subsorts of these should be injected.
- I believe injections should be declared strict.

