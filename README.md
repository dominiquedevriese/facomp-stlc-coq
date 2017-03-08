<meta http-equiv="Content-Type" content="text/html; charset=utf-8" />

# Fully Abstract Compilation by Approximate Back-translation: Coq proof

This repository contains Coq proofs for the results reported in [1].
Essentially, it shows that a simply typed lambda calculus with general recursion
(but no recursive types) can be fully abstractly compiled to untyped lambda
calculus by wrapping compiled terms with dynamic type enforcement wrappers.

The proof uses a technique called "Approximate back-translation", which we do
not explain further here, since it is described in detail in [1].

This Coq proof was constructed by Steven Keuchel <steven.keuchel@ugent.be> and
Dominique Devriese <dominique.devriese@cs.kuleuven.be>.

## Coq version

These proofs were successfully checked using Coq v8.5pl2.

## Structure of Coq proof

Here is a list of Coq files with a short description of what they contain, in a
dependency order:

* Common/Common.v: A few simple arithmetic lemmas that we didn't immediately
find in the Coq libraries
* Common/Relations.v: Lemmas and definitions concerning the transitive and transitive-reflexive closure of relations and the transitive-reflexive closure indexed with a step count.
* Db/Spec.v: A generic specification of languages with a De Bruijn binding structure, along with a set of type classes that may be instantiated for such languages.
* Db/Inst.v: Some instances for the type classes in Db/Spec.v.
* Db/Tactics.v: A (weird?) tactic used in Db/Lemmas.v.
* Db/Lemmas.v: a set of lemmas about languages instantiating the type classes in Db/Spec.v
* Db/WellScoping.v: A set of lemmas related to well-scopedness of terms and substitutions.
* Stlc/*.v: Definitions and lemmas for the simply-typed lambda calculus that is our source language.
* Utlc/*.v: Definitions and lemmas for the untyped lambda calculus that is our target language.
* UVal/UVal.v: Definition of UVal type and some helper definitions, lemmas and tactics.
* LogRel/*.v: Definition of the logical relation, and lemmas.
* Compiler/*.v: Definition of the compiler and proof of equivalence reflection.
* BackTrans/*.v: Definition of the back-translation and lemmas.
* FullAbstraction.v: Proof of equivalence preservation and full abstraction.

## Instructions for compiling

We are using the _CoqProject machinery to build, so making your local coq check
this proof should be as easy as:

    # make
    ... (no errors means proof checks out)
    "coqc"  -q  -R "." FaComp   FullAbstraction.v
    Axioms:
    functional_extensionality_dep : ∀ (A : Type) (B : A → Type)
                                    (f g : ∀ x : A, B x),
                                    (∀ x : A, f x = g x) → f = g
    make[1]: Map '.../facomp-stlc-coq' wordt verlaten
    # 

### Checking assumptions of the proof

The file FullAbstraction.v contains the command "Print Assumptions
fullAbstraction". When Coq checks the file, it tells you that the proof relies
on only one axiom: functional extensionality:

    # touch FullAbstraction.v
    # make
    
    make -j -f Makefile.coq
    make[1]: Map '.../facomp-stlc-coq' wordt binnengegaan
    "coqdep" -c -R "." FaComp "FullAbstraction.v" > "FullAbstraction.v.d" || ( RV=$?; rm -f "FullAbstraction.v.d"; exit ${RV} )
    "coqc"  -q  -R "." FaComp   FullAbstraction.v
    Axioms:
    functional_extensionality_dep : ∀ (A : Type) (B : A → Type)
                                    (f g : ∀ x : A, B x),
                                    (∀ x : A, f x = g x) → f = g
    make[1]: Map '.../facomp-stlc-coq' wordt verlaten
    # 

## References

[1] Dominique Devriese, Marco Patrignani, and Frank Piessens. 2016. Fully-abstract compilation by approximate back-translation. In Proceedings of the 43rd Annual ACM SIGPLAN-SIGACT Symposium on Principles of Programming Languages (POPL '16). ACM, New York, NY, USA, 164-177. DOI: https://doi.org/10.1145/2837614.2837618
