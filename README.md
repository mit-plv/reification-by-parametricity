# Reification Methods

This code package contains descriptions and implementations of all
reification methods discussed in the paper "Reification by Parametricity."

We expect the reader to be struck by the seemingly needless complexity of some
of these methods, especially when handling binders -- we feel the same way!
For readers just interested in learning one method of reification, we recommend
reading section 3 of the paper along with ExampleMoreParametricity.v.
That said, the source files for other reification methods also contain ample
comments, which we hope can be useful for learning about the Coq metaprogramming
facilities they use.

# Reification By Parametricity

MiscIntro.v contains the code used in the introduction of the paper.

ExampleSelfContainedParametricity.v is a fully self-contained example of using
reification by parametricity. ExampleMoreParametricity.v contains a series of
examples extending beyond features directly handled through parametricity.

Parametricity.v contains the implementation of reification by parametricity used
in the benchmarks.

ParametricityWithConst.v shows how constants could be reified differently from
other terms with the same type. We do not recommend or benchmark this approach.

# Other Implementations

## Dependencies

To build all of this code, you must have installed:

- OCaml
- Coq 8.7
- Ltac2 plugin (available on opam and at
  https://github.com/ppedrot/ltac2.git branch v8.7)
- UniCoq plugin (available at https://github.com/unicoq/unicoq.git
  branch v1.2-coq8.7-poly)
- Mtac2 plugin (available at https://github.com/Mtac2/Mtac2.git
  branch master)
- Template-Coq plugin (available at
  https://github.com/Template-Coq/template-coq.git branch
  coq-8.7)

The files which don't use these plugins will build fine without
them.

### Versions Used For Benchmarking

For benchmarking, we used

- OCaml 4.02.3
- Coq 8.7.1
- Ltac2 commit 7f562a9539522e56004596a751758a08cee798b1 from https://github.com/ppedrot/ltac2.git
- UniCoq commit fd5f41f32f5f7cb94de81d66a42dff18df7084a2 from https://github.com/unicoq/unicoq.git
- Mtac2 commit 607689192296bc42d75bc933ab2229a6b347c73b from https://github.com/Mtac2/Mtac2.git
- Template-Coq commit d6f621d27e882f16cf555d78b3e587038951ea94 from https://github.com/Template-Coq/template-coq.git

## Ltac

If binders are not needed, Ltac reification is one of the simplest methods of reification.
The idea is to recurse over the structure of the term, in Ltac.
These procedures are generally easy to write and suffer mainly in performance and complexity around reifying binders.
Most of the time in binder-heavy code seems to result from the overhead of switching back and forth between term checking and tactic evaluation.
Note that we use lazymatch rather than match to propagate error messages and prevent unwanted backtracking.

The Ltac-based implementations below are sorted by the mechanisms they use to recurse under binders.
Each method of recursing under binders further allows different options for how
to track the object-language variable reference for each metalanguage variable
during reification.

LtacPrimUncurry.v recurses under binders by translating a pair of binders to a
binder of a pair and using Ltac @? patterns to work under a single binder.
This method is explained in Certified Programming with Dependent Types.

### Tactics in Terms

Since Coq 8.5, the ltac:(...) syntax can be used insert tactic-generated terms
directly into Gallina code, even under binders, even when that Gallina code is
constructed using constr:(...) in tactic code just to be inspected right away.
Thus, the pattern for under binders becomes:

    let result := constr:(fun (x:T) => ltac:(recurse x)) in ...

There are a number of bugs and misfeatures to be wary of when using this method;
the attached implementations were developed by working around one unexpected
behavior after another.

LtacTacInTermPrimPair.v uses the tactics-in-terms feature to recurse under
binders and tracks variable references using pairs.

LtacTacInTermGallinaCtx.v recurses under binders with tactics in terms and
tracks variables in the Gallina context.

LtacTacInTermExplicitCtx.v recurses under binders with tactics in terms and uses
an explicit context type for references to reified variables.

### Typeclasses

Typeclasses can be used to implement tactics-in-terms-equivalent functionality
in four steps:

1. Declare a dummy class taking the same arguments as the tactic.
2. Wherever the tactic would need to recurse under binders, trigger typeclass
inference for that class by constructing a function from the bound variables to
an underscore of the class type.
3. Use Ltac to match on the inferred function and confirm that the binders are
unused in the result of the recursive call, also removing the type annotation
introduced in the previous step.
4. Add a typeclass-resolution hint to invoke our tactic to solve this class.

LtacTCPrimPair.v uses typeclass resolution to recurse under binders and tracks
references to variables using pairs.

LtacTCGallinaCtx.v uses typeclass resolution to recurse under binders and uses
the Gallina context to track references for variables being reified.

LtacTCExplicitCtx.v uses typeclass resolution to recurse under binders and uses
an explicit context type for variable references.

## Ltac2

Ltac2.v contains the Ltac2 transcription of Ltac1 reification from
LtacTacInTermExplicitCtx.v.

Ltac2LowLevel.v improves on that by using lower-level primitives not available
in Ltac1. One key insight here is that it does not need to track variable
contexts at all!  We can instead retype the same binders with type var. This
version is 50x faster than the previous.

### Typeclasses

TypeClasses.v is the most general form of typeclass-based reification.

TypeClassesBodyFlatPHOAS.v uses the body rather than the type indices of a
typeclass to store the reified term, but it does not support let ... in ... .

TypeClassesBodyHOAS.v similarly uses the body rather than the type but reifies
to @expr nat rather than forall var, @expr var.

## Mtac 2

Mtac2.v

## Canonical Structures

CanonicalStructuresFlatHOAS.v and CanonicalStructuresFlatPHOAS.v reify expression
trees only (no let ... in ...) into HOAS and PHOAS syntax trees respectively.
The HOAS files reify to @expr nat, which allows them to avoid some bookkeeping
and be a bit shorter; the PHOAS files reify to polymorphic Expr.

CanonicalStructuresHOAS.v and CanonicalStructuresPHOAS.v support let ... in ..
by rewriting it to a locked identifier before reification.

CanonicalStructures.txt contains a dump of our working knowledge based on which we
wrote these implementations in hope that reading it will make the code look
slightly less opaque.

## Custom OCaml

reify_plugin.ml4 contains the OCaml implementation for reification.
OCaml.v provides an Ltac interface to it. The implementation strategy is very
similar to that of the low-level Ltac2 implementation, but this one is yet
another 50x faster.

Pierre-Marie Pedrot, the author of Ltac2, said that essentially all of the
slowness of Ltac2 over OCaml comes from the overhead of Ltac2 being interpreted.
We look forward to the day when this straightforward compilation is built into
the Ltac2 plugin.

## template-coq

TemplateCoq.v. The template-coq plugin is a general-purpose OCaml reification
plugin. It targets an inductive datatype that mirrors Coq's underlying
representation of terms. The biggest overhead in this method of reification is
allocation, but reifying to template-coq's de Bruijn AST and then compiling from
there to PHOAS is still quite fast.

## quote tactic

The standard library's quote plugin inverts a simple denotation function to construct an OCaml reification routine; it does not handle binders.

See QuoteFlat.v.

# Benchmarking Infrastructure

PHOAS.v contains the syntax tree used in benchmarks. ReifyCommon.v contains the
general setup that was used with each individual reification method during
benchmarking. BenchmarkUtil.v generates the terms to be reified.
BaselineStats.v provides some benchmarks of simple operations for scale.

The Makefile target parsing-test-files will construct the .v
files which reify by "copy-paste".  This target requires Bash and Python 2.

The Makefile targets quick-bench, medium-bench, and slow-bench will run the
benchmarks at various sizes.

The Makefile target bench.wl will create a Wolfram Mathematica
file with the relevant benchmark results in it, and the WolframScript file
reification-by-parametricity-graphs.wls can use this file to generate the PDF
graphs in the paper.
