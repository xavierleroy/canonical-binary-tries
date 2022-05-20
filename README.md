# Canonical Binary Trees, the Coq development

This is the Coq development accompanying the paper [*Efficient Extensional Binary Trees*](https://hal.inria.fr/hal-03372247) by Andrew W. Appel and Xavier Leroy, 2021-2022.

## Implementations of binary tries (finite maps indexed by positive numbers)

* [Canonical.v](https://xavierleroy.org/canonical-binary-tries/Tries.Canonical.html): the new, extensional implementation of binary tries, using a canonical first-order representation.
* [Original.v](https://xavierleroy.org/canonical-binary-tries/Tries.Original.html): the simple, non-extensional implementation of binary tries used in CompCert 3.9 and earlier.
* [Node01.v](https://xavierleroy.org/canonical-binary-tries/Tries.Node01.html): a minor variant of the Original implementation, slightly more compact but still not extensional, used mostly for benchmarking.
* [Sigma.v](https://xavierleroy.org/canonical-binary-tries/Tries.Sigma.html): an extensional but not very efficient implementation of binary tries obtained by wrapping the Original implementation in a sigma-type.
* [GADT.v](https://xavierleroy.org/canonical-binary-tries/Tries.GADT.html): another extensional but not very efficient implementation of binary tries that uses GADTs and dependent types.
* [Patricia.v](https://xavierleroy.org/canonical-binary-tries/Tries.Patricia.html): binary Patricia trees from section 12.3 of [_Functional algorithms, verified!_](https://functional-algorithms-verified.org/) by T. Nipkow et al.  About as efficient as the Canonical implementation but not extensional.

## Implementations of dictionaries (finite maps indexed by character strings)

* [CharTrie.v](https://xavierleroy.org/canonical-binary-tries/Tries.CharTrie.html): a trie data structure with sparse, 256-degree nodes that branch on the next character of the string.

## Benchmarking

Do `make coqbench` to measure the execution speed within Coq.

Do `make ocamlbench` to measure execution speed after extraction to OCaml.

See the paper for a description and analysis of the benchmarks.
