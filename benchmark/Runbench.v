From Coq Require Import String.
From Tries Require Import Benchmark.

Local Open Scope string_scope.

Compute "AVLpositive (words, x100)".
Time Eval vm_compute in (repeat 100 TestAVLPositive.bench1 poswords).
Compute "AVLpositive (small numbers, x1000)".
Time Eval vm_compute in (repeat 1000 TestAVLPositive.bench1 smallnumbers).
Compute "AVLpositive (small numbers, cbv, x100)".
Time Eval cbv in (repeat 100 TestAVLPositive.bench1 smallnumbers).
Compute "AVLpositive (repeated keys, x10)".
Time Eval vm_compute in (repeat 10 TestAVLPositive.bench2 tt).

Compute "Original (words, x100)".
Time Eval vm_compute in (repeat 100 TestOriginal.bench1 poswords).
Compute "Original (small numbers, x1000)".
Time Eval vm_compute in (repeat 1000 TestOriginal.bench1 smallnumbers).
Compute "Original (small numbers, cbv, x100)".
Time Eval cbv in (repeat 100 TestOriginal.bench1 smallnumbers).
Compute "Original (small numbers, cbn)".
Time Eval cbn in (TestOriginal.bench1 smallnumbers).
Compute "Original (repeated keys, x10)".
Time Eval vm_compute in (repeat 10 TestOriginal.bench2 tt).

Compute "Canonical (words, x100)".
Time Eval vm_compute in (repeat 100 TestCanonical.bench1 poswords).
Compute "Canonical (small numbers, x1000)".
Time Eval vm_compute in (repeat 1000 TestCanonical.bench1 smallnumbers).
Compute "Canonical (small numbers, cbv, x100)".
Time Eval cbv in (repeat 100 TestCanonical.bench1 smallnumbers).
Compute "Canonical (small numbers, cbn)".
Time Eval cbn in (TestCanonical.bench1 smallnumbers).
Compute "Canonical (repeated keys, x10)".
Time Eval vm_compute in (repeat 10 TestCanonical.bench2 tt).

Compute "Sigma (words, x100)".
Time Eval vm_compute in (repeat 100 TestSigma.bench1 poswords).
Compute "Sigma (small numbers, x1000)".
Time Eval vm_compute in (repeat 1000 TestSigma.bench1 smallnumbers).
Compute "Sigma (small numbers, cbv, x100)".
Time Eval cbv in (repeat 100 TestSigma.bench1 smallnumbers).
Compute "Sigma (small numbers, cbn)".
Time Eval cbn in (TestSigma.bench1 smallnumbers).
Compute "Sigma (repeated keys, x10)".
Time Eval vm_compute in (repeat 10 TestSigma.bench2 tt).

Compute "Node01 (words, x100)".
Time Eval vm_compute in (repeat 100 TestNode01.bench1 poswords).
Compute "Node01 (small numbers, x1000)".
Time Eval vm_compute in (repeat 1000 TestNode01.bench1 smallnumbers).
Compute "Node01 (small numbers, cbv, x100)".
Time Eval cbv in (repeat 100 TestNode01.bench1 smallnumbers).
Compute "Node01 (small numbers, cbn)".
Time Eval cbn in (TestNode01.bench1 smallnumbers).
Compute "Node01 (repeated keys, x10)".
Time Eval vm_compute in (repeat 10 TestNode01.bench2 tt).

Compute "GADT (words, x100)".
Time Eval vm_compute in (repeat 100 TestGADT.bench1 poswords).
Compute "GADT (small numbers, x1000)".
Time Eval vm_compute in (repeat 1000 TestGADT.bench1 smallnumbers).
Compute "GADT (small numbers, cbv, x100)".
Time Eval cbv in (repeat 100 TestGADT.bench1 smallnumbers).
Compute "GADT (small numbers, cbn)".
Time Eval cbn in (TestGADT.bench1 smallnumbers).
Compute "GADT (repeated keys, x10)".
Time Eval vm_compute in (repeat 10 TestGADT.bench2 tt).

Compute "AVLstring (words, x100)".
Time Eval vm_compute in (repeat 100 TestAVLString.bench1 words).

Compute "CharTrie (words, x100)".
Time Eval vm_compute in (repeat 100 TestCharTrie.bench1 words).

Compute "Originalstring (words, x100)".
Time Eval vm_compute in (repeat 100 TestOriginalAsStringmap.bench1 words).

Compute "Canonicalstring (words, x100)".
Time Eval vm_compute in (repeat 100 TestCanonicalAsStringmap.bench1 words).
