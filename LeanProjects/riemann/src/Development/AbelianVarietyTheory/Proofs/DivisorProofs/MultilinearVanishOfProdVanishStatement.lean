import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MultilinearVanishOfProdVanish
import Mathlib
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sum_smul_multilinear_eq_zero_of_prod_vanish : ∀ {K : Type} [Field K] {ι : Type} [Fintype ι] [DecidableEq ι] {X : ι → Type} (A : ∀ i, Submodule K (X i → K)) {M : Type} [AddCommGroup M] [Module K M] (P : MultilinearMap K (fun i => A i) M) {D : Type} (s : Finset D) (c : D → K) (f : D → ∀ i, A i), (∀ x : ∀ i, X i, ∑ d ∈ s, c d * ∏ i, (f d i : X i → K) (x i) = 0) → ∑ d ∈ s, c d • P (f d) = 0 := by
  first | exact @GlobalTheory.multilinear_vanish_of_prod_vanish | exact GlobalTheory.multilinear_vanish_of_prod_vanish | (intros; apply GlobalTheory.multilinear_vanish_of_prod_vanish <;> assumption)
