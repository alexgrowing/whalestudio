import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExteriorFormsSpanOfSetsMulSmulMono
import Development.AbelianVarietyTheory.Definitions.Divisors.IsFlatLift
open GlobalTheory GlobalTheory.DI
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exteriorFormsSpanOfSets_mul_smul_mono : ∀ {K : Type} [CommRing K] {V : Type} [AddCommGroup V] [Module K V] (A : Subring K) (L : Set V), (1 : ExteriorAlgebra K V) ∈ forms (A : Set K) L 0 ∧ (∀ q x y, x ∈ forms (A : Set K) L 1 → y ∈ forms (A : Set K) L q → x * y ∈ forms (A : Set K) L (q + 1)) ∧ (∀ q (c : K) y, c ∈ A → y ∈ forms (A : Set K) L q → c • y ∈ forms (A : Set K) L q) ∧ (∀ (B : Set K) q (c : K) y, y ∈ forms B L q → c • y ∈ forms ((fun b => c * b) '' B) L q) ∧ ∀ (B B' : Set K) (L' : Set V) q, B ⊆ B' → L ⊆ L' → forms B L q ≤ forms B' L' q := by
  first | exact @GlobalTheory.DI.forms_mul_smul_mono | exact GlobalTheory.DI.forms_mul_smul_mono | (intros; apply GlobalTheory.DI.forms_mul_smul_mono <;> assumption)
