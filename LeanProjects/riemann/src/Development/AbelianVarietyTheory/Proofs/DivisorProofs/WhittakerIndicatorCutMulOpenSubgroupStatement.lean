import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WhittakerIndicatorCutMulOpenSubgroup
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemSupportComp
open Matrix Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.whittakerIndicatorCut_mul_open_subgroup : ∀ {F : Type} [NormedField F] (ψ : AddChar F ℂ) {n : ℕ} (U : Subgroup (GL (Fin n) F)), IsOpen (U : Set (GL (Fin n) F)) → ∀ X A : Set (GL (Fin n) F), (∀ x ∈ X, ∀ u ∈ U, x * u ∈ X) → GlobalTheory.JSW.Cut.Cuts ψ (U : Set (GL (Fin n) F)) X A → ∃ U₁ : Subgroup (GL (Fin n) F), U₁ ≤ U ∧ IsOpen (U₁ : Set (GL (Fin n) F)) ∧ GlobalTheory.JSW.Cut.Cuts ψ (U : Set (GL (Fin n) F)) X {g | ∃ a ∈ A, ∃ u ∈ U₁, g = a * u} := by
  first | exact @GlobalTheory.JSW.Cut.cuts_mul_open_subgroup | exact GlobalTheory.JSW.Cut.cuts_mul_open_subgroup | (intros; apply GlobalTheory.JSW.Cut.cuts_mul_open_subgroup <;> assumption)
