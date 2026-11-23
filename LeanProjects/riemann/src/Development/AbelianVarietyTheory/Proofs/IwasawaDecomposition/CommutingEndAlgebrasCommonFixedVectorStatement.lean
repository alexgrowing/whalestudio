import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CommutingEndAlgebrasCommonFixedVector
import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousMapPFin
open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC Formalism.UG Formalism.BasicNotions GlobalTheory.DefU
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_ne_zero_fixed_by_commuting_rankOne_images : ∀ (ι : Type) [Fintype ι] (Wv : ι → Type) [∀ v, AddCommGroup (Wv v)] [∀ v, Module ℂ (Wv v)] [∀ v, FiniteDimensional ℂ (Wv v)] (V : Type) [AddCommGroup V] [Module ℂ V] (Φ : ∀ v, Module.End ℂ (Wv v) →ₐ[ℂ] Module.End ℂ V) (w : ∀ v, Wv v) (ℓ : ∀ v, Module.Dual ℂ (Wv v)), Nontrivial V → (∀ v, ℓ v (w v) = 1) → (∀ u v, u ≠ v → ∀ A B, Commute (Φ u A) (Φ v B)) → ∃ y : V, y ≠ 0 ∧ ∀ v, Φ v ((ℓ v).smulRight (w v)) y = y := by
  first | exact @GlobalTheory.commuting_endAlgebras_common_fixed_vector | exact GlobalTheory.commuting_endAlgebras_common_fixed_vector | (intros; apply GlobalTheory.commuting_endAlgebras_common_fixed_vector <;> assumption)
