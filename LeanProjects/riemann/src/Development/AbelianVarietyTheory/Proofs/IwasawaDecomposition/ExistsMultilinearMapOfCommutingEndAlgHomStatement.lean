import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsMultilinearMapOfCommutingEndAlgHom
import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousMapPFin
open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC Formalism.UG Formalism.BasicNotions GlobalTheory.DefU
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_multilinearMap_of_commuting_endAlgHom : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (Wv : ι → Type) [∀ v, AddCommGroup (Wv v)] [∀ v, Module ℂ (Wv v)] (V : Type) [AddCommGroup V] [Module ℂ V] (Φ : ∀ v, Module.End ℂ (Wv v) →ₐ[ℂ] Module.End ℂ V) (w : ∀ v, Wv v) (ℓ : ∀ v, Module.Dual ℂ (Wv v)) (y : V), (∀ u v, u ≠ v → ∀ A B, Commute (Φ u A) (Φ v B)) → (∀ v, Φ v ((ℓ v).smulRight (w v)) y = y) → ∃ F : MultilinearMap ℂ Wv V, F w = y ∧ ∀ v (A : Module.End ℂ (Wv v)) (x : ∀ u, Wv u), Φ v A (F x) = F (Function.update x v (A (x v))) := by
  first | exact @GlobalTheory.exists_multilinear_of_commuting_endAlgHom | exact GlobalTheory.exists_multilinear_of_commuting_endAlgHom | (intros; apply GlobalTheory.exists_multilinear_of_commuting_endAlgHom <;> assumption)
