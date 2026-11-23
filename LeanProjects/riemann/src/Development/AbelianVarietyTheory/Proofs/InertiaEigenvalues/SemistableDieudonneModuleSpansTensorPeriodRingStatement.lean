import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SemistableDieudonneModuleSpansTensorPeriodRing
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TwistStep
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N GlobalTheory.Pst GlobalTheory.PMon TensorProduct Module
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.semistableDieudonneModule_spans_tensor_periodRing : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI) (K : FinExt l) (V : Type) [AddCommGroup V] [Module ℚ_[l] V] [FiniteDimensional ℚ_[l] V] (ρ : Representation ℚ_[l] ↥(GK K) V), IsSst P ρ → ∀ v : V, ∃ (k : ℕ) (a : Fin k → Bst P) (x : Fin k → V ⊗[ℚ_[l]] Bst P), (∀ i, x i ∈ Dst P ρ) ∧ v ⊗ₜ[ℚ_[l]] (1 : Bst P) = ∑ i, onB P ℚ_[l] V (LinearMap.mulLeft ℚ_[l] (a i)) (x i) := by
  first | exact @GlobalTheory.Pst.Dst_spans_tensor_Bst | exact GlobalTheory.Pst.Dst_spans_tensor_Bst | (intros; apply GlobalTheory.Pst.Dst_spans_tensor_Bst <;> assumption)
