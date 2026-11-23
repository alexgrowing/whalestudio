import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsPotentiallySemistableOfSemistableRestrict
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TwistStep
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon TensorProduct
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isPotentiallySemistable_of_semistable_restrict : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI) (K K' : FinExt l) (hK : K.1 ≤ K'.1) (V : Type) [AddCommGroup V] [Module ℚ_[l] V] [FiniteDimensional ℚ_[l] V] (ρ : Representation ℚ_[l] ↥(GK K) V), IsSst P (resTo ρ hK) → IsPst P ρ := by
  first | exact @GlobalTheory.PMon.isPst_of_isSst_resTo | exact GlobalTheory.PMon.isPst_of_isSst_resTo | (intros; apply GlobalTheory.PMon.isPst_of_isSst_resTo <;> assumption)
