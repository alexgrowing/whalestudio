import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LinearIndepOnOfInvariant
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RatioInvariantInK0
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fontaine_inequality_dcris_finite_concrete_rings : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ K LL : FinExt l, FontaineLe (P.PD K) ↥LL.1 ∧ ∀ (V : Type) [AddCommGroup V] [Module ↥LL.1 V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] ↥LL.1 V] [FiniteDimensional ↥LL.1 V] (ρ : Representation ↥LL.1 ↥(GK K) V), FiniteDimensional ↥LL.1 ↥(Dcris (P.PD K) ρ) := by
  intro l _ P AI T K LL
  have key : ∀ (V : Type) [AddCommGroup V] [Module ↥LL.1 V] [Module ℚ_[l] V]
      [IsScalarTower ℚ_[l] ↥LL.1 V] [FiniteDimensional ↥LL.1 V] (ρ : Representation ↥LL.1 ↥(GK K) V),
      Module.Finite ↥LL.1 (Dcris (P.PD K) ρ) ∧
        Module.finrank ↥LL.1 (Dcris (P.PD K) ρ) ≤ Module.finrank ℚ_[l] ↥(K0 K) * Module.finrank ↥LL.1 V := by
    intro V _ _ _ _ _ ρ
    have := GlobalTheory.Per.FontaineBound.isDomain_cris (P.PD K) (GlobalTheory.Per.FontaineBound.isField_of_tied T)
    have := (P.PD K).finK₀
    have := LL.2
    refine GlobalTheory.Per.FontaineBound.finite_finrank_le (P.PD K).actB (fun b b' hb h => GlobalTheory.Per.FracInv.tied_frac_invariant l P AI T K b' b hb fun g hg => ?_) ρ
    have h1 := h ⟨g, hg⟩
    rw [P.PD_actB, P.PD_actB] at h1
    rw [mul_comm, h1, mul_comm]
  exact ⟨fun V _ _ _ _ _ ρ => (key V ρ).2, fun V _ _ _ _ _ ρ => (key V ρ).1⟩
