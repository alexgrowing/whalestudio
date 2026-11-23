import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsContinuousIntegralUnitCharOfChar
import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_continuous_integralUnitChar_of_char : ∀ (l : ℕ) [Fact l.Prime] (K LL : FinExt l) (τ₀ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1) (c : ↥(GK K) →* (↥(K0 K))ˣ), Continuous (fun g : ↥(GK K) => (((c g : (↥(K0 K))ˣ) : ↥(K0 K)) : Om l)) → ∃ χ : ↥(GK K) →* (↥(OL LL))ˣ, Continuous (fun g : ↥(GK K) => (((χ g : (↥(OL LL))ˣ) : ↥(OL LL)) : ↥LL.1)) ∧ ∀ g : ↥(GK K), (((χ g : (↥(OL LL))ˣ) : ↥(OL LL)) : ↥LL.1) * τ₀ (algebraMap ↥(K0 K) ↥K.1 ((c g : (↥(K0 K))ˣ) : ↥(K0 K))) = 1 := by
  first | exact @GlobalTheory.ContCharUnitsOL.main | exact GlobalTheory.ContCharUnitsOL.main | (intros; apply GlobalTheory.ContCharUnitsOL.main <;> assumption)
