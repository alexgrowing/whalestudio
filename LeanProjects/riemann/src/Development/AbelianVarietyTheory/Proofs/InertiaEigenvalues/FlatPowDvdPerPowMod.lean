import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TrivIsCr
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TwistStep
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AinfUnitBoundedTeichmullerFlatDenominators
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinPeriodIsUnitWittTiltAndNeZero
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.BKLim

theorem flatPow_dvd_perPow_mod : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l), bk.IsPer τ →
    ∀ (M n : ℕ), ∃ (c : ℕ) (y : Ainf l), (l : Ainf l) ^ n ∣ bk.ev X ^ c - τ ^ M * y := by
  intro l _ K bk τ hτ M n
  have hU : IsUnit (inclW l (τ ^ M)) := by
    rw [map_pow]
    exact (GlobalTheory.BSP.isUnit_inclW_of_isPer l K bk τ hτ).1.pow M
  obtain ⟨m, t, h⟩ := GlobalTheory.BSP.BddDen.main l K bk (τ ^ M) hU n
  refine ⟨m, t, ?_⟩
  have : bk.ev X ^ m - τ ^ M * t = -(t * τ ^ M - bk.ev X ^ m) := by ring
  rw [this]
  exact (dvd_neg).2 h

end GlobalTheory.BKLim
