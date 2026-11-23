import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TrivIsCr
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TwistStep
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsBreuilKisinBasisOfSemistablePeriodsStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SemistablePeriodsBreuilKisinGaloisStableStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SemistablePeriodFrameIsDeRhamStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DvdGalSubStatement

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

namespace GlobalTheory

theorem semistablePeriodFrame : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l), bk.IsPer τ → ∀ (d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) (ℤ_[l])), (∀ g, IsUnit (ρ g)) → ∀ (s : WSeed bk d ρ τ), ∃ (N : ℕ) (F : Frame bk N d ρ), F.IsDR ∧ ((∀ g, s.κ g = 1) → F.IsCr) := by
  intro l _ K bk τ hτ d ρ hρ s
  obtain ⟨N, F, Y, Z, hY, hZ, hW⟩ := GlobalTheory.T.exists_breuilKisinBasis_of_semistablePeriods l K bk τ hτ d ρ hρ s
  obtain ⟨F₀, rfl, hε⟩ := GlobalTheory.T.semistablePeriods_breuilKisin_galoisStable l K bk τ hτ d ρ hρ s N F Y Z hY hZ hW
  refine ⟨N, F₀, ?_, ?_⟩
  · exact GlobalTheory.T.semistablePeriodFrame_isDeRham l K bk τ hτ d ρ hρ s N F₀ Y Z hY hZ hW hε
  · intro hκ
    exact GlobalTheory.T.isCr_of_wSeed_alt l K bk τ hτ d ρ hρ s N F₀ Y Z hY hZ hW hε hκ

end GlobalTheory
