import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TrivIsCr
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TwistStep
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinFrameIsCrOfLinkedTowerStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsDROfLinksStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsBreuilKisinLatticeFrameOfLinkedPreframeStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsBreuilKisinBasisLimitLatticeStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

namespace GlobalTheory.BKLim

theorem limit_frame_exists : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l), bk.IsPer τ → ∀ (d N : ℕ) (ρ : ↥(GK K) →* GL (Fin d) ℤ_[l]) (tw : Tower ρ) (F : ∀ n, Frame bk N (tw.d' n) fun g => (tw.ρ' n g).val), (∀ n, (F n).IsDR) → ∃ F₀ : Frame bk N d (fun g => (ρ g).val), F₀.IsDR ∧ ((∀ n, (F n).IsCr) → F₀.IsCr) ∧ ∃ r, ∀ n, ∃ m, n ≤ m ∧ Link bk F₀.T (F m).T (tw.Pi m) n r := by
  intro l _ K bk τ hτ d N ρ tw F hDR
  obtain ⟨P, r, hP⟩ := GlobalTheory.T.exists_breuilKisin_basis_limit_lattice l K bk τ hτ d N ρ tw (fun n => (F n).toPre)
  obtain ⟨F₀, hF₀⟩ := GlobalTheory.T.exists_breuilKisinLatticeFrame_of_linked_preframe l K bk d N ρ tw F P r hP
  have hL : ∀ n, ∃ m, n ≤ m ∧ Link bk F₀.T (F m).T (tw.Pi m) n r := by
    subst hF₀
    exact hP
  exact ⟨F₀, GlobalTheory.T.isDR_of_links' l K bk d N ρ tw F F₀ r hL hDR,
    fun hCr => GlobalTheory.T.breuilKisinFrame_isCr_of_linked_tower l K bk d N ρ tw F F₀ r hL hCr, r, hL⟩

end GlobalTheory.BKLim
