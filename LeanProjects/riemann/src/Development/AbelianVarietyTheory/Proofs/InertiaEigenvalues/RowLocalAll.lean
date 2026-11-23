import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CenLocOfCenReal
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CoreEq
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NoFormsOff
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsRhoPtOfSplitting
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsComp
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroWild
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroSupport
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalGlobalAboveL
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsUnitarisableOfIsLocS
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SphericalAwayFromTypesStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsSplitPlaceGood
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.RowSphSmall

theorem rowLoc_overRows : PrN → ∀ hL : GlobalTheory.Published.LocalLanglandsGL, OverRows fun _ _ _ _ w Z _ _ z _ Y =>
    ∀ Rw, ParIn hL (w.st Z).toD7 (TC.cf w.I w.l Z) (repOf Y) Rw → ∀ σ, RowLoc (w.st Z).toD7 Rw σ := by
  intro hP hL
  refine EvG.imp (GlobalTheory.T.spherical_away_from_types hP) fun K _ _ _ _ hK => large₂.imp hK fun B f T _ H => ?_
  intro hKP w hpin Z Wt hX z p0 Y hH hEx hGeo hGrp hGA Rw hPar σ w' hsplit hoff
  have H' := H hKP w hpin Z Wt hX z p0 Y hH hEx hGeo hGrp hGA σ
  obtain ⟨s, rfl⟩ := GlobalTheory.OffBad.splitPlace_of_isSplitPl _ w' hsplit
  obtain ⟨τ, hloc, hsph⟩ := H' s hoff
  obtain ⟨Bf, k1, k2, k3, k4⟩ := exists_form_rowRepR hP.hc hP.decay _ _ _ _ _ _ _ z.R z.F z.cG p0 Y z.pins σ
  have hunit := isUnitarisable_of_isLocS (repOf Y σ) Bf k1 k2 k3 k4 s τ hloc
  have he := hPar.row.1 σ s τ hloc
  obtain ⟨hu, hb⟩ := locRec_unr_frobEig_le hL ((w.st Z).toD7.nd.plOm.2 s.w) τ hsph hunit
  rw [← he] at hu hb
  have hu' := (hPar.T.unr _ _).2 hu
  refine ⟨hu', fun α hα => ?_⟩
  rw [hPar.T.frobEig _ _ hu'] at hα
  have h1 := hb α hα
  have hq : (1 : ℝ) < ((Formalism.ConjugateSelfDual.normV s.w : ℕ) : ℝ) := by exact_mod_cast GlobalTheory.WeilDeligne.one_lt_normV s.w
  have hrt : (((w.st Z).toD7.R.r : ℝ) - 1) / 2 < (((w.st Z).toD7.R.t : ℝ) - 1) / 2 := by
    have := (w.st Z).toD7.R.rank_add_five_le
    have h2 : (w.st Z).toD7.R.r < (w.st Z).toD7.R.t := by unfold Ranks.r; omega
    have h3 : ((w.st Z).toD7.R.r : ℝ) < ((w.st Z).toD7.R.t : ℝ) := by exact_mod_cast h2
    linarith
  calc ‖α‖ ≤ ((Formalism.ConjugateSelfDual.normV s.w : ℕ) : ℝ) ^ ((((w.st Z).toD7.R.r : ℝ) - 1) / 2) := h1
    _ < ((Formalism.ConjugateSelfDual.normV s.w : ℕ) : ℝ) ^ ((((w.st Z).toD7.R.t : ℝ) - 1) / 2) := Real.rpow_lt_rpow_of_exponent_lt hq hrt
    _ = ((Ideal.absNorm s.w.asIdeal : ℕ) : ℝ) ^ ((((w.st Z).toD7.R.t : ℝ) - 1) / 2) := rfl

end GlobalTheory.RowSphSmall
