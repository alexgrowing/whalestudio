import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CharAbove
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.InjPrimeTo
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.GaloisSideTwistedSelmerAuxiliaryPrimes
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CGTrue
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.GaloisRepOfPolarizedCuspidal
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsSpanFormsNeBot
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EventuallyNatCastNotMem
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeilDeligneParamMonodromyEqZeroIff

noncomputable section

namespace GlobalTheory.GalAway

open GlobalTheory.TripleGal Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial Neutral.B1 Formalism.L2.Host GlobalTheory.HeckeGal GlobalTheory.Pst
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.HeightCounting

theorem galoisReps_of_cgTrue : ∀ hL : GlobalTheory.Published.LocalLanglandsGL, GlobalTheory.Published.AutomorphicFormsFiniteGL → GlobalTheory.Published.GaloisRepOfPolarizedCuspidal → ∀ (D : D7) (T : GlobalTheory.RowTie.WDTie D.nd D.naut), GlobalTheory.HeightCounting.CGTrue hL D T → GlobalTheory.IndefiniteRowSideFullHecke.RayClassPrimeCounting.GaloisReps D := by
  intro hL hF hG D T C π hc hr l _ ι
  have := host_isCMField D.host
  have ha : 1 ≤ D.R.r := by
    have := D.R.two_le_m; have := D.R.m_add_three_le_k; unfold Ranks.r; omega
  have hr' : (C.e _ π).1.IsRegAlg := (GlobalTheory.CuspRep.CG.isRegAlg_iff _).2 fun τ => by
    have := (D.naut.ralg_def π).1 hr τ
    rwa [C.inf] at this
  obtain ⟨r, h1, h2, h3⟩ := exists_wdOf_eq_locPar hL hF hG D.nd.Om ι ha (C.e _ π).1 ((C.csd _ π).1 hc) hr'
  refine ⟨r, h1, h2, fun w hw => ?_⟩
  have hl : ((l : ℕ) : 𝓞 D.host.E) ∉ w.asIdeal := hw
  have e : T.e w (D.naut.lpTw (D.naut.locG π w) ((1 - (D.R.r : ℝ)) / 2)) = wdOf (D.nd.plOm.2 w) hl ι r := by
    rw [T.tw, C.loc, h3]
    rfl
  refine ⟨fun s hs => ?_, ?_, fun hu B s hB hs => ?_⟩
  · rw [T.inePol w _ s hs, e]
    exact inePol_wdOf hl ι h1 hs
  · rw [T.mono0, e]
    exact weilDeligneParam_monodromy_eq_zero_iff hl ι h1
  · have hu' := (D.naut.unr_tw _ ((1 - (D.R.r : ℝ)) / 2)).2 hu
    rw [galPol, T.frobEig w _ hu', e]
    exact frobEig_wdOf hl ι h1 (e ▸ (T.unr w _).1 hu') hB hs

end GlobalTheory.GalAway

end
