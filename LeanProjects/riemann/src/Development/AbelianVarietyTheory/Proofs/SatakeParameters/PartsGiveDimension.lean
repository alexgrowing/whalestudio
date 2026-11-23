import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.GoodIdempotentFixesOfOnlySeriesOfLabelActs
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsSemisimpleGaloisRepWeightsStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.HeckeGaloisOfUnramifiedMatchStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.HeckeGaloisRepQbarConjugateUniqueStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsHeckeGaloisQOfIsHeckeGaloisStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.UnramifiedMatchOfHeckeGaloisStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.HeckeGaloisLocalWeightsStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.HeckeGaloisLocalWeightsDeRhamStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.TwistedMuPartInBaseChangeStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.RowParamOfThetaLiftBaseChangeStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial

namespace GlobalTheory.NRows.Parts

theorem lgc : ∀ D : D7, SumRepresentations.tie0 D → SumRepresentations.adm2 D → SumRepresentations.adm5 D → ∀ (i : D.nd.Loc) (x : D.nd.X i) (P : D.naut.AV i) (Pa : List (Part D.naut.CG)), D.naut.ptV i P = some x → IsBCV D.nd D.naut i P Pa → ∀ ρ : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om →* GL (Fin D.R.nV) (Qbar (D.nd.l i)), SumRepresentations.At.IsHeckeGaloisQ D.nd D.naut i x ρ → (∀ w, w ∉ placesOver D.host.E (D.nd.l i) → D.naut.wdOf i ρ w = D.naut.lpTw (isoLoc D.nd D.naut Pa w) ((1 - (D.R.nV : ℝ)) / 2)) ∧ ∀ w ∈ placesOver D.host.E (D.nd.l i), D.naut.IsdRW i ρ w ∧ D.naut.wdOf i ρ w = D.naut.lpTw (isoLoc D.nd D.naut Pa w) ((1 - (D.R.nV : ℝ)) / 2) ∧ ∀ τ, InducesW D.nd i τ w → D.naut.jumpsW i ρ τ = D.naut.locAutHodgeTateWeightsLevelZero i τ := by
  intro D t0 a2 a5 i x P Pa hP hPa ρ hρ
  obtain ⟨ρ0, hc, hs, hw, hl⟩ := GlobalTheory.T.exists_semisimple_galois_rep_weights D t0 a2 i P Pa hPa
  obtain ⟨Pm, hPm⟩ := GlobalTheory.T.heckeGaloisRepQbar_conjugate_unique D a5 i x ρ0 ρ (GlobalTheory.T.hecke_galois_of_unramified_match D i x P Pa hP hPa ρ0 hc hs hw) hρ
  obtain ⟨c1, c2, c3⟩ := (t0.2.2.2.2.2 i).2.1 _ ρ0 ρ hc Pm hPm
  refine ⟨fun w h => (c2 w (Or.inl h)).trans (hw w h), fun w h => ⟨(c1 w h).2 (hl w h).1, (c2 w (Or.inr (hl w h).1)).trans (hl w h).2.1, fun τ hτ => ?_⟩⟩
  rw [c3 τ, (hl w h).2.2 τ hτ]
  intro w' hw'
  obtain rfl : w' = w := HeightOneSpectrum.ext (Ideal.ext fun y => (hw' y).symm.trans (hτ y))
  exact (hl _ h).1

theorem h41 (D : D7) (a : SumRepresentations.AdmAt D) : SumRepresentations.ReducedFamilyProposition D := by
  obtain ⟨⟨t0, hO, a1, a2, a3, a4, a5⟩, a7⟩ := a
  have ex : ∀ (i : D.nd.Loc) (x : D.nd.X i), ∃ ρ, SumRepresentations.At.IsHeckeGaloisQ D.nd D.naut i x ρ := fun i x => by
    obtain ⟨P, hP⟩ := D.naut.pt_surj i x
    obtain ⟨Pa, hPa⟩ := a1 i P
    obtain ⟨ρ, hc, hs, hw, -⟩ := GlobalTheory.T.exists_semisimple_galois_rep_weights D t0 a2 i P Pa hPa
    exact ⟨ρ, GlobalTheory.T.hecke_galois_of_unramified_match D i x P Pa hP hPa ρ hc hs hw⟩
  have lg := lgc D t0 a2 a5
  intro i
  refine ⟨⟨fun x => (ex i x).choose, fun x => (ex i x).choose_spec⟩, GlobalTheory.T.unramified_match_of_hecke_galois D a1 a5 ex lg i, fun r hr => ?_⟩
  have he := fun x => GlobalTheory.T.isHeckeGaloisQ_of_isHeckeGalois' D i x (r x) (hr x)
  exact ⟨(GlobalTheory.T.hecke_galois_local_weights D t0 a1 lg i r he).1, GlobalTheory.T.hecke_galois_local_weights_de_rham D t0 a1 lg i r he, (GlobalTheory.T.hecke_galois_local_weights D t0 a1 lg i r he).2⟩

theorem h42 (D : D7) (a : SumRepresentations.AdmAt D) (s : GlobalTheory.RowCopy.RowSize D) (hk : GlobalTheory.RowCopy.HeckeSplitOne D)
    (l : ∀ i : D.nd.Loc, GlobalTheory.RowCopy.LamPos D (D.nd.mu i) (D.nd.j i)) (th : GlobalTheory.RowCopy.ThetaOne D) : SumRepresentations.ReducedParameterProposition D := by
  obtain ⟨⟨t0, hO, a1, a2, a3, a4, a5⟩, a7⟩ := a
  intro i σ hσ
  obtain ⟨P, hP⟩ := th i σ hσ
  obtain ⟨Pa, hPa⟩ := a1 i P
  obtain ⟨Sig, h1, h2⟩ := GlobalTheory.T.row_param_of_thetaLift_baseChange D t0 a3 a4 a5 i σ P Pa hP hPa (GlobalTheory.T.twisted_mu_part_in_base_change D t0 a3 a5 a7 s hk i σ P Pa hσ hP hPa)
  refine ⟨⟨⟨_, (l i σ).2 hσ, (l i σ).1⟩, P, hP⟩, Sig, h1, fun P' hP' => ?_⟩
  obtain rfl : P = P' := by
    by_contra hne
    exact hP.1 (le_bot_iff.1 ((le_inf hP.2 hP'.2).trans ((D.naut.typeV_indep i).pairwiseDisjoint hne).le_bot))
  exact h2

theorem main : ∀ D : D7, GlobalTheory.NRows.PartsGive D := fun D => GlobalTheory.NRows.partsGive_of (h41 D) (h42 D)
end GlobalTheory.NRows.Parts
