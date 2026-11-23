import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.ExistsInertiaCharpolyFactorOfTameType
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsobaricDiscreteSelfDualStrongMultiplicityOne
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.RankOneUnitary

noncomputable section

namespace GlobalTheory.NRows

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial

theorem isHeckeGaloisQ_of_wdOf_baseChange : ∀ (D : D7) (i : D.nd.Loc) (x : D.nd.X i) (P : D.naut.AV i)
    (Pa : List (Part D.naut.CG)), D.naut.ptV i P = some x → IsBCV D.nd D.naut i P Pa →
    ∀ ρ : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om →* GL (Fin D.R.nV) (Qbar (D.nd.l i)), SumRepresentations.At.ContQ D.nd i ρ → IsSSRep ρ →
    (∀ w, w ∉ placesOver D.host.E (D.nd.l i) →
      D.naut.wdOf i ρ w = D.naut.lpTw (isoLoc D.nd D.naut Pa w) ((1 - (D.R.nV : ℝ)) / 2)) →
    SumRepresentations.At.IsHeckeGaloisQ D.nd D.naut i x ρ := by
  intro D i x P Pa hP hBC ρ hc hss hwd
  refine ⟨hc, hss, fun w hw B σ hB hσ => ?_⟩
  have hS := (D.nd.S_def i w).not.1 hw.2.2.1
  have hunr : D.naut.unr (D.naut.locV i P w) := by
    refine D.naut.locV_unr i P w hw.1 hw.2.2.2 (fun k hk => hS ⟨?_, hw.2.1⟩)
      (fun hk => hS ⟨Or.inr (Or.inr hk), hw.2.1⟩)
    fin_cases k
    · exact Or.inl hk
    · exact Or.inr (Or.inl hk)
  have hloc := hBC.2.2.2.1 w hw.1
  have hw' := hwd w hw.2.1
  have hu : D.naut.unr (D.naut.wdOf i ρ w) := by
    rw [hw', hloc]
    exact (D.naut.unr_tw _ _).2 hunr
  have e := D.naut.wdOf_frob i ρ w hw.2.1 hc hu B σ hB hσ
  rw [hw', hloc, ← D.naut.pt_loc i P x hP w hw] at e
  apply Polynomial.map_injective (D.naut.iotaQC i).toRingHom (D.naut.iotaQC i).injective
  rw [e, Polynomial.map_map]
  rfl

end GlobalTheory.NRows
