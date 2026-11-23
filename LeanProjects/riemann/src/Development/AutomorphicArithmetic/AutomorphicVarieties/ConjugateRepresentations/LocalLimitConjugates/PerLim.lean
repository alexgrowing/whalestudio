import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.CasimirResolventProjection
import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.ZigLim
import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.CorrLim
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.FNonneg
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DifferentialTranslates.DeRhamInjOf
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DifferentialTranslates.LocSec
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DifferentialTranslates.ConeConvex
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DifferentialTranslates.LevelVal
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DifferentialTranslates.CorrFwd
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DifferentialTranslates.CorrSmooth
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DifferentialTranslates.CorrUniq
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DifferentialTranslates.CorrInv
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DifferentialTranslates.ExistsCurve
open NumberField Matrix MeasureTheory Filter Topology Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.GKCoh GlobalTheory.UnitaryBC UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible
open UpperTheory.V.Lit UpperTheory.V.Lit.Geo UpperTheory.V.Lit.Bor UpperTheory.V.Lit.Dr
open scoped TensorProduct GlobalTheory.CuspRep.CuspidalL2GL
open UpperTheory.V.Cj UpperTheory.V.Cj.H

theorem UpperTheory.V.Cj.H.perLim :
    UpperTheory.V.Cj.H.PerLim := by
  intro E _ _ _ a U Ξ q ω hω h0 hl
  have hc := (coneConvex E a).1
  have hn : (cone E a).Nonempty := ⟨_, hOne_mem_cone⟩
  have ho : IsOpen (cone E a) := isOpen_iff_mem_nhds.2 fun p hp => by
    obtain ⟨τ, -, hτ⟩ := locSec E a p hp
    exact hτ.mono fun x hx => ⟨τ x, hx⟩
  have key : ∀ k, ∃ w : (geo ho U Ξ).Om q, Corr U Ξ (ω k) w.1 ∧ (∀ γ, (geo ho U Ξ).act q γ w = w) ∧
      (geo ho U Ξ).dOm q w = 0 := fun k => by
    have hv : ∀ X, LeftInv (ω k X) ∧ RightInv U (ω k X) := fun X => (levelVal E a U Ξ _).1 ((hω k).val X)
    obtain ⟨w, hw, hw0⟩ := corrFwd E a U Ξ q (ω k) (hω k).equiv fun X => (hv X).2
    let w' : (geo ho U Ξ).Om q := ⟨w, fun s => ⟨corrSmooth E a U Ξ q _ w hw s, hw0 s⟩⟩
    have hw' : Corr U Ξ (ω k) w'.1 := hw
    have h := corrD E a ho U Ξ q _ _ hw'
    rw [h0 k] at h
    exact ⟨w', hw', fun γ => (corrInv E a ho U Ξ q _ _ hw').1 (fun X => (hv X).1) γ,
      (corrUniq E a ho U Ξ (q + 1)).2 0 _ 0 h (corr_zero U Ξ)⟩
  choose w hw hi hd0 using key
  obtain ⟨c, hz, hlim⟩ := zigLim _ _ _ _ (geo ho U Ξ) hc hn q 0 (fun k _ => w k)
    (fun k => ⟨fun γ _ _ => (hi k γ).symm, fun x hx => by simp [hd, hx, Finset.sum_range_succ]⟩)
    (fun k _ _ => hd0 k) (fun _ _ => corrLim E a ho U Ξ q ω w hw hl)
  exact ⟨c, fun k => ⟨ho, w k, hw k, hz k⟩, fun x hx => hlim x (by omega)⟩
