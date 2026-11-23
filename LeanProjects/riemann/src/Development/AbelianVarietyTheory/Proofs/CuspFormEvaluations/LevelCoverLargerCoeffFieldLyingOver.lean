import Mathlib
import Development.AbelianVarietyTheory.Definitions.ThetaValues.LeCovCoeff
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.RuleBaseChangeSectionValuesSemilinearStatement

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.FieldBC

namespace GlobalTheory.FieldBC

theorem frOver_isLev_ddBC : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c c' : Coeff l) (hle : c.F ≤ c'.F) (n : ℕ) (d : DeltaDat Xo c n), (∀ (k : Type) [CommRing k] [Algebra c.F k] [Algebra c'.F k] [Algebra d.c₂.F k] [A₂ : Algebra (covCoeff hle d).F k] (h : AlgOver c c' hle k) (h₂ : AlgOver d.c₂ (covCoeff hle d) (le_covCoeff hle d) k) (y₂ : FrPt d.Xo₂ (covCoeff hle d) k) (y : FrPt Xo c' k), @FrOver E _ _ _ H Dw l Xo c' n (ddBC hle d) k _ _ A₂ y₂ y ↔ FrOver d (y₂.res (le_covCoeff hle d) h₂) (y.res hle h)) ∧ (d.IsLev → (ddBC hle d).IsLev) := by
  intro E _ _ _ H Dw l Xo c c' hle n d
  refine ⟨fun k _ _ _ _ _ _ _ _ _ => Iff.rfl, ?_⟩
  rintro ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  have hB := (GlobalTheory.T.ruleBaseChange_section_values_semilinear E H Dw d.l₂ d.Xo₂ d.c₂ (covCoeff hle d) (le_covCoeff hle d)).1 0 0 d.cδ h8
  refine ⟨h1, h2, h3, h4, h5, h6, ?_, hB.1, ?_⟩
  · intro k _ _ A A₂ hA y
    letI A₂' : Algebra (covCoeff hle d).F k := A₂
    letI B : Algebra c.F k := @resAlg E _ _ _ H l c c' hle k _ A
    letI B₂ : Algebra d.c₂.F k := @resAlg E _ _ _ H d.l₂ d.c₂ (covCoeff hle d) (le_covCoeff hle d) k _ A₂'
    have h : @AlgOver E _ _ _ H l c c' hle k _ B A := fun _ => rfl
    have h₂ : @AlgOver E _ _ _ H d.l₂ d.c₂ (covCoeff hle d) (le_covCoeff hle d) k _ B₂ A₂' := fun _ => rfl
    obtain ⟨z, hz⟩ := @h7 k _ _ B B₂ (fun a => hA (incF c c' hle a)) (@FrPt.res E _ _ _ H Dw l c c' hle Xo k _ B A h y)
    exact ⟨@FrPt.ext E _ _ _ H Dw d.l₂ d.c₂ (covCoeff hle d) (le_covCoeff hle d) d.Xo₂ k _ B₂ A₂' h₂ z, hz⟩
  · intro k _ _ A₂ y₂
    letI A₂' : Algebra (covCoeff hle d).F k := A₂
    letI B₂ : Algebra d.c₂.F k := @resAlg E _ _ _ H d.l₂ d.c₂ (covCoeff hle d) (le_covCoeff hle d) k _ A₂'
    have h₂ : @AlgOver E _ _ _ H d.l₂ d.c₂ (covCoeff hle d) (le_covCoeff hle d) k _ B₂ A₂' := fun _ => rfl
    intro h0
    exact @h9 k _ _ B₂ _ ((@hB.2 k _ B₂ A₂' h₂ y₂).symm.trans h0)

end GlobalTheory.FieldBC
