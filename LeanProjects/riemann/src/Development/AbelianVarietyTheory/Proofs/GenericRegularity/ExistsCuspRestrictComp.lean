import Mathlib
import Development.AbelianVarietyTheory.Definitions.RegularCharts.Reframe
import Development.AbelianVarietyTheory.Definitions.RegularCharts.ModelAt
import Development.AbelianVarietyTheory.Definitions.RegularCharts.SCharts
import Formalism.LocalToGlobal.ProjectiveLattices.FrameCharts
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsIdempotentWeightZeroSectionOfComponentStatement
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.IdemMulMemCusp

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg

namespace GlobalTheory.Reg

private theorem evC_mul' {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}
    {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} (h : GenFrEx Xo c) (Z : Comp Xo c)
    (f g : Rul Xo c) : evC h Z (f * g) = evC h Z f * evC h Z g := by
  show evR Xo c (f * g) (genFr h Z) = evR Xo c f (genFr h Z) * evR Xo c g (genFr h Z)
  unfold evR evalAt
  split
  · exact map_mul _ _ _
  · simp

theorem exists_cusp_restrict_comp : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), EvLaws Xo c → ∀ h : GenFrEx Xo c, Atlas h → ∀ (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Formalism.L2.PjFree.Unf Xo c σ r), (∀ σ, Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf (U σ)) → ∀ (Z : Comp Xo c) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), ∀ g ∈ Formalism.L2.PjFree.cusp Xo c U a n, ∃ g' ∈ Formalism.L2.PjFree.cusp Xo c U a n, evC h Z g' = evC h Z g ∧ ∀ Z', Z' ≠ Z → evC h Z' g' = 0 := by
  intro E _ _ _ H Dw l Xo c hL h hA r U hU Z a n g hg
  obtain ⟨χ, hχ, hidem, h1, h0⟩ := GlobalTheory.T.exists_idempotent_weightZero_section_of_component E H Dw l Xo c hL h hA Z
  refine ⟨χ * g, GlobalTheory.Reg.IdemCusp.idem_mul_mem_cusp E H Dw l Xo c r U hU χ hχ hidem a n g hg, ?_, ?_⟩
  · rw [evC_mul' h Z, h1, _root_.one_mul]
  · intro Z' hZ'
    rw [evC_mul' h Z', h0 Z' hZ']
    simp

end GlobalTheory.Reg
