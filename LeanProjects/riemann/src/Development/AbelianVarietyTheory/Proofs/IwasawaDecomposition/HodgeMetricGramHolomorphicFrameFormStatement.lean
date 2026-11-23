import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HodgeMetricGramHolomorphicFrameForm
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MultOfNotMem
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame
open GlobalTheory.PointChern Filter Topology
open scoped Matrix

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hodgeMetric_gram_holomorphic_frame_form : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (σ : c.F →+* ℂ) (U : Formalism.L2.PjFree.Unf Xo c σ (Dw.p + Dw.q)), Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → ∀ k' : U.Comp, ∃ (G : ReciprocityTheory.ChartRestriction.G.FD.Frame (U.X k').Ψ (Dw.p + Dw.q) → Mat Dw.mult ℂ) (z : ReciprocityTheory.ChartRestriction.G.FD.Frame (U.X k').Ψ (Dw.p + Dw.q) → GlobalTheory.AllWt.Psi H → Matrix (Fin Dw.p) (Fin Dw.q) ℂ) (cc : (E →+* ℂ) → ℝ), (∀ τ, 0 < cc τ) ∧ ∀ (x : ReciprocityTheory.ChartRestriction.G.FD.Frame (U.X k').Ψ (Dw.p + Dw.q)) (hx : x ∈ (U.X k').dom), (∀ τ a b, AnalyticAt ℂ (fun x' => G x' τ a b) x) ∧ (∀ τ a b, AnalyticAt ℂ (fun x' => z x' τ a b) x) ∧ (∀ τ, IsUnit (G x τ).det) ∧ InDom (z x) ∧ ∀ τ, ((hodgeMet Z U).gram (cxPt Z (U.un k' ⟨x, hx⟩)) (cxFrame Z (U.un k' ⟨x, hx⟩)) τ)ᵀ = (cc τ : ℂ) • (G x τ * modelGram H Dw (z x) τ * (G x τ)ᴴ) := by
  first | exact @GlobalTheory.HodgeGramGen.hodge_gram_frame | exact GlobalTheory.HodgeGramGen.hodge_gram_frame | (intros; apply GlobalTheory.HodgeGramGen.hodge_gram_frame <;> assumption)
