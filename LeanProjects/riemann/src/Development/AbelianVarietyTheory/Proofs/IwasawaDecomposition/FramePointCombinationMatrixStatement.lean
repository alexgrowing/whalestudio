import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FramePointCombinationMatrix
import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GramTransformOfCoordinateChangeImports
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExpFourClauses
import Formalism.LocalToGlobal.ProjectiveLattices.OpenRowsFree
open AlgebraicGeometry CategoryTheory NumberField Matrix
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory GlobalTheory.CxPts GlobalTheory.Toroidal GlobalTheory.LieMet GlobalTheory.ShFam
open Formalism.DegreeFormula Formalism.MJ GlobalTheory.HodgeDomain GlobalTheory.TrueCx
open ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.FramePairGram

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frame_point_combination_matrix : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Z : Model Xo c β} [SmoothOfRelativeDimension Dw.dim (genStr Z)] (x : OddPrimesWithRootsOfUnity Z) {σ : c.F →+* ℂ} (y y' : FrPt Xo c (CAt σ)), y.x = y'.x → ∀ (τ : E →+* ℂ) (K : Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) ℂ), (∀ i, Formalism.L2.Pj.IsCombAt y'.x (y'.u τ) (fun b => (K b i : CAt σ)) (y.u τ i)) → x.gram (cxPt Z y) (cxFrame Z y) τ = Kᴴ * x.gram (cxPt Z y') (cxFrame Z y') τ * K := by
  first | exact @GlobalTheory.FramePairGram.gram_of_comb | exact GlobalTheory.FramePairGram.gram_of_comb | (intros; apply GlobalTheory.FramePairGram.gram_of_comb <;> assumption)
