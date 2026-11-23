import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RiemannFormFramePoint
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsIsHodgeFrameIff
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UniformizedFamilyChartIndex
open AlgebraicGeometry CategoryTheory Limits NumberField Matrix
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory GlobalTheory.CxPts GlobalTheory.Toroidal GlobalTheory.LieMet GlobalTheory.GradedNorm GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.ShFam GlobalTheory.ShFam.Pad
open GlobalTheory.ArcQ
open scoped ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.riemann_form_frame_point : ∀ (D : D7) (A : Amb D) (N j : ℕ) (S : Sig A N j) (κ : Lv A) (s : FinalTheorems S κ) (x : ToroidalCompactificationData s) (σ : κ.c.F →+* ℂ), Formalism.L2.PjFree.GoodEmb κ.c σ → ∀ (W : UnfWit (s.U σ)) (i : Fin W.F.n) (P : (W.F.Di i).La →+ (Fin W.g → ℂ)), IsPeriod (W.F.Di i) (fun j => Formalism.L2.PjFree.relab κ.c σ (W.e j).1) P → ∀ (Hm : Matrix (Fin W.g) (Fin W.g) ℂ), IsRiem W.F i P Hm → ∀ (q : FrPt (S.Xo κ.l) κ.c (CAt σ)) (z : ∀ τ : D.host.E →+* ℂ, Fin (S.Dw.mult τ) → (Fin W.g → ℂ)), AnLie W.F i P q z → ∀ (y : CxPts (genStr s.T.Z) σ), cxPt s.T.Z q = y → ∀ f : EigFrame s.T.Z σ (y.1 ≫ genι s.T.Z), (∀ τ k, ∃ w : Sp (DualNumber ℂ) ⟶ s.T.Z.oF.t.G.left, w ≫ s.T.Z.m0.toSABMap.φ = q.u τ k ∧ w ≫ s.T.Z.m.φ = f.v τ k) → ∀ τ a b, (x.hodge σ).gram y f τ a b = (Real.pi : ℂ) * hermForm Hm (z τ b) (z τ a) := by
  first | exact @GlobalTheory.ShFam.ToroidalCompactificationData.hodge_gram_of_sameVec | exact GlobalTheory.ShFam.ToroidalCompactificationData.hodge_gram_of_sameVec | (intros; apply GlobalTheory.ShFam.ToroidalCompactificationData.hodge_gram_of_sameVec <;> assumption)
