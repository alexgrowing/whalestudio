import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EtaleLinearHomFramedPointEigenbases
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsIsCan
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.ThetaTrace GlobalTheory.HkFam GlobalTheory.Frames GlobalTheory.HeckeEx
open GlobalTheory.IndefiniteRowSideFullHecke.FibrePushforwardExistenceTori (IsLinHom IsLieImg IsThGen IsHeckeIsog)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.etale_linear_hom_framed_point_eigenbases : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (T : Type) [CommRing T] [Algebra c.F T] (y : FrPt Xo c T) (x' : Sp T ⟶ Xo.X) (Ψ : Gx y.x ⟶ Gx x') (p : ℕ), p ≠ 0 → IsLinHom Ψ → Etale Ψ → ∃ u : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → (Sp (DualNumber T) ⟶ Xo.univ.t.G.left), (∀ τ j, IsLieImg p Ψ (y.u τ j) (u τ j)) ∧ (∀ τ j, IsEigAt c τ (u τ j)) ∧ ∀ τ w, IsTanAt x' w → IsEigAt c τ w → ∃! a : Fin (Dw.mult τ) → T, IsCombAt x' (u τ) a w := by
  first | exact @GlobalTheory.HeckePointLawRing.exists_frame_image | exact GlobalTheory.HeckePointLawRing.exists_frame_image | (intros; apply GlobalTheory.HeckePointLawRing.exists_frame_image <;> assumption)
