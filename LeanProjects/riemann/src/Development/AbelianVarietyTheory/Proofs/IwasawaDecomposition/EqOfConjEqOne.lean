import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsIsHodgeFrameIff
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnfoldedFramesParabolicRelation
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FramePointCombinationMatrix
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FrameCoefficientEqWeightRatio
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FrameCoefficientEqOmegaRatio

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField Matrix
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory GlobalTheory.CxPts GlobalTheory.Toroidal GlobalTheory.LieMet GlobalTheory.GradedNorm GlobalTheory.Cartier
  GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.ShFam GlobalTheory.ShFam.Pad
open Formalism.DegreeFormula Formalism.MJ GlobalTheory.HodgeDomain GlobalTheory.TrueCx
open ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.FramePairGram
open MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.PullbackSections

namespace GlobalTheory.HodgeOnDomain

attribute [local instance] Over.cartesianMonoidalCategory

section Main

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Z : Model Xo c β}

theorem eigGram_transport {σ : c.F →+* ℂ} (M : EigMet Z σ) {p q : CxPts (genStr Z) σ} (e : p = q)
    (F : EigFrame Z σ (p.1 ≫ genι Z)) (G : EigFrame Z σ (q.1 ≫ genι Z)) (τ : E →+* ℂ)
    (T : Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) ℂ)
    (h : ∀ i, IsCombAtG Z.t (q.1 ≫ genι Z) (G.v τ) (fun a => T a i) (F.v τ i)) :
    M.gram p F τ = Tᴴ * M.gram q G τ * T := by
  subst e
  rw [M.change p G F τ, EigFrame.co_eq h]

theorem eigGram_of_comb {σ : c.F →+* ℂ} (M : EigMet Z σ) (y y' : FrPt Xo c (CAt σ)) (h : y.x = y'.x)
    (τ : E →+* ℂ) (K : Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) ℂ)
    (hK : ∀ i, Formalism.L2.Pj.IsCombAt y'.x (y'.u τ) (fun b => (K b i : CAt σ)) (y.u τ i)) :
    M.gram (cxPt Z y) (cxFrame Z y) τ = Kᴴ * M.gram (cxPt Z y') (cxFrame Z y') τ * K := by
  refine eigGram_transport M (cxPt_congr h) _ _ τ K fun i => ?_
  have hv : IsTanAtG Xo.univ.t y'.x (y.u τ i) := h ▸ y.tan τ i
  have hx' : GlobalTheory.AllWt.ptF (S := CAt σ) y' ≫ Z.jQ ≫ genι Z = (cxPt Z y').1 ≫ genι Z := (Category.assoc _ _ _).symm
  have hx : GlobalTheory.AllWt.ptF (S := CAt σ) y ≫ Z.jQ ≫ genι Z = (cxPt Z y).1 ≫ genι Z := (Category.assoc _ _ _).symm
  have e1 : (cxFrame Z y).v τ i = (tv (lieEquiv Z y' hx' (tanOf hv))).left := ofFrPt_v_eq h hx hx' τ i hv
  rw [e1]
  exact isComb_ofFrPt (S := CAt σ) y' hx' τ (fun b => (K b i : CAt σ)) hv (hK i)

end Main

theorem eq_of_conj_eq_one {n : Type} [Fintype n] [DecidableEq n] {W P : Matrix n n ℂ} (hW : IsUnit W.det)
    (h : Wᴴ * P * W = 1) : P = (W⁻¹)ᴴ * W⁻¹ := by
  have hW' : IsUnit Wᴴ.det := by rw [det_conjTranspose]; exact hW.star
  calc P = (Wᴴ)⁻¹ * (Wᴴ * P * W) * W⁻¹ := by
        rw [Matrix.mul_assoc, mul_nonsing_inv_cancel_right _ _ hW, ← Matrix.mul_assoc, nonsing_inv_mul _ hW',
          Matrix.one_mul]
    _ = (W⁻¹)ᴴ * W⁻¹ := by rw [h, Matrix.mul_one, conjTranspose_nonsing_inv]

theorem smul_submatrix_sq {m n : Type} (a : ℂ) (M : Matrix n n ℂ) (e : m → n) :
    (a • M).submatrix e e = a • M.submatrix e e := rfl

end GlobalTheory.HodgeOnDomain

namespace GlobalTheory.HodgeOnDomain

end GlobalTheory.HodgeOnDomain
