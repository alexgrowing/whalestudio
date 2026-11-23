import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TotalEqOfNonneg
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NontrivialIsomClassInt
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.HermFrame GlobalTheory.CurveDens GlobalTheory.Cartier
open scoped ComplexOrder

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.VMetric

theorem isometric_det_tens_det (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k)
    (S : ShortComplex X.Modules) (r s : ℕ) (h : VMetric p S.X₂ (r + s)) (H : h.IsCInf)
    (hS : S.ShortExact) (h₁ : IsVB S.X₁ r) (h₃ : IsVB S.X₃ s) (hf : IsSubbundle S.f) :
    ((VMetric.det (H.restrict hf h₁)).tens (VMetric.det (H.quot hS h₁ h₃))).Isometric (VMetric.det H) := by
  refine HermLB.isometric_of_local (J := VBExt.AdaptedChart S r s) (fun a => a.U)
    (fun x => VBExt.exists_adaptedChart hS h₁ h₃ x)
    (fun a => a.mid hS) (fun a => (a.sub, a.quot)) (fun _ => le_rfl) (fun _ => le_inf le_rfl le_rfl)
    (fun _ => 1) (fun x a a' hx hx' => ?_) (fun σ a y hy => ?_)
  · have key : gm (𝟙 X) x _ ((VMetric.det H).B.g (a.mid hS) (a'.mid hS)) =
        gm (𝟙 X) x _ (((VMetric.det (H.restrict hf h₁)).tens (VMetric.det (H.quot hS h₁ h₃))).B.g
          (a.sub, a.quot) (a'.sub, a'.quot)) :=
      ((congrArg (gm (𝟙 X) x _) (VBExt.detUnit_sumElim hS a.he a.ht a'.he a'.ht inf_le_left inf_le_right)).trans
        (map_mul _ _ _)).trans
        (CechPic.gm_tens (VB.det S.X₁ r) (VB.det S.X₃ s) (𝟙 X) x (a.sub, a.quot) (a'.sub, a'.quot)
          ⟨hx, hx⟩ ⟨hx', hx'⟩).symm
    rw [map_one, map_one, mul_one, key, mul_inv_cancel]
  · rw [CxPts.logSq_one hy, add_zero]
    change -Real.log ((h.met σ).G (a.mid hS) y).det.re =
      -Real.log (((h.met σ).restrict hf h₁).G a.sub y).det.re +
        -Real.log (((h.met σ).quot hS h₁ h₃).G a.quot y).det.re
    have hP := (h.met σ).posDef_gram_frame hS a hy
    have e₁ : ((h.met σ).restrict hf h₁).G a.sub y = subGram ((h.met σ).gram a.frame y) := rfl
    have e₂ : ((h.met σ).G (a.mid hS) y).det = ((h.met σ).gram a.frame y).det := by
      rw [(h.met σ).gram_frame hS a hy, Matrix.det_submatrix_equiv_self]
    have e₃ : ((h.met σ).gram a.frame y).det =
        (subGram ((h.met σ).gram a.frame y)).det * (quotGram ((h.met σ).gram a.frame y)).det := by
      have hA := posDef_subGram hP
      letI : Invertible ((h.met σ).gram a.frame y).toBlocks₁₁ := hA.isUnit.invertible
      conv_lhs => rw [← Matrix.fromBlocks_toBlocks ((h.met σ).gram a.frame y)]
      rw [Matrix.det_fromBlocks₁₁, Matrix.invOf_eq_nonsing_inv]
      rfl
    rw [e₁, (h.met σ).quot_G hS h₁ h₃ a hy, e₂, e₃]
    have hA := posDef_subGram hP
    have hQ := posDef_quotGram hP
    have i₁ : (subGram ((h.met σ).gram a.frame y)).det.im = 0 := (Complex.lt_def.1 hA.det_pos).2.symm
    rw [Complex.mul_re, i₁, zero_mul, sub_zero, Real.log_mul (det_re_pos hA).ne' (det_re_pos hQ).ne']
    ring

end GlobalTheory.VMetric
