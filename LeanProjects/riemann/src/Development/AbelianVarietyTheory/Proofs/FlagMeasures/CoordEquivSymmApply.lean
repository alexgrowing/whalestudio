import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Direct
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.PoincareInHH
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NOfibRat
open scoped Classical ENNReal
open Matrix MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.LocWSOf Formalism.L2.SG.PoincareInHH.PoincareSetting GlobalTheory.CovDom
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CovDomGrp

variable {D : D7} (X : HidaSetting D)

theorem vecOf_apply (c : Fin (2 * D.R.rS + D.R.k + 1) → D.host.E) :
    vecOf X c = ∑ i, c i • X.bas (ci X i) := by
  simp only [vecOf, LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
    LinearEquiv.funCongrLeft_apply, Module.Basis.equivFun_symm_apply]
  rw [← (ci X).sum_comp]
  simp

theorem crdH_vecOf (c : Fin (2 * D.R.rS + D.R.k + 1) → D.host.E) : crdH X (vecOf X c) = c := by
  funext i
  simp only [crdH, vecOf, LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
    ← Module.Basis.equivFun_apply, LinearEquiv.apply_symm_apply, LinearEquiv.funCongrLeft_apply]
  simp

theorem vecOf_crdH (y : (VS D).V) : vecOf X (crdH X y) = y := by
  simp only [vecOf, LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply]
  conv_rhs => rw [← X.bas.equivFun.symm_apply_apply y]
  congr 1

variable {X} in
theorem n_vecOf {n : (VS D).V ≃ₗ[D.host.E] (VS D).V}
    {γ : Matrix (Fin (2 * D.R.rS + D.R.k + 1)) (Fin (2 * D.R.rS + D.R.k + 1)) D.host.E}
    (hγ : ∀ y, crdH X (n y) = γ *ᵥ crdH X y) (c : Fin (2 * D.R.rS + D.R.k + 1) → D.host.E) :
    n (vecOf X c) = vecOf X (γ *ᵥ c) := by
  conv_lhs => rw [← vecOf_crdH X (n (vecOf X c)), hγ, crdH_vecOf]

theorem crdH_eq_crd (y : (VS D).V) (i : Fin (2 * D.R.rS + D.R.k + 1)) :
    crdH X y i = X.ιE (X.crd y (ci X i)) := by
  simp [crdH, HidaSetting.crd, crdOf]

theorem sig_apply (a : D.host.E) : (D.sp.cm.sig : D.host.E →+* D.host.E) a = star a := rfl

theorem hT_vecOf (a b : Fin (2 * D.R.rS + D.R.k + 1) → D.host.E) :
    (VS D).hT (vecOf X a) (vecOf X b) = GlobalTheory.SgAlg.form (D.sp.cm.sig : D.host.E →+* D.host.E) (Jc X) b a := by
  rw [vecOf_apply, vecOf_apply]
  simp only [map_sum, map_smulₛₗ, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul,
    GlobalTheory.SgAlg.form, dotProduct, Matrix.mulVec, sig_apply, Jc, Finset.mul_sum, RingHom.id_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [starRingEnd_apply]
  ring

theorem Jc_det_ne_zero : (Jc X).det ≠ 0 := by
  have h : Jc X = (X.B.I.J.map X.ιE).submatrix (ci X) (ci X) := by
    ext i j
    simp [Jc, X.J_eq]
  rw [h, Matrix.det_submatrix_equiv_self]
  intro h0
  apply X.B.I.J_det
  apply X.ιE.injective
  rw [map_zero]
  exact (RingHom.map_det X.ιE.toRingHom X.B.I.J).trans h0

def coordEquiv : (Fin (2 * D.R.rS + D.R.k + 1) → D.host.E) ≃ₗ[D.host.E] (VS D).V :=
  (LinearEquiv.funCongrLeft D.host.E D.host.E (ci X).symm).trans X.bas.equivFun.symm

theorem coordEquiv_apply (c : Fin (2 * D.R.rS + D.R.k + 1) → D.host.E) : coordEquiv X c = vecOf X c := rfl

theorem coordEquiv_symm_apply (y : (VS D).V) : (coordEquiv X).symm y = crdH X y := by
  apply (coordEquiv X).injective
  rw [LinearEquiv.apply_symm_apply, coordEquiv_apply, vecOf_crdH]

theorem exists_mat (n : (VS D).V ≃ₗ[D.host.E] (VS D).V) :
    ∃ γ : Matrix (Fin (2 * D.R.rS + D.R.k + 1)) (Fin (2 * D.R.rS + D.R.k + 1)) D.host.E, ∀ y, crdH X (n y) = γ *ᵥ crdH X y := by
  refine ⟨LinearMap.toMatrix' (((coordEquiv X).symm.toLinearMap ∘ₗ n.toLinearMap) ∘ₗ (coordEquiv X).toLinearMap), fun y => ?_⟩
  rw [LinearMap.toMatrix'_mulVec]
  simp [coordEquiv_symm_apply, coordEquiv_apply, vecOf_crdH]

theorem exists_equiv (γ : Matrix (Fin (2 * D.R.rS + D.R.k + 1)) (Fin (2 * D.R.rS + D.R.k + 1)) D.host.E) (hU : GlobalTheory.SgAlg.IsUn (D.sp.cm.sig : D.host.E →+* D.host.E) (Jc X) γ) :
    ∃ n : (VS D).V ≃ₗ[D.host.E] (VS D).V, ∀ y, crdH X (n y) = γ *ᵥ crdH X y := by
  have hdet : IsUnit γ.det := by
    rw [isUnit_iff_ne_zero]
    intro h0
    apply Jc_det_ne_zero X
    have := congrArg Matrix.det hU
    rw [Matrix.det_mul, Matrix.det_mul, h0, mul_zero] at this
    exact this.symm
  have h1 : γ⁻¹ * γ = 1 := Matrix.nonsing_inv_mul γ hdet
  have h2 : γ * γ⁻¹ = 1 := Matrix.mul_nonsing_inv γ hdet
  refine ⟨(coordEquiv X).symm.trans ((Matrix.toLin'OfInv h1 h2).trans (coordEquiv X)), fun y => ?_⟩
  simp only [LinearEquiv.trans_apply, coordEquiv_symm_apply, coordEquiv_apply, Matrix.toLin'OfInv_apply,
    Matrix.toLin'_apply, crdH_vecOf]
  rfl

end GlobalTheory.CovDomGrp
