import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CoordEquivSymmApply
open scoped Classical ENNReal
open Matrix MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.LocWSOf Formalism.L2.SG.PoincareInHH.PoincareSetting GlobalTheory.CovDom GlobalTheory.CovDomGrp
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CovDomGrp

theorem coordMat_place : ∀ {D : D7} (X : HidaSetting D) {x : X.B.I.GA} (n : (VS D).V ≃ₗ[D.host.E] (VS D).V) (γ : Matrix (Fin (2 * D.R.rS + D.R.k + 1)) (Fin (2 * D.R.rS + D.R.k + 1)) D.host.E), Formalism.L2.SG.TermOp.RatLink X x n → (∀ y, crdH X (n y) = γ *ᵥ crdH X y) → ∀ τ : D.what₂.Tau, γ.map (embS D τ) = (X.B.I.P (vOf X τ) * uMat (x.1 (vOf X τ)) * (X.B.I.P (vOf X τ))⁻¹).submatrix (ci X) (ci X) := by
  intro D X x n γ hR hγ τ
  obtain ⟨M, -, h1, -, h4⟩ := hR
  have hPu : IsUnit (X.B.I.P (vOf X τ)).det :=
    (Matrix.isUnit_iff_isUnit_det _).1 (X.B.I.P_unit (vOf X τ))
  have hP : X.B.I.P (vOf X τ) * uMat (x.1 (vOf X τ)) * (X.B.I.P (vOf X τ))⁻¹ =
      (M : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E).map (X.B.I.φ (vOf X τ)) := by
    rw [h1 (vOf X τ)]
    simp only [← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hPu, Matrix.one_mul]
    rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hPu, Matrix.mul_one]

  have hN : ∀ c, γ *ᵥ c = (((M : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E).map X.ιE).submatrix (ci X) (ci X)) *ᵥ c := by
    intro c
    have hc := hγ (vecOf X c)
    rw [crdH_vecOf] at hc
    rw [← hc]
    funext i
    rw [crdH_eq_crd, h4]
    simp only [Matrix.mulVec, dotProduct, map_sum, map_mul, Matrix.submatrix_apply, Matrix.map_apply]
    rw [← (ci X).sum_comp]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← crdH_eq_crd, crdH_vecOf]
  have hγe : γ = ((M : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E).map X.ιE).submatrix (ci X) (ci X) :=
    Matrix.toLin'.injective (LinearMap.ext fun c => by rw [Matrix.toLin'_apply, Matrix.toLin'_apply]; exact hN c)
  rw [hP, hγe]
  ext i j
  simp only [Matrix.map_apply, Matrix.submatrix_apply, X.φ_eq]
  congr 1
  simp [vOf]

end GlobalTheory.CovDomGrp
