import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IotaScalarOne
open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps GlobalTheory.DetInv Matrix TensorProduct

namespace GlobalTheory.DetInv

theorem charpoly_eq_of_intertwined :
    ∀ (A : Type) [CommRing A] [IsDomain A] (h : ℕ) (μ : A) (F G X Y : Matrix (Fin h) (Fin h) A),
      μ ≠ 0 → G * F = μ • (1 : Matrix (Fin h) (Fin h) A) → F * X = Y * F →
        Y.charpoly = X.charpoly := by
  intro A _ _ h μ F G X Y hμ hGF hFX
  have hdet : F.det ≠ 0 := by
    intro h0
    have h1 := congrArg Matrix.det hGF
    rw [Matrix.det_mul, h0, mul_zero, Matrix.det_smul, Matrix.det_one, mul_one] at h1
    exact pow_ne_zero _ hμ h1.symm
  have hmap : (F.map Polynomial.C) * (X.map Polynomial.C)
      = (Y.map Polynomial.C) * (F.map Polynomial.C) := by
    have := congrArg (fun M => Polynomial.C.mapMatrix M) hFX
    simpa [map_mul] using this
  have hcomm : (F.map Polynomial.C) * Matrix.scalar (Fin h) (Polynomial.X : Polynomial A)
      = Matrix.scalar (Fin h) (Polynomial.X : Polynomial A) * (F.map Polynomial.C) :=
    ((Matrix.scalar_commute _ (fun r => Commute.all _ r) _).eq).symm
  have key : (F.map Polynomial.C) * charmatrix X = charmatrix Y * (F.map Polynomial.C) := by
    simp only [charmatrix, RingHom.mapMatrix_apply, mul_sub, sub_mul]
    rw [hmap, hcomm]
  have hd := congrArg Matrix.det key
  rw [Matrix.det_mul, Matrix.det_mul, mul_comm] at hd
  have hC : (F.map Polynomial.C).det ≠ 0 := by
    have : (F.map Polynomial.C).det = Polynomial.C F.det := by
      simpa using (RingHom.map_det (Polynomial.C : A →+* Polynomial A) F).symm
    rw [this]
    exact Polynomial.C_ne_zero.mpr hdet
  have := mul_right_cancel₀ hC hd
  simpa [Matrix.charpoly] using this.symm

end GlobalTheory.DetInv
