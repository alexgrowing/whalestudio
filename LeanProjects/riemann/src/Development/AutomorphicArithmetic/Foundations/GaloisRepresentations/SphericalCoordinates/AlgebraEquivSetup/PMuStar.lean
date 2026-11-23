import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.ApartOfNotMem

open NumberField IsDedekindDomain Matrix GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKGeo GlobalTheory.LKMid GlobalTheory.LKDef GlobalTheory.CuspRep GlobalTheory.UnitaryBC UpperTheory.Gal.W2.Seed
open UpperTheory.Gal.CertificateRingHomMap (GUf Gam0 AfQ Plc sim mat comp rat lev ZU)
open scoped TensorProduct

private theorem conj_H {E : Type} [Field E] [NumberField E] [IsCMField E] (A : Arith E) (n : ℕ) :
    (A.H n).map (IsCMField.complexConj E : E →+* E) = A.H n := by
  have hc : (IsCMField.complexConj E) ((A.c : 𝓞 E) : E) = (A.c : E) := by
    rw [← A.bar_eq, A.c_real]
  ext i j
  simp only [Arith.H, Matrix.map_apply, Matrix.diagonal_apply]
  split_ifs with hij
  · simp only [Arith.hd, Arith.dg]
    split_ifs <;> simp [hc]
  · simp

private theorem H_eq {E : Type} [Field E] [NumberField E] [IsCMField E] (A : Arith E) (n : ℕ) :
    A.H n = (-(A.c : E)) • Matrix.diagonal (fun i => (A.dg n i : E)) := by
  rw [Arith.H, ← Matrix.diagonal_smul]
  congr 1

private theorem key {E : Type} [Field E] [NumberField E] [IsCMField E] (A : Arith E) (n : ℕ)
    (y : Matrix (Fin n) (Fin n) E) :
    Matrix.diagonal (fun i => (A.dg n i : E)) *
        (((A.H n).map (IsCMField.complexConj E : E →+* E))⁻¹ * y * (A.H n).map (IsCMField.complexConj E : E →+* E)) =
      y * Matrix.diagonal (fun i => (A.dg n i : E)) := by
  rw [conj_H]
  have hc : (-(A.c : E)) ≠ 0 := neg_ne_zero.mpr A.c_ne
  have hD : Matrix.diagonal (fun i => (A.dg n i : E)) = (-(A.c : E))⁻¹ • A.H n := by
    rw [H_eq, smul_smul, inv_mul_cancel₀ hc, one_smul]
  have hu : IsUnit (A.H n).det := isUnit_iff_ne_zero.mpr (A.det_ne n)
  rw [hD, Matrix.smul_mul, Matrix.mul_smul, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
    Matrix.mul_nonsing_inv _ hu, Matrix.one_mul]

theorem UpperTheory.Gal.W2.Seed.pMuStar :
    MuStar := by
  intro R E _ _ _ _ _ A n μ hμ x
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul r m =>
    have hk := key A n ((m.map (IsCMField.complexConj E : E →+* E))ᵀ)
    ext i k
    rw [starT_tmul, hermStar_apply, Matrix.diagonal_mul, Matrix.mul_diagonal, hμ,
      Matrix.transpose_apply, Matrix.map_apply, hμ, conjT_tmul,
      Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one]
    congr 1
    have := congrFun (congrFun hk i) k
    simpa [Matrix.diagonal_mul, Matrix.mul_diagonal] using this
  | add x y hx hy =>
    rw [map_add, MulOpposite.unop_add, map_add, Matrix.mul_add, hx, hy, map_add,
      Matrix.map_add _ (map_add _), Matrix.transpose_add, Matrix.add_mul]
