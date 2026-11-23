import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicHensel.PadicUnitNorm

noncomputable section

open NumberField IsDedekindDomain Matrix GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.LKDef GlobalTheory.CuspRep GlobalTheory.UnitaryBC
open UpperTheory.Gal.W2.Seed
open scoped TensorProduct

namespace UpperTheory.Gal.G1

private theorem key_mat {E : Type} [Field E] {n : ℕ} (H Q b b' R : Matrix (Fin n) (Fin n) E) (hd : H.det ≠ 0) (s : E)
    (h : b' * H⁻¹ = Q * (s • (b * H⁻¹)) * R) : b' = s • (Q * b * (H⁻¹ * R * H)) := by
  have hu : IsUnit H.det := isUnit_iff_ne_zero.2 hd
  have h1 : b' = (b' * H⁻¹) * H := (Matrix.nonsing_inv_mul_cancel_right _ _ hu).symm
  rw [h1, h]
  simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc]

theorem pRelOf : RelOf := by
  intro E _ _ _ A n p _ S B B' s hs P hP h
  have hH := A.det_ne n
  have key := key_mat (A.H n) Pᵀ (mat S ↑B.β) (mat S ↑B'.β) (P.map ⇑(IsCMField.complexConj E)) hH
    (s : E) h
  have hdetT : IsUnit (Pᵀ).det := by
    rw [Matrix.det_transpose]
    exact isUnit_iff_ne_zero.mpr hP
  have hu : IsUnit Pᵀ := (Matrix.isUnit_iff_isUnit_det _).mpr hdetT
  have hHc : (A.H n).map ⇑(IsCMField.complexConj E) = A.H n := by
    have h1 := A.herm n
    calc (A.H n).map ⇑(IsCMField.complexConj E) = (((A.H n).map (cj E))ᵀ)ᵀ :=
          (Matrix.transpose_transpose _).symm
      _ = (A.H n)ᵀ := by rw [h1]
      _ = A.H n := by simp [Arith.H]
  have hsh : MulOpposite.unop (hermStar (A.H n) hH Pᵀ) = (A.H n)⁻¹ * P.map ⇑(IsCMField.complexConj E) * A.H n := by
    rw [hermStar_apply]
    change ((A.H n).map ⇑(IsCMField.complexConj E))⁻¹ * ((Pᵀ).map ⇑(IsCMField.complexConj E))ᵀ *
      (A.H n).map ⇑(IsCMField.complexConj E) = _
    rw [hHc, Matrix.transpose_map, Matrix.transpose_transpose]
  refine ⟨hu.unit, s, hs, ?_⟩
  change mat S ↑B'.β = algebraMap ℚ (Matrix (Fin n) (Fin n) E) s *
    (Pᵀ * mat S ↑B.β * MulOpposite.unop (hermStar (A.H n) hH Pᵀ))
  rw [hsh, key, ← Algebra.smul_def, ← algebraMap_smul E s, eq_ratCast]

end UpperTheory.Gal.G1
