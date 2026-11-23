import Mathlib
import CompanionTheory.HarishChandraModules.KFiniteAnalyticVectors.AdmissibleSmoothVectors.IwaChol

open Matrix
open scoped ComplexOrder

namespace GlobalTheory.CompanionTheory.Iwasawa

theorem exists_upper_mul_unitary_complex {n : ℕ} (Y : Matrix (Fin n) (Fin n) ℂ) (hY : IsUnit Y) :
    ∃ B R K : Matrix (Fin n) (Fin n) ℂ, B.IsUpperTriangular ∧ B * R = 1 ∧ R * B = 1 ∧
      K * Kᴴ = 1 ∧ Kᴴ * K = 1 ∧ Y = B * K := by
  let e : Fin n ≃ Fin n := Fin.revPerm
  have hYd : Y.det ≠ 0 := ((Matrix.isUnit_iff_isUnit_det Y).mp hY).ne_zero
  set Y' : Matrix (Fin n) (Fin n) ℂ := Y.submatrix e e with hY'
  have hY'u : IsUnit Y' := by
    rw [Matrix.isUnit_iff_isUnit_det, hY', Matrix.det_submatrix_equiv_self]
    exact (Matrix.isUnit_iff_isUnit_det Y).mp hY
  have hpd : (Y' * Y'ᴴ).PosDef :=
    Matrix.PosDef.mul_conjTranspose_self Y' (Matrix.vecMul_injective_iff_isUnit.mpr hY'u)
  obtain ⟨C, a, hCu, -, -, hC⟩ := CompanionTheory.D.gk.admitted.CholeskyDecomposition.exists_cholesky hpd
  have hBu : (Cᴴ.submatrix e e).IsUpperTriangular := by
    intro i j hij
    have h0 : C (e j) (e i) = 0 := hCu (Fin.rev_lt_rev.mpr hij)
    simp only [Matrix.submatrix_apply, Matrix.conjTranspose_apply]
    rw [h0, star_zero]
  have hBB : Cᴴ.submatrix e e * (Cᴴ.submatrix e e)ᴴ = Y * Yᴴ := by
    rw [Matrix.conjTranspose_submatrix, Matrix.conjTranspose_conjTranspose, Matrix.submatrix_mul_equiv, hC,
      hY', Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv, Matrix.submatrix_submatrix]
    have hee : (e : Fin n → Fin n) ∘ e = id := funext fun i => Fin.rev_rev i
    rw [hee, Matrix.submatrix_id_id]
  have hBd : (Cᴴ.submatrix e e).det ≠ 0 := by
    intro h0
    have := congrArg Matrix.det hBB
    rw [Matrix.det_mul, Matrix.det_mul, h0, zero_mul, Matrix.det_conjTranspose] at this
    exact mul_ne_zero hYd (star_ne_zero.mpr hYd) this.symm
  set B := Cᴴ.submatrix e e with hBdef
  have hBi : B⁻¹ * B = 1 := Matrix.nonsing_inv_mul B (isUnit_iff_ne_zero.mpr hBd)
  have hBi' : B * B⁻¹ = 1 := Matrix.mul_nonsing_inv B (isUnit_iff_ne_zero.mpr hBd)
  have hKK : (B⁻¹ * Y) * (B⁻¹ * Y)ᴴ = 1 := by
    calc (B⁻¹ * Y) * (B⁻¹ * Y)ᴴ = B⁻¹ * (Y * Yᴴ) * B⁻¹ᴴ := by
          rw [Matrix.conjTranspose_mul]; simp only [Matrix.mul_assoc]
      _ = B⁻¹ * (B * Bᴴ) * B⁻¹ᴴ := by rw [hBB]
      _ = (B⁻¹ * B) * (B⁻¹ * B)ᴴ := by
          rw [Matrix.conjTranspose_mul]; simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hBi, Matrix.conjTranspose_one, Matrix.mul_one]
  refine ⟨B, B⁻¹, B⁻¹ * Y, hBu, hBi', hBi, hKK, mul_eq_one_comm.mp hKK, ?_⟩
  rw [← Matrix.mul_assoc, hBi', Matrix.one_mul]

noncomputable abbrev evalMat {ι : Type} {n : ℕ} (w : ι) :
    Matrix (Fin n) (Fin n) (ι → ℂ) →+* Matrix (Fin n) (Fin n) ℂ :=
  (Pi.evalRingHom (fun _ : ι => ℂ) w).mapMatrix

theorem evalMat_apply {ι : Type} {n : ℕ} (w : ι) (X : Matrix (Fin n) (Fin n) (ι → ℂ))
    (i j : Fin n) : evalMat w X i j = X i j w := rfl

theorem evalMat_conjTranspose {ι : Type} {n : ℕ} (w : ι) (X : Matrix (Fin n) (Fin n) (ι → ℂ)) :
    evalMat w Xᴴ = (evalMat w X)ᴴ := by
  ext i j
  simp only [evalMat_apply, Matrix.conjTranspose_apply]
  rfl

theorem matrix_ext_eval {ι : Type} {n : ℕ} {X X' : Matrix (Fin n) (Fin n) (ι → ℂ)}
    (h : ∀ w, evalMat w X = evalMat w X') : X = X' := by
  ext i j w
  have := congrFun (congrFun (h w) i) j
  rwa [evalMat_apply, evalMat_apply] at this

theorem exists_upper_mul_unitary {ι : Type} {n : ℕ} (y : GL (Fin n) (ι → ℂ)) :
    ∃ (b : GL (Fin n) (ι → ℂ)) (k : Matrix.unitaryGroup (Fin n) (ι → ℂ)),
      (∀ i j : Fin n, j < i → b.val i j = 0) ∧ y = b * Unitary.toUnits k := by
  have hu : ∀ w : ι, IsUnit (evalMat w (y : Matrix (Fin n) (Fin n) (ι → ℂ))) :=
    fun w => (Units.isUnit y).map (evalMat w)
  choose B R K hB hBR hRB hKK hKK' hY using fun w => exists_upper_mul_unitary_complex _ (hu w)
  let b : Matrix (Fin n) (Fin n) (ι → ℂ) := fun i j w => B w i j
  let r : Matrix (Fin n) (Fin n) (ι → ℂ) := fun i j w => R w i j
  let k : Matrix (Fin n) (Fin n) (ι → ℂ) := fun i j w => K w i j
  have eb : ∀ w, evalMat w b = B w := fun w => by ext i j; rw [evalMat_apply]
  have er : ∀ w, evalMat w r = R w := fun w => by ext i j; rw [evalMat_apply]
  have ek : ∀ w, evalMat w k = K w := fun w => by ext i j; rw [evalMat_apply]
  have hbr : b * r = 1 := matrix_ext_eval fun w => by rw [map_mul, eb, er, hBR w, map_one]
  have hrb : r * b = 1 := matrix_ext_eval fun w => by rw [map_mul, eb, er, hRB w, map_one]
  have hk1 : k * star k = 1 := matrix_ext_eval fun w => by
    rw [map_mul, Matrix.star_eq_conjTranspose, evalMat_conjTranspose, ek, hKK w, map_one]
  have hk2 : star k * k = 1 := matrix_ext_eval fun w => by
    rw [map_mul, Matrix.star_eq_conjTranspose, evalMat_conjTranspose, ek, hKK' w, map_one]
  refine ⟨⟨b, r, hbr, hrb⟩, ⟨k, Unitary.mem_iff.mpr ⟨hk2, hk1⟩⟩, ?_, ?_⟩
  · intro i j hij
    funext w
    exact hB w hij
  · apply Units.ext
    apply matrix_ext_eval
    intro w
    rw [Units.val_mul]
    show evalMat w (y : Matrix (Fin n) (Fin n) (ι → ℂ)) = evalMat w (b * k)
    rw [map_mul, eb, ek]
    exact hY w

end GlobalTheory.CompanionTheory.Iwasawa
