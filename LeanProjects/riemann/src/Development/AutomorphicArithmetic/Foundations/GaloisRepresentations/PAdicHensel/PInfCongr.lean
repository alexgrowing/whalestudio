import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicHensel.PadicUnitNorm

open NumberField IsDedekindDomain Matrix GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.LKDef GlobalTheory.CuspRep GlobalTheory.UnitaryBC UpperTheory.Gal.W2.Seed UpperTheory.Gal.G1
open scoped TensorProduct

open scoped MatrixOrder ComplexOrder in
private lemma exists_factor {n : ℕ} {A : Matrix (Fin n) (Fin n) ℂ} (hA : A.PosDef) :
    ∃ B : Matrix (Fin n) (Fin n) ℂ, IsUnit B ∧ A = Bᴴ * B := by
  have h0 : 0 ≤ A := hA.posSemidef.nonneg
  have h1 := CFC.sqrt_mul_sqrt_self A h0
  have h2 : IsSelfAdjoint (CFC.sqrt A) := (CFC.sqrt_nonneg A).isSelfAdjoint
  refine ⟨CFC.sqrt A, ?_, ?_⟩
  · have hu : IsUnit (CFC.sqrt A * CFC.sqrt A) := by
      rw [h1]
      exact hA.isUnit
    exact isUnit_of_mul_isUnit_left hu
  · rw [← Matrix.star_eq_conjTranspose, h2.star_eq, h1]

open scoped ComplexOrder in
private lemma smul_posDef {n : ℕ} {M : Matrix (Fin n) (Fin n) ℂ} (hM : M.IsHermitian) {ε : ℝ}
    (h : ∀ x : Fin n → ℂ, x ≠ 0 → 0 < ε * (star x ⬝ᵥ (M *ᵥ x)).re) : ((ε : ℂ) • M).PosDef := by
  have hH : ((ε : ℂ) • M).IsHermitian := by
    unfold Matrix.IsHermitian
    rw [Matrix.conjTranspose_smul, hM.eq]
    simp
  refine Matrix.PosDef.of_dotProduct_mulVec_pos hH ?_
  intro x hx
  have him := hM.im_star_dotProduct_mulVec_self x
  have e : star x ⬝ᵥ ((ε : ℂ) • M) *ᵥ x = (ε : ℂ) * (star x ⬝ᵥ M *ᵥ x) := by
    simp [Matrix.smul_mulVec, dotProduct_smul]
  rw [e, Complex.lt_def]
  simp only [RCLike.im_to_complex] at him
  constructor
  · simpa [him] using h x hx
  · simp [him]

theorem UpperTheory.Gal.G1.pInfCongr :
    InfCongr := by
  intro n G G' hG hG' ε h h'
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    refine ⟨1, by simp, ?_⟩
    exact Subsingleton.elim _ _
  have hε : (ε : ℂ) ≠ 0 := by
    intro h0
    have hx : (fun i : Fin n => if i = ⟨0, hn⟩ then (1 : ℂ) else 0) ≠ 0 := by
      intro hz
      have := congrFun hz ⟨0, hn⟩
      simp at this
    have := h _ hx
    rw [Complex.ofReal_eq_zero.1 h0] at this
    simp at this
  obtain ⟨B, hB, hBe⟩ := exists_factor (smul_posDef hG h)
  obtain ⟨C, hC, hCe⟩ := exists_factor (smul_posDef hG' h')
  have hBd : IsUnit B.det := (Matrix.isUnit_iff_isUnit_det B).1 hB
  have hCd : IsUnit C.det := (Matrix.isUnit_iff_isUnit_det C).1 hC
  set P := B⁻¹ * C with hP
  have hBP : B * P = C := by
    rw [hP, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv B hBd, Matrix.one_mul]
  have key : (ε : ℂ) • G' = (ε : ℂ) • (Pᴴ * G * P) := by
    calc (ε : ℂ) • G' = Cᴴ * C := hCe
      _ = (B * P)ᴴ * (B * P) := by rw [hBP]
      _ = Pᴴ * (Bᴴ * B) * P := by
        rw [Matrix.conjTranspose_mul]
        simp only [Matrix.mul_assoc]
      _ = Pᴴ * ((ε : ℂ) • G) * P := by rw [hBe]
      _ = (ε : ℂ) • (Pᴴ * G * P) := by rw [Matrix.mul_smul, Matrix.smul_mul]
  have hG'P : G' = Pᴴ * G * P := smul_right_injective _ hε key
  refine ⟨P.map (starRingEnd ℂ), ?_, ?_⟩
  · have hdet := (starRingEnd ℂ).map_det P
    rw [RingHom.mapMatrix_apply] at hdet
    rw [← hdet, map_ne_zero, hP, Matrix.det_mul]
    exact ((Matrix.isUnit_nonsing_inv_det B hBd).mul hCd).ne_zero
  · have e1 : (P.map (starRingEnd ℂ))ᵀ = Pᴴ := by
      ext i j
      simp [Matrix.conjTranspose_apply]
    have e2 : (P.map (starRingEnd ℂ)).map (starRingEnd ℂ) = P := by
      ext i j
      simp
    rw [e1, e2]
    exact hG'P
