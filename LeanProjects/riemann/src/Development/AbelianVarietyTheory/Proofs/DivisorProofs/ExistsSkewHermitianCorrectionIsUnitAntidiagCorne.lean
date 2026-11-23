import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFinMapsOfForall
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMemKAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AntiCols
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.KFinLoc
open scoped TensorProduct Matrix

theorem GlobalTheory.HermBlockChange.exists_unit_lower_block : ∀ (O : Type) [CommRing O] (c : O →+* O), IsUnit (2 : O) →
    (∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) O), (∀ i j, c (J j i) = J i j) → IsUnit J.det →
      ∀ g : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) O, IsUnit g.det →
        gᵀ * Matrix.fromBlocks 0 J J 0 * g.map c = Matrix.fromBlocks 0 J J 0 →
        ∃ Z : Matrix (Fin n) (Fin n) O, Zᵀ * J + J * Z.map c = 0 ∧ IsUnit (g.toBlocks₂₁ * Z + g.toBlocks₂₂).det) →
    ∀ (n : ℕ) (JL : Matrix (Fin n) (Fin n) O) (G G' : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) O),
    (∀ i j, c (JL j i) = JL i j) → IsUnit JL.det → G * G' = 1 →
    Gᵀ * Matrix.fromBlocks JL 0 0 (-JL) * G.map c = Matrix.fromBlocks JL 0 0 (-JL) →
    ∃ Z : Matrix (Fin n) (Fin n) O, Zᵀ * JL + JL * Z.map c = 0 ∧
      IsUnit (((Matrix.fromRows (1 : Matrix (Fin n) (Fin n) O) (-1 : Matrix (Fin n) (Fin n) O))ᵀ : Matrix (Fin n) (Fin n ⊕ Fin n) O) * G * (Matrix.fromRows (1 : Matrix (Fin n) (Fin n) O) (-1 : Matrix (Fin n) (Fin n) O) : Matrix (Fin n ⊕ Fin n) (Fin n) O) +
        ((Matrix.fromRows (1 : Matrix (Fin n) (Fin n) O) (-1 : Matrix (Fin n) (Fin n) O))ᵀ : Matrix (Fin n) (Fin n ⊕ Fin n) O) * G * (Matrix.fromRows (1 : Matrix (Fin n) (Fin n) O) (1 : Matrix (Fin n) (Fin n) O) : Matrix (Fin n ⊕ Fin n) (Fin n) O) * Z).det := by
  intro O _ c h2 hcore n JL G G' hJL hdet hGG' hG
  obtain ⟨a, ha⟩ : ∃ a : O, a * 2 = 1 := ⟨↑(h2.unit⁻¹), by simp⟩
  have ha' : (2 : O) * a = 1 := by rw [mul_comm, ha]
  have hca : c a = a := by
    have h1 : c a * 2 = 1 := by
      have := congrArg c ha
      rwa [map_mul, map_one, map_ofNat] at this
    calc c a = c a * (2 * a) := by rw [ha', mul_one]
      _ = (c a * 2) * a := by ring
      _ = a := by rw [h1, one_mul]
  set Δ : Matrix (Fin n ⊕ Fin n) (Fin n) O := Matrix.fromRows (1 : Matrix (Fin n) (Fin n) O) 1 with hΔ
  set Nb : Matrix (Fin n ⊕ Fin n) (Fin n) O := Matrix.fromRows (1 : Matrix (Fin n) (Fin n) O) (-1) with hNb
  set T : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) O := Matrix.fromCols Δ Nb with hTdef
  have hT : T = Matrix.fromBlocks 1 1 1 (-1) := by
    ext i j; rcases i with i | i <;> rcases j with j | j <;> simp [T, Δ, Nb]
  have hTt : Tᵀ = T := by
    rw [hT, Matrix.fromBlocks_transpose]; simp
  have hTc : T.map c = T := by
    rw [hT, Matrix.fromBlocks_map]; simp
    ext i j; by_cases h : i = j <;> simp [Matrix.one_apply, h]
  have hTT : T * T = (2 : O) • 1 := by
    rw [hT, Matrix.fromBlocks_multiply, ← Matrix.fromBlocks_one, Matrix.fromBlocks_smul]
    simp [two_smul]
  set J : Matrix (Fin n) (Fin n) O := (2 : O) • JL with hJ
  set K : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) O := Matrix.fromBlocks 0 J J 0 with hK
  set D : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) O := Matrix.fromBlocks JL 0 0 (-JL) with hD
  have hTKT : T * K * T = (4 : O) • D := by
    rw [hT, Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply, Matrix.fromBlocks_smul]
    simp [J]
    exact ⟨by rw [← add_smul]; norm_num, by rw [← neg_add, ← add_smul]; norm_num⟩
  have hTDT : T * D * T = K := by
    rw [hT, Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
    simp [K, J, two_smul]
  have h4 : a * a * 4 = (1 : O) := by linear_combination (2 * a + 1) * ha
  set g : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) O := a • (Tᵀ * G * T) with hg
  have hmapsmul : ∀ (b : O) (M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) O), (b • M).map c = c b • M.map c := by
    intro b M; ext i j; simp
  have hgt : gᵀ = a • (T * Gᵀ * T) := by
    simp only [hg, Matrix.transpose_smul, Matrix.transpose_mul, Matrix.transpose_transpose, hTt, Matrix.mul_assoc]
  have hgc : g.map c = a • (T * G.map c * T) := by
    rw [hg, hTt, hmapsmul, Matrix.map_mul, Matrix.map_mul, hTc, hca]
  have hgK : gᵀ * K * g.map c = K := by
    rw [hgt, hgc]
    calc a • (T * Gᵀ * T) * K * a • (T * G.map c * T)
        = (a * a) • (T * Gᵀ * (T * K * T) * G.map c * T) := by
          simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.mul_assoc]
      _ = (a * a * 4) • (T * (Gᵀ * D * G.map c) * T) := by
          rw [hTKT]; simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.mul_assoc]
      _ = K := by rw [hG, h4, one_smul, hTDT]
  have hgdet : g * (a • (T * G' * T)) = 1 := by
    rw [hg, hTt]
    calc a • (T * G * T) * a • (T * G' * T)
        = (a * a) • (T * G * (T * T) * G' * T) := by
          simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.mul_assoc]
      _ = (a * a * 2) • (T * (G * G') * T) := by
          rw [hTT]; simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.mul_assoc, Matrix.one_mul]
      _ = 1 := by
          rw [hGG', Matrix.mul_one, hTT, smul_smul, show a * a * 2 * 2 = (1 : O) by linear_combination (2 * a + 1) * ha, one_smul]
  have hJherm : ∀ i j, c (J j i) = J i j := by intro i j; simp only [J, Matrix.smul_apply, smul_eq_mul, map_mul, map_ofNat, hJL]
  have hJdet : IsUnit J.det := by
    rw [hJ, Matrix.det_smul]; exact (h2.pow _).mul hdet
  obtain ⟨Z, hZ1, hZ2⟩ := hcore n J hJherm hJdet g (Matrix.isUnit_det_of_right_inverse hgdet) hgK
  refine ⟨Z, ?_, ?_⟩
  · have h := congrArg (fun M => a • M) hZ1
    simp only [J, Matrix.mul_smul, Matrix.smul_mul, ← smul_add, smul_smul, ha, one_smul, smul_zero] at h
    exact h
  · have hblk : Tᵀ * G * T = Matrix.fromBlocks (Δᵀ * G * Δ) (Δᵀ * G * Nb) (Nbᵀ * G * Δ) (Nbᵀ * G * Nb) := by
      rw [hTdef, Matrix.transpose_fromCols, Matrix.fromRows_mul, Matrix.fromRows_mul_fromCols]
    have h21 : g.toBlocks₂₁ = a • (Nbᵀ * G * Δ) := by
      rw [hg, hblk, Matrix.fromBlocks_smul, Matrix.toBlocks_fromBlocks₂₁]
    have h22 : g.toBlocks₂₂ = a • (Nbᵀ * G * Nb) := by
      rw [hg, hblk, Matrix.fromBlocks_smul, Matrix.toBlocks_fromBlocks₂₂]
    have hE : Nbᵀ * G * Nb + Nbᵀ * G * Δ * Z = (2 : O) • (g.toBlocks₂₁ * Z + g.toBlocks₂₂) := by
      rw [h21, h22, Matrix.smul_mul, ← smul_add, smul_smul, ha', one_smul, add_comm]
    rw [hE, Matrix.det_smul]; exact (h2.pow _).mul hZ2
