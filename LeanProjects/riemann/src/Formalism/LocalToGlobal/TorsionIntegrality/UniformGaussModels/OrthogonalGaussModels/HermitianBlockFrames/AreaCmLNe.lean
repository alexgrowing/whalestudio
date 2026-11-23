import Formalism.LocalToGlobal.TorsionIntegrality.UniformGaussModels.OrthogonalGaussModels.HermitianBlockFrames.BlockDiagMulBlockShift

noncomputable section
open scoped BigOperators ComplexConjugate

namespace Formalism.L2.Th1.Top.FrP.UnitaryGroupMassFormula.HermFrame
open Formalism.L2.Th1.Top.FrP

theorem area_cmL_ne (a₀ : ℕ) (b₀ : ℤ) (dK : ℕ) (ha : 0 < a₀) (hdK : 0 < dK) (lam : ℂ) (hlam : lam ≠ 0) :
    area (cmL a₀ b₀ dK ha hdK lam hlam) ≠ 0 := by
  unfold area cmL scalePair cmPair
  simp only
  have e : conj (lam * (a₀ : ℂ)) * (lam * cmTheta b₀ dK) =
      (((a₀ : ℝ) * Complex.normSq lam : ℝ) : ℂ) * cmTheta b₀ dK := by
    rw [map_mul, Complex.conj_natCast]
    push_cast
    rw [Complex.normSq_eq_conj_mul_self]
    ring
  have hth : (cmTheta b₀ dK).im = Real.sqrt dK / 2 := by
    simp [cmTheta]
  rw [e, Complex.im_ofReal_mul, hth]
  have h1 : (0 : ℝ) < a₀ := by exact_mod_cast ha
  have h2 : 0 < Complex.normSq lam := Complex.normSq_pos.mpr hlam
  have h3 : 0 < Real.sqrt dK := Real.sqrt_pos.mpr (by exact_mod_cast hdK)
  exact abs_ne_zero.mpr (by positivity)

theorem gram_G (L : PeriodPair) {n : Type} [Fintype n] [DecidableEq n] (h : Matrix n n ℂ)
    (g₁ : (Fin 4 × n → ℂ) ≃ₗ[ℂ] (Fin 4 × n → ℂ))
    (hIso : IsIsom (matH (blk4 h)) (stdH L (Fin 4 × n)) (g₁ : (Fin 4 × n → ℂ) →ₗ[ℂ] (Fin 4 × n → ℂ))) :
    (gmat g₁).transpose * bd4 h * (gmat g₁).map conj = (((area L : ℝ) : ℂ)⁻¹) • (1 : Matrix _ _ ℂ) := by
  ext u w
  have h1 := hIso (g₁.symm (Pi.single u 1)) (g₁.symm (Pi.single w 1))
  simp only [LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply, stdH_apply] at h1
  have hl : ∑ i, (Pi.single u (1 : ℂ) : Fin 4 × n → ℂ) i * ((area L : ℝ) : ℂ)⁻¹ *
      conj ((Pi.single w (1 : ℂ) : Fin 4 × n → ℂ) i) =
      (((area L : ℝ) : ℂ)⁻¹ • (1 : Matrix (Fin 4 × n) (Fin 4 × n) ℂ)) u w := by
    by_cases huw : u = w
    · subst huw
      simp [Pi.single_apply, Matrix.one_apply]
    · simp [Pi.single_apply, Matrix.one_apply, huw]
      intro hi
      exact absurd hi.symm huw
  rw [hl] at h1
  rw [h1]
  simp only [matH, LinearMap.mk₂'ₛₗ_apply, Matrix.mul_apply, Matrix.transpose_apply,
    Matrix.map_apply, gmat, Finset.sum_mul]
  rw [Finset.sum_comm]
  rfl

theorem ratStep : RatStep := by
  intro a₀ b₀ c₀ dK ha hdK lam hlam hCm l _ hl5 hld hin n _ _ h Λ g₀ g₁ hLat hIso hIdx
  have hΛ : IsSelfDual (matH h) Λ := hLat.2.1
  set L := cmL a₀ b₀ dK ha hdK lam hlam with hL
  set G := gmat g₁ with hGdef
  set Gi : Matrix (Fin 4 × n) (Fin 4 × n) ℂ :=
    LinearMap.toMatrix' (g₁ : (Fin 4 × n → ℂ) →ₗ[ℂ] (Fin 4 × n → ℂ)) with hGidef
  have hGGi : G * Gi = 1 := by
    rw [hGdef, hGidef, gmat_eq, ← LinearMap.toMatrix'_comp]
    have : ((g₁.symm : (Fin 4 × n → ℂ) →ₗ[ℂ] (Fin 4 × n → ℂ)) ∘ₗ (g₁ : (Fin 4 × n → ℂ) →ₗ[ℂ] (Fin 4 × n → ℂ)))
        = LinearMap.id := by ext x; simp
    rw [this, LinearMap.toMatrix'_id]
  have hGiG : Gi * G = 1 := by
    rw [hGdef, hGidef, gmat_eq, ← LinearMap.toMatrix'_comp]
    have : ((g₁ : (Fin 4 × n → ℂ) →ₗ[ℂ] (Fin 4 × n → ℂ)) ∘ₗ (g₁.symm : (Fin 4 × n → ℂ) →ₗ[ℂ] (Fin 4 × n → ℂ)))
        = LinearMap.id := by ext x; simp
    rw [this, LinearMap.toMatrix'_id]
  have hint : ∀ T : Matrix (Fin 4 × n) (Fin 4 × n) ℂ, (∀ y ∈ pow4 Λ, Matrix.toLin' T y ∈ pow4 Λ) →
      ∀ x w, ∃ q₁ q₂ : ℚ, padicNorm l q₁ ≤ 1 ∧ padicNorm l q₂ ≤ 1 ∧ (Gi * T * G) x w = q₁ + q₂ * sq dK := by
    intro T hT x w
    rw [hGidef, hGdef, conj_matrix_apply]
    exact conj_entry_int hCm l hl5 hin h Λ hΛ g₁ hIso hIdx _ hT x w
  obtain ⟨w, hPu⟩ := exists_cols G Gi hGGi
  set P : Matrix n n ℂ := Matrix.of fun i j => G (0, i) (w j) with hP
  have hdetP : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det P).mp hPu
  set Pinv := P⁻¹ with hPinv
  have hPP : P * Pinv = 1 := Matrix.mul_nonsing_inv P hdetP
  have hPP' : Pinv * P = 1 := Matrix.nonsing_inv_mul P hdetP
  set S : Matrix (Fin 4 × n) (Fin 4 × n) ℂ :=
    Matrix.of fun x (y : Fin 4 × n) => (Gi * (mv y.1 : Matrix (Fin 4 × n) (Fin 4 × n) ℂ) * G) x (w y.2) with hS
  clear_value S
  have hGS : G * S = bd4 P := by
    ext z ⟨a, j⟩
    have e := congrFun (congrFun (show G * (Gi * (mv a : Matrix (Fin 4 × n) (Fin 4 × n) ℂ) * G) =
      (mv a : Matrix (Fin 4 × n) (Fin 4 × n) ℂ) * G by
        rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hGGi, Matrix.one_mul]) z) (w j)
    rw [mv_mul_apply, Matrix.mul_apply] at e
    rw [Matrix.mul_apply]
    simp only [hS, Matrix.of_apply]
    rw [e]
    simp only [bd4, hP, Matrix.of_apply]
  have hSdef : S = Gi * bd4 P := by rw [← hGS, ← Matrix.mul_assoc, hGiG, Matrix.one_mul]
  set M := bd4 Pinv * G with hM
  clear_value M
  have hSM : S * M = 1 := by
    rw [hSdef, hM, Matrix.mul_assoc, ← Matrix.mul_assoc (bd4 P), bd4_mul, hPP, bd4_one, Matrix.one_mul, hGiG]
  have hMS : M * S = 1 := by
    rw [hSdef, hM, Matrix.mul_assoc, ← Matrix.mul_assoc G, hGGi, Matrix.one_mul, bd4_mul, hPP', bd4_one]
  have hSK : ∀ x y, S x y ∈ Kc dK hdK := fun x y => by
    obtain ⟨q₁, q₂, -, -, e⟩ := hint (mv y.1) (mv_pres Λ y.1) x (w y.2)
    exact ⟨q₁, q₂, by rw [hS]; exact e⟩
  have hMK : ∀ x y, M x y ∈ Kc dK hdK := by
    set S' : Matrix (Fin 4 × n) (Fin 4 × n) (Kc dK hdK) := Matrix.of fun x y => ⟨S x y, hSK x y⟩ with hS'
    have hS'map : S'.map (Kc dK hdK).subtype = S := by ext x y; rfl
    have hdetS : IsUnit S.det := by
      have e := congrArg Matrix.det hSM
      rw [Matrix.det_mul, Matrix.det_one] at e
      exact isUnit_iff_ne_zero.mpr (left_ne_zero_of_mul_eq_one e)
    have hdet : IsUnit S'.det := by
      have e : (Kc dK hdK).subtype S'.det = S.det := by rw [RingHom.map_det]; rfl
      refine isUnit_iff_ne_zero.mpr fun h0 => ?_
      rw [h0, map_zero] at e
      exact not_isUnit_zero (e ▸ hdetS)
    have hinv : S * (S'⁻¹).map (Kc dK hdK).subtype = 1 := by
      rw [← hS'map, ← Matrix.map_mul, Matrix.mul_nonsing_inv _ hdet]
      exact Matrix.map_one _ (map_zero _) (map_one _)
    have e : M = (S'⁻¹).map (Kc dK hdK).subtype := by
      calc M = M * (S * (S'⁻¹).map (Kc dK hdK).subtype) := by rw [hinv, Matrix.mul_one]
        _ = _ := by rw [← Matrix.mul_assoc, hMS, Matrix.one_mul]
    intro x y
    rw [e]
    exact (S'⁻¹ x y).2
  have hA : ((area L : ℝ) : ℂ) ≠ 0 := by exact_mod_cast area_cmL_ne a₀ b₀ dK ha hdK lam hlam
  have hgram := gram_G L h g₁ hIso
  have hGi : Gi.transpose * Gi.map conj = ((area L : ℝ) : ℂ) • bd4 h := by
    have e1 : Gi.transpose * (G.transpose * bd4 h * G.map conj) * Gi.map conj = bd4 h := by
      have : Gi.transpose * (G.transpose * bd4 h * G.map conj) * Gi.map conj
          = (G * Gi).transpose * bd4 h * (G * Gi).map (starRingEnd ℂ) := by
        rw [Matrix.transpose_mul, Matrix.map_mul]; simp only [Matrix.mul_assoc]
      rw [this, hGGi]; simp
    rw [hGdef] at e1
    rw [hgram, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul] at e1
    rw [← e1, smul_smul, mul_inv_cancel₀ hA, one_smul]
  set R : Matrix n n ℂ := ((area L : ℝ) : ℂ) • (P.transpose * h * P.map conj) with hR
  clear_value R
  have hbdR : bd4 R = S.transpose * S.map conj := by
    rw [hSdef, Matrix.transpose_mul, Matrix.map_mul, bd4_transpose, bd4_map _ (map_zero _),
      show bd4 P.transpose * Gi.transpose * (Gi.map (starRingEnd ℂ) * bd4 (P.map (starRingEnd ℂ)))
        = bd4 P.transpose * (Gi.transpose * Gi.map (starRingEnd ℂ)) * bd4 (P.map (starRingEnd ℂ)) by
          simp only [Matrix.mul_assoc],
      hGi, Matrix.mul_smul, Matrix.smul_mul, bd4_mul, bd4_mul, hR, bd4_smul]
  have hRK : ∀ i j, R i j ∈ Kc dK hdK := by
    intro i j
    have e : R i j = (S.transpose * S.map conj) (0, i) (0, j) := by rw [← hbdR]; simp [bd4]
    rw [e, Matrix.mul_apply]
    exact Subfield.sum_mem _ fun x _ => Subfield.mul_mem _ (hSK x (0, i)) (conj_mem_Kc (hSK x (0, j)))
  have hGramM : M.transpose * bd4 R * M.map conj = 1 := by
    rw [hbdR]
    calc M.transpose * (S.transpose * S.map conj) * M.map conj
        = (S * M).transpose * (S * M).map (starRingEnd ℂ) := by
          rw [Matrix.transpose_mul, Matrix.map_mul]; simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hSM]; simp
  have hUeq : ∀ k : Fin 4, (bmv0 k : Matrix _ _ ℂ) * M = M * (Gi * bmv0 k * G) := by
    intro k
    calc (bmv0 k : Matrix _ _ ℂ) * M = bmv0 k * bd4 Pinv * G := by rw [hM, Matrix.mul_assoc]
      _ = bd4 Pinv * bmv0 k * G := by rw [blockDiag_mul_blockShift]
      _ = bd4 Pinv * (G * Gi) * bmv0 k * G := by rw [hGGi, Matrix.mul_one]
      _ = M * (Gi * bmv0 k * G) := by rw [hM]; simp only [Matrix.mul_assoc]
  have hMK' : ∀ x y, ∃ q₁ q₂ : ℚ, M x y = q₁ + q₂ * sq dK := hMK
  have hRK' : ∀ i j, ∃ q₁ q₂ : ℚ, R i j = q₁ + q₂ * sq dK := hRK
  choose M₁ M₂ hMd using hMK'
  choose R₁ R₂ hRd using hRK'
  have hkM : kmat dK (Matrix.of M₁) (Matrix.of M₂) = M := by
    ext x y; simp [kmat, hMd x y, mul_comm]
  have hkMc : kmat dK (Matrix.of M₁) (-Matrix.of M₂) = M.map conj := by
    ext x y; simp [kmat, hMd x y, sq_conj, mul_comm]
  have hkR : kmat dK (Matrix.of R₁) (Matrix.of R₂) = R := by
    ext x y; simp [kmat, hRd x y, mul_comm]
  refine ⟨lam • P, Matrix.of M₁, Matrix.of M₂, Matrix.of R₁, Matrix.of R₂, 1, padicNorm.one, ?_, ?_, ?_⟩
  · rw [hkM, bd4_smul, Matrix.smul_mul, smul_smul, inv_mul_cancel₀ hlam, one_smul, hM, ← Matrix.mul_assoc,
      bd4_mul, hPP, bd4_one, Matrix.one_mul]
  · rw [hkM, hkR, hkMc, hGramM]; simp
  · intro k
    have := hint (bmv0 k) (blockShift_mapsTo Λ k)
    choose U₁ U₂ hU₁ hU₂ hUe using this
    refine ⟨Matrix.of U₁, Matrix.of U₂, fun x y => ⟨hU₁ x y, hU₂ x y⟩, ?_⟩
    rw [hkM, hUeq k]
    congr 1
    ext x y; simp [kmat, hUe x y, mul_comm]

end Formalism.L2.Th1.Top.FrP.UnitaryGroupMassFormula.HermFrame
