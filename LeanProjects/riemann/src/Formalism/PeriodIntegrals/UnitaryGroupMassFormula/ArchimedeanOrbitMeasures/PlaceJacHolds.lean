import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.PjRows

noncomputable section

namespace PI.AprimeInfW

open MeasureTheory Matrix

theorem const_alg (N P : ℝ) (k m : ℕ) (hN : N ≠ 0) (hP : P ≠ 0) :
    ((1 / P * N) ^ k)⁻¹ * (((P * N) ^ m)⁻¹ * ((1 / P ^ 2 * (N * (N ^ 2)⁻¹)) ^ m)⁻¹) = P ^ m * P ^ k / N ^ k := by
  have h1 : N * (N ^ 2)⁻¹ = N⁻¹ := by
    rw [pow_two, mul_inv, ← mul_assoc, mul_inv_cancel₀ hN, one_mul]
  have h2 : 1 / P ^ 2 * N⁻¹ = (P ^ 2 * N)⁻¹ := by
    rw [one_div, mul_inv]
  rw [h1, h2, inv_pow, inv_inv, one_div, mul_pow, mul_pow, mul_pow, mul_inv, inv_pow, inv_inv, ← pow_mul]
  field_simp
  ring

private theorem sum_eq_sum_compl_equiv_of_eq_zero_on {n m : ℕ} (S : Finset (Fin n)) (eU : Fin m ≃ {i // i ∉ S})
    (f : Fin n → ℂ) (hf : ∀ i ∈ S, f i = 0) : ∑ i, f i = ∑ c, f (eU c) := by
  classical
  rw [← Fintype.sum_subtype_add_sum_subtype (fun i => i ∈ S) f,
    Finset.sum_eq_zero (fun i _ => hf i.1 i.2), zero_add]
  exact (Equiv.sum_comp eU (fun i => f i)).symm

private theorem rowsM_mul {n k m : ℕ} (S : Finset (Fin n)) (eS : Fin k ≃ ↥S)
    (eU : Fin m ≃ {i // i ∉ S}) (X : Matrix (Fin k) (Fin m) ℂ) (Y Z : Matrix (Fin m) (Fin m) ℂ) :
    rowsM S eS eU X Y * Z = rowsM S eS eU (X * Z) (Y * Z) := by
  ext i j
  by_cases hi : i ∈ S <;> simp [rowsM, hi, Matrix.mul_apply]

private theorem rowsM_add_rowsM {n k m : ℕ} (S : Finset (Fin n)) (eS : Fin k ≃ ↥S)
    (eU : Fin m ≃ {i // i ∉ S}) (X X' : Matrix (Fin k) (Fin m) ℂ) (Y Y' : Matrix (Fin m) (Fin m) ℂ) :
    rowsM S eS eU X Y + rowsM S eS eU X' Y' = rowsM S eS eU (X + X') (Y + Y') := by
  ext i j
  by_cases hi : i ∈ S <;> simp [rowsM, hi]

private theorem smul_rowsM {n k m : ℕ} (S : Finset (Fin n)) (eS : Fin k ≃ ↥S)
    (eU : Fin m ≃ {i // i ∉ S}) (c : ℂ) (X : Matrix (Fin k) (Fin m) ℂ) (Y : Matrix (Fin m) (Fin m) ℂ) :
    c • rowsM S eS eU X Y = rowsM S eS eU (c • X) (c • Y) := by
  ext i j
  by_cases hi : i ∈ S <;> simp [rowsM, hi]

private theorem xiF_mul_eq_rowsM {n k m : ℕ} {η : Type} [Fintype η] (ε : Fin n → Bool) (S : Finset (Fin n))
    (eS : Fin k ≃ ↥S) (eU : Fin m ≃ {i // i ∉ S}) (H : EuclideanSpace ℝ η →ₗ[ℝ] Matrix (Fin m) (Fin m) ℂ)
    (w : Matrix (Fin n) (Fin m) ℂ) (hw : ∀ i ∈ S, ∀ b, w i b = 0)
    (z : EuclideanSpace ℝ (Fin k × Fin m × Bool) × EuclideanSpace ℝ η) :
    xiF ε S eS eU H z * w = rowsM S eS eU (Matrix.of (cpx z.1) * (r2 • Matrix.of fun b j => w (eU b) j))
      (Matrix.diagonal (fun a => sgn ε (eU a)) * (Complex.I • H z.2) * Matrix.of fun b j => w (eU b) j) := by
  ext i j
  rw [Matrix.mul_apply, sum_eq_sum_compl_equiv_of_eq_zero_on S eU _ (fun l hl => by rw [hw l hl, mul_zero])]
  by_cases hi : i ∈ S
  · obtain ⟨a, rfl⟩ : ∃ a, ((eS a : ↥S) : Fin n) = i := ⟨eS.symm ⟨i, hi⟩, by simp⟩
    rw [rowsM_S]
    simp only [xi_SU, Matrix.mul_apply, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul]
    refine Finset.sum_congr rfl fun b _ => ?_
    ring
  · obtain ⟨a, rfl⟩ : ∃ a, ((eU a : {i // i ∉ S}) : Fin n) = i := ⟨eU.symm ⟨i, hi⟩, by simp⟩
    rw [rowsM_U, Matrix.mul_apply]
    simp only [xi_UU, Matrix.diagonal_mul, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul]
    refine Finset.sum_congr rfl fun b _ => ?_
    ring

private theorem mul_eq_rowsM_zero_of_zero_on {n k m : ℕ} (S : Finset (Fin n)) (eS : Fin k ≃ ↥S)
    (eU : Fin m ≃ {i // i ∉ S}) (w : Matrix (Fin n) (Fin m) ℂ) (hw : ∀ i ∈ S, ∀ b, w i b = 0)
    (X : Matrix (Fin m) (Fin m) ℂ) :
    w * X = rowsM S eS eU 0 ((Matrix.of fun b j => w (eU b) j) * X) := by
  ext i j
  by_cases hi : i ∈ S
  · simp [rowsM, hi, Matrix.mul_apply, hw i hi]
  · simp [rowsM, hi, Matrix.mul_apply]

private theorem conjTranspose_mul_Jm_mul_eq_of_zero_on {n m : ℕ} (ε : Fin n → Bool) (S : Finset (Fin n))
    (eU : Fin m ≃ {i // i ∉ S}) (w : Matrix (Fin n) (Fin m) ℂ) (hw : ∀ i ∈ S, ∀ b, w i b = 0) :
    wᴴ * Formalism.REAL.Jm ε * w = (Matrix.of fun b j => w (eU b) j)ᴴ *
      Matrix.diagonal (fun a => sgn ε (eU a)) * (Matrix.of fun b j => w (eU b) j) := by
  ext a b
  rw [Matrix.mul_apply, Matrix.mul_apply, sum_eq_sum_compl_equiv_of_eq_zero_on S eU _ (fun i hi => by rw [hw i hi b, mul_zero])]
  refine Finset.sum_congr rfl fun c _ => ?_
  simp [Formalism.REAL.Jm, Matrix.mul_diagonal, sgn, Matrix.conjTranspose_apply]

private theorem rsL_reim_eq_reim_rowsM {n k m : ℕ} (S : Finset (Fin n)) (eS : Fin k ≃ ↥S)
    (eU : Fin m ≃ {i // i ∉ S}) (X : Matrix (Fin k) (Fin m) ℂ) (Y : Matrix (Fin m) (Fin m) ℂ) :
    rsL S eS eU (reim X, reim Y) = reim (rowsM S eS eU X Y) := by
  have h1 : ∀ {p q : ℕ} (Z : Matrix (Fin p) (Fin q) ℂ), Matrix.of (cpx (reim Z)) = Z := by
    intro p q Z
    ext a b
    exact cpx_reim Z a b
  rw [rsL_apply, h1, h1]

private theorem dg_smul_mul_add_half_eq_half_mul_add {m : ℕ} (W0 Dg Hz Ht : Matrix (Fin m) (Fin m) ℂ) (hW : W0.det ≠ 0)
    (hD : Dg * Dg = 1) :
    Dg * (Complex.I • Hz) * W0 + (1 / 2 : ℂ) • (W0 * (W0ᴴ * Dg * W0)⁻¹ * Ht) =
      ((1 / 2 : ℂ) • (Dg * W0ᴴ⁻¹)) *
        (Complex.I • ((((Real.sqrt 2 : ℝ) : ℂ) • W0)ᴴ * Hz * (((Real.sqrt 2 : ℝ) : ℂ) • W0)) + Ht) := by
  have hWu : IsUnit W0.det := isUnit_iff_ne_zero.mpr hW
  have hWHu : IsUnit W0ᴴ.det := by
    rw [Matrix.det_conjTranspose]
    exact isUnit_iff_ne_zero.mpr (star_ne_zero.mpr hW)
  have hDinv : Dg⁻¹ = Dg := Matrix.inv_eq_left_inv hD
  have hG : W0 * (W0ᴴ * Dg * W0)⁻¹ = Dg * W0ᴴ⁻¹ := by
    rw [Matrix.mul_inv_rev, Matrix.mul_inv_rev, hDinv, ← Matrix.mul_assoc,
      Matrix.mul_nonsing_inv _ hWu, Matrix.one_mul]
  have hB : (((Real.sqrt 2 : ℝ) : ℂ) • W0)ᴴ * Hz * (((Real.sqrt 2 : ℝ) : ℂ) • W0) =
      (2 : ℂ) • (W0ᴴ * Hz * W0) := by
    simp only [Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
    congr 1
    rw [Complex.star_def, Complex.conj_ofReal, ← Complex.ofReal_mul,
      Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  rw [hG, hB]
  have hP : W0ᴴ⁻¹ * W0ᴴ = 1 := Matrix.nonsing_inv_mul _ hWHu
  simp only [Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc W0ᴴ⁻¹ W0ᴴ, hP, Matrix.one_mul]
  congr 1
  congr 1
  ring

private theorem of_reimE_reim {p q : ℕ} (Z : Matrix (Fin p) (Fin q) ℂ) :
    Matrix.of ((reimE (r := p) (m := q)).symm (reim Z)) = Z :=
  (reimE (r := p) (m := q)).symm_apply_apply Z

private theorem continuous_reim {p q : ℕ} : Continuous (fun Y : Matrix (Fin p) (Fin q) ℂ => reim Y) :=
  (reimL (n := p) (m := q)).continuous_of_finiteDimensional.congr fun Y => reimL_apply Y

set_option maxHeartbeats 800000 in

private theorem key_lemma_12 {n m : ℕ} {ι η : Type} [Fintype ι] [Fintype η] (ε : Fin n → Bool)
    (S : Finset (Fin n)) (eS : Fin S.card ≃ ↥S) (eU : Fin m ≃ {i // i ∉ S})
    (w : Matrix (Fin n) (Fin m) ℂ) (hw : ∀ i ∈ S, ∀ b, w i b = 0)
    (L : EuclideanSpace ℝ ι →ₗ[ℝ] Matrix (Fin n) (Fin n) ℂ)
    (H : EuclideanSpace ℝ η →ₗ[ℝ] Matrix (Fin m) (Fin m) ℂ) (hH : ∀ t, (H t)ᴴ = H t)
    (hnH : ∀ t, ∑ i, ∑ j, ‖H t i j‖ ^ 2 = ‖t‖ ^ 2) (hsH : ∀ M : Matrix (Fin m) (Fin m) ℂ, Mᴴ = M → ∃ t, H t = M)
    (Λ : EuclideanSpace ℝ (Fin S.card × Fin m × Bool) × EuclideanSpace ℝ η →ₗ[ℝ] EuclideanSpace ℝ ι)
    (hLΛ : ∀ z, L (Λ z) = xiF ε S eS eU H z) (W0 Dg B A2 : Matrix (Fin m) (Fin m) ℂ)
    (hW0def : W0 = Matrix.of fun b j => w (eU b) j) (hDgdef : Dg = Matrix.diagonal fun a => sgn ε (eU a))
    (hBdef : B = ((Real.sqrt 2 : ℝ) : ℂ) • W0) (hA2def : A2 = (1 / 2 : ℂ) • (Dg * W0ᴴ⁻¹))
    (hW0 : W0.det ≠ 0) (hDD : Dg * Dg = 1)
    (z1 : EuclideanSpace ℝ (Fin S.card × Fin m × Bool)) (z2 t : EuclideanSpace ℝ η) :
    reim (L (Λ (z1, z2)) * w + (1 / 2 : ℂ) • (w * (wᴴ * Formalism.REAL.Jm ε * w)⁻¹ * H t)) =
      rsL S eS eU (reim (Matrix.of ((reimE (r := S.card) (m := m)).symm z1) * (r2 • W0)),
        reim (A2 * Matrix.of ((reimE (r := m) (m := m)).symm
          (psiLp H (congH H hH hnH hsH B z2, t))))) := by
  subst hBdef hA2def
  rw [hLΛ, xiF_mul_eq_rowsM ε S eS eU H w hw, mul_eq_rowsM_zero_of_zero_on S eS eU w hw, rowsM_mul, smul_rowsM,
    rowsM_add_rowsM, psiLp_apply, of_reimE_reim, ← cpx_eq, rsL_reim_eq_reim_rowsM, congH_spec,
    conjTranspose_mul_Jm_mul_eq_of_zero_on ε S eU w hw, ← hW0def, ← hDgdef]
  congr 2
  · rw [Matrix.zero_mul, smul_zero, add_zero]
  · exact dg_smul_mul_add_half_eq_half_mul_add W0 Dg (H z2) (H t) hW0 hDD

set_option maxHeartbeats 800000 in

private theorem map_volume_reim_block_eq_of_det_ne_zero {m : ℕ} {η : Type} [Fintype η]
    (H : EuclideanSpace ℝ η →ₗ[ℝ] Matrix (Fin m) (Fin m) ℂ) (hH : ∀ t, (H t)ᴴ = H t)
    (hnH : ∀ t, ∑ i, ∑ j, ‖H t i j‖ ^ 2 = ‖t‖ ^ 2) (hsH : ∀ M : Matrix (Fin m) (Fin m) ℂ, Mᴴ = M → ∃ t, H t = M)
    (B A2 : Matrix (Fin m) (Fin m) ℂ) (hB : B.det ≠ 0) (hA : A2.det ≠ 0) :
    (volume : Measure (EuclideanSpace ℝ η × EuclideanSpace ℝ η)).map
      (fun p => reim (A2 * Matrix.of ((reimE (r := m) (m := m)).symm
        (psiLp H (Prod.map (congH H hH hnH hsH B) id p))))) =
      (ENNReal.ofReal (Complex.normSq B.det ^ m)⁻¹ * ENNReal.ofReal (Complex.normSq A2.det ^ m)⁻¹) •
        volume := by
  have hc2 : Continuous fun y : EuclideanSpace ℝ (Fin m × Fin m × Bool) =>
      Matrix.of ((reimE (r := m) (m := m)).symm y) :=
    (reimE (r := m) (m := m)).symm.toLinearMap.continuous_of_finiteDimensional
  have hmulLm : Measurable fun y : EuclideanSpace ℝ (Fin m × Fin m × Bool) =>
      reim (A2 * Matrix.of ((reimE (r := m) (m := m)).symm y)) :=
    (continuous_reim.comp (continuous_const.matrix_mul hc2)).measurable
  have hpsim : Measurable (psiLp H) := (psiLp H).continuous_of_finiteDimensional.measurable
  have hcgm : Measurable (congH H hH hnH hsH B) :=
    (congH H hH hnH hsH B).continuous_of_finiteDimensional.measurable
  have hPm : Measurable (Prod.map (congH H hH hnH hsH B)
      (id : EuclideanSpace ℝ η → EuclideanSpace ℝ η)) := Measurable.prodMap hcgm measurable_id
  have hcg : (volume : Measure (EuclideanSpace ℝ η × EuclideanSpace ℝ η)).map
      (Prod.map (congH H hH hnH hsH B) id) =
      ENNReal.ofReal (Complex.normSq B.det ^ m)⁻¹ • volume := by
    rw [Measure.volume_eq_prod, ← Measure.map_prod_map _ _ hcgm measurable_id,
      cong_factor H hH hnH hsH B hB, Measure.map_id, Measure.prod_smul_left]
  have e : (fun p => reim (A2 * Matrix.of ((reimE (r := m) (m := m)).symm
      (psiLp H (Prod.map (congH H hH hnH hsH B) id p))))) =
      (fun y => reim (A2 * Matrix.of ((reimE (r := m) (m := m)).symm y))) ∘ (psiLp H) ∘
        (Prod.map (congH H hH hnH hsH B) id) := rfl
  rw [e, ← Measure.map_map hmulLm (hpsim.comp hPm), ← Measure.map_map hpsim hPm, hcg,
    Measure.map_smul, (psi_mp H hH hnH hsH).map_eq, Measure.map_smul, map_mulL A2 hA, smul_smul]

private theorem inv_pow_mul_inv_pow_eq_two_pow_div_pow (N : ℝ) (m k : ℕ) (hN : N ≠ 0) :
    ((1 / (2 : ℝ) ^ m * N) ^ k)⁻¹ * ((((2 : ℝ) ^ m * N) ^ m)⁻¹ * (((1 / 4 : ℝ) ^ m * N⁻¹) ^ m)⁻¹) =
      2 ^ ((m + k) * m) / N ^ k := by
  have h4 : (1 / 4 : ℝ) ^ m * N⁻¹ = 1 / ((2 : ℝ) ^ m) ^ 2 * (N * (N ^ 2)⁻¹) := by
    rw [show N * (N ^ 2)⁻¹ = N⁻¹ by rw [sq, mul_inv, ← mul_assoc, mul_inv_cancel₀ hN, one_mul],
      show ((2 : ℝ) ^ m) ^ 2 = 4 ^ m by rw [← pow_mul, mul_comm, pow_mul]; norm_num,
      _root_.one_div_pow]
  rw [h4, const_alg N (2 ^ m) k m hN (by positivity), ← pow_mul, ← pow_mul, ← pow_add]
  congr 1
  ring

set_option maxHeartbeats 800000 in

theorem placeJac_holds : PlaceJac := by
  intro n m ε S w ι η _ _ L H hn hw hG hL hnL hLs hH hnH hsH
  classical
  have hcardU : Fintype.card {i // i ∉ S} = m := by
    simp only [Fintype.card_subtype_compl, Fintype.card_fin, Fintype.card_coe]
    omega
  obtain ⟨eS⟩ : Nonempty (Fin S.card ≃ ↥S) := ⟨S.equivFin.symm⟩
  obtain ⟨eU⟩ : Nonempty (Fin m ≃ {i // i ∉ S}) := ⟨(Fintype.equivFinOfCardEq hcardU).symm⟩
  obtain ⟨W0, hW0def⟩ : ∃ X : Matrix (Fin m) (Fin m) ℂ, X = Matrix.of fun b j => w (eU b) j := ⟨_, rfl⟩
  obtain ⟨Dg, hDgdef⟩ : ∃ X : Matrix (Fin m) (Fin m) ℂ, X = Matrix.diagonal fun a => sgn ε (eU a) :=
    ⟨_, rfl⟩
  obtain ⟨B, hBdef⟩ : ∃ X : Matrix (Fin m) (Fin m) ℂ, X = ((Real.sqrt 2 : ℝ) : ℂ) • W0 := ⟨_, rfl⟩
  obtain ⟨A2, hA2def⟩ : ∃ X : Matrix (Fin m) (Fin m) ℂ, X = (1 / 2 : ℂ) • (Dg * W0ᴴ⁻¹) := ⟨_, rfl⟩
  have hgram : wᴴ * Formalism.REAL.Jm ε * w = W0ᴴ * Dg * W0 := by
    rw [hW0def, hDgdef]
    exact conjTranspose_mul_Jm_mul_eq_of_zero_on ε S eU w hw
  have hDD : Dg * Dg = 1 := by
    rw [hDgdef, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext a
    simp only [sgn]
    split_ifs <;> norm_num
  have hDnorm : ‖Dg.det‖ = 1 := by
    rw [hDgdef, Matrix.det_diagonal, norm_prod]
    refine Finset.prod_eq_one fun a _ => ?_
    simp only [sgn]
    split_ifs <;> simp
  have hW0 : W0.det ≠ 0 := by
    intro h0
    apply hG
    rw [hgram, Matrix.det_mul, Matrix.det_mul, h0, mul_zero]
  have hWHu : IsUnit W0ᴴ.det := by
    rw [Matrix.det_conjTranspose]
    exact isUnit_iff_ne_zero.mpr (star_ne_zero.mpr hW0)
  have hDdet : Dg.det ≠ 0 := by
    intro h
    rw [h, norm_zero] at hDnorm
    exact zero_ne_one hDnorm
  have hBdet : B.det ≠ 0 := by
    rw [hBdef, Matrix.det_smul]
    exact mul_ne_zero (pow_ne_zero _ (Complex.ofReal_ne_zero.mpr
      (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2)).ne')) hW0
  have hA2det : A2.det ≠ 0 := by
    rw [hA2def, Matrix.det_smul, Matrix.det_mul]
    exact mul_ne_zero (pow_ne_zero _ (by norm_num))
      (mul_ne_zero hDdet (Matrix.isUnit_nonsing_inv_det _ hWHu).ne_zero)
  have hR : (r2 • W0).det ≠ 0 := by
    rw [Matrix.det_smul]
    exact mul_ne_zero (pow_ne_zero _ (Complex.ofReal_ne_zero.mpr
      (inv_pos.mpr (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2))).ne')) hW0

  obtain ⟨Λ, hΛ, hLΛ⟩ := dom_exists (ε := ε) (S := S) (eS := eS) (eU := eU) (H := H)
    L hL hnL hLs hH hnH hsH

  have hc1 : Continuous fun y : EuclideanSpace ℝ (Fin S.card × Fin m × Bool) =>
      Matrix.of ((reimE (r := S.card) (m := m)).symm y) :=
    (reimE (r := S.card) (m := m)).symm.toLinearMap.continuous_of_finiteDimensional
  have hc2 : Continuous fun y : EuclideanSpace ℝ (Fin m × Fin m × Bool) =>
      Matrix.of ((reimE (r := m) (m := m)).symm y) :=
    (reimE (r := m) (m := m)).symm.toLinearMap.continuous_of_finiteDimensional
  have hΦ1m : Measurable fun y : EuclideanSpace ℝ (Fin S.card × Fin m × Bool) =>
      reim (Matrix.of ((reimE (r := S.card) (m := m)).symm y) * (r2 • W0)) :=
    (continuous_reim.comp (hc1.matrix_mul continuous_const)).measurable
  have hmulLm : Measurable fun y : EuclideanSpace ℝ (Fin m × Fin m × Bool) =>
      reim (A2 * Matrix.of ((reimE (r := m) (m := m)).symm y)) :=
    (continuous_reim.comp (continuous_const.matrix_mul hc2)).measurable
  have hpsim : Measurable (psiLp H) := (psiLp H).continuous_of_finiteDimensional.measurable
  have hcgm : Measurable (congH H hH hnH hsH B) :=
    (congH H hH hnH hsH B).continuous_of_finiteDimensional.measurable
  have hPm : Measurable (Prod.map (congH H hH hnH hsH B)
      (id : EuclideanSpace ℝ η → EuclideanSpace ℝ η)) := Measurable.prodMap hcgm measurable_id
  have hΦ2m : Measurable fun p : EuclideanSpace ℝ η × EuclideanSpace ℝ η =>
      reim (A2 * Matrix.of ((reimE (r := m) (m := m)).symm
        (psiLp H (Prod.map (congH H hH hnH hsH B) id p)))) := hmulLm.comp (hpsim.comp hPm)
  have hLc : Continuous L := L.continuous_of_finiteDimensional
  have hHc : Continuous H := H.continuous_of_finiteDimensional
  have hFc : Continuous fun z : EuclideanSpace ℝ ι × EuclideanSpace ℝ η =>
      L z.1 * w + (1 / 2 : ℂ) • (w * (wᴴ * Formalism.REAL.Jm ε * w)⁻¹ * H z.2) := by
    have h1 : Continuous fun z : EuclideanSpace ℝ ι × EuclideanSpace ℝ η => L z.1 * w :=
      (hLc.comp continuous_fst).matrix_mul continuous_const
    have h2 : Continuous fun z : EuclideanSpace ℝ ι × EuclideanSpace ℝ η =>
        w * (wᴴ * Formalism.REAL.Jm ε * w)⁻¹ * H z.2 :=
      continuous_const.matrix_mul (hHc.comp continuous_snd)
    have h3 : Continuous fun z : EuclideanSpace ℝ ι × EuclideanSpace ℝ η =>
        (1 / 2 : ℂ) • (w * (wᴴ * Formalism.REAL.Jm ε * w)⁻¹ * H z.2) := h2.const_smul (1 / 2 : ℂ)
    exact h1.add h3
  have hFm : Measurable fun z : EuclideanSpace ℝ ι × EuclideanSpace ℝ η =>
      reim (L z.1 * w + (1 / 2 : ℂ) • (w * (wᴴ * Formalism.REAL.Jm ε * w)⁻¹ * H z.2)) :=
    (continuous_reim.comp hFc).measurable
  have hrsm : Measurable (rsL S eS eU) := (rsL S eS eU).continuous_of_finiteDimensional.measurable
  have hΦm := Measurable.prodMap hΦ1m hΦ2m

  have hPre : MeasurePreserving (Prod.map Λ (id : EuclideanSpace ℝ η → EuclideanSpace ℝ η))
      (volume : Measure ((EuclideanSpace ℝ (Fin S.card × Fin m × Bool) × EuclideanSpace ℝ η) ×
        EuclideanSpace ℝ η)) (volume : Measure (EuclideanSpace ℝ ι × EuclideanSpace ℝ η)) := by
    rw [Measure.volume_eq_prod (EuclideanSpace ℝ (Fin S.card × Fin m × Bool) × EuclideanSpace ℝ η)
      (EuclideanSpace ℝ η), Measure.volume_eq_prod (EuclideanSpace ℝ ι) (EuclideanSpace ℝ η)]
    exact hΛ.prod (MeasurePreserving.id _)
  have hAssoc := measurePreserving_prodAssoc
    (volume : Measure (EuclideanSpace ℝ (Fin S.card × Fin m × Bool)))
    (volume : Measure (EuclideanSpace ℝ η)) (volume : Measure (EuclideanSpace ℝ η))
  have hfun : (fun z : EuclideanSpace ℝ ι × EuclideanSpace ℝ η =>
      reim (L z.1 * w + (1 / 2 : ℂ) • (w * (wᴴ * Formalism.REAL.Jm ε * w)⁻¹ * H z.2))) ∘ Prod.map Λ id =
      (rsL S eS eU) ∘ (Prod.map (fun y : EuclideanSpace ℝ (Fin S.card × Fin m × Bool) =>
        reim (Matrix.of ((reimE (r := S.card) (m := m)).symm y) * (r2 • W0)))
        (fun p : EuclideanSpace ℝ η × EuclideanSpace ℝ η => reim (A2 * Matrix.of
          ((reimE (r := m) (m := m)).symm (psiLp H (Prod.map (congH H hH hnH hsH B) id p))))))
        ∘ (MeasurableEquiv.prodAssoc) := by
    funext ⟨⟨z1, z2⟩, t⟩
    exact key_lemma_12 ε S eS eU w hw L H hH hnH hsH Λ hLΛ W0 Dg B A2 hW0def hDgdef hBdef hA2def hW0 hDD
      z1 z2 t
  rw [← hPre.map_eq, Measure.map_map hFm hPre.measurable, hfun,
    ← Measure.map_map hrsm (hΦm.comp MeasurableEquiv.prodAssoc.measurable),
    ← Measure.map_map hΦm MeasurableEquiv.prodAssoc.measurable,
    Measure.volume_eq_prod (EuclideanSpace ℝ (Fin S.card × Fin m × Bool) × EuclideanSpace ℝ η)
      (EuclideanSpace ℝ η),
    Measure.volume_eq_prod (EuclideanSpace ℝ (Fin S.card × Fin m × Bool)) (EuclideanSpace ℝ η),
    hAssoc.map_eq, ← Measure.map_prod_map _ _ hΦ1m hΦ2m,
    ← Measure.volume_eq_prod (EuclideanSpace ℝ η) (EuclideanSpace ℝ η),
    map_volume_reim_block_eq_of_det_ne_zero H hH hnH hsH B A2 hBdet hA2det, map_mulR (r2 • W0) hR,
    Measure.prod_smul_left, Measure.prod_smul_right, smul_smul, Measure.map_smul,
    ← Measure.volume_eq_prod (EuclideanSpace ℝ (Fin S.card × Fin m × Bool))
      (EuclideanSpace ℝ (Fin m × Fin m × Bool)), (rs_mp S eS eU).map_eq]

  congr 1
  have hN : Complex.normSq W0.det ≠ 0 := (Complex.normSq_pos.mpr hW0).ne'
  have e1 : Complex.normSq (r2 • W0).det = 1 / (2 : ℝ) ^ m * Complex.normSq W0.det := by
    rw [Matrix.det_smul, Fintype.card_fin, map_mul, map_pow]
    congr 1
    simp only [r2, Complex.normSq_ofReal]
    rw [← mul_inv, Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2), one_div, inv_pow]
  have e2 : Complex.normSq B.det = (2 : ℝ) ^ m * Complex.normSq W0.det := by
    rw [hBdef, Matrix.det_smul, Fintype.card_fin, map_mul, map_pow, Complex.normSq_ofReal,
      Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  have hdinv : Complex.normSq (W0ᴴ⁻¹).det = (Complex.normSq W0.det)⁻¹ := by
    have h1 : (W0ᴴ⁻¹).det * W0ᴴ.det = 1 := by
      rw [← Matrix.det_mul, Matrix.nonsing_inv_mul _ hWHu, Matrix.det_one]
    have h3 := congrArg Complex.normSq h1
    rw [map_mul, map_one, Matrix.det_conjTranspose, Complex.star_def, Complex.normSq_conj] at h3
    exact eq_inv_of_mul_eq_one_left h3
  have hDsq : Complex.normSq Dg.det = 1 := by
    rw [Complex.normSq_eq_norm_sq, hDnorm, one_pow]
  have h12 : Complex.normSq (1 / 2 : ℂ) = 1 / 4 := by
    rw [show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by push_cast; ring, Complex.normSq_ofReal]
    norm_num
  have e3 : Complex.normSq A2.det = (1 / 4) ^ m * (Complex.normSq W0.det)⁻¹ := by
    rw [hA2def, Matrix.det_smul, Fintype.card_fin, Matrix.det_mul, map_mul, map_mul, map_pow, hDsq,
      hdinv, h12, one_mul]
  have e4 : ‖(wᴴ * Formalism.REAL.Jm ε * w).det‖ = Complex.normSq W0.det := by
    rw [hgram, Matrix.det_mul, Matrix.det_mul, norm_mul, norm_mul, hDnorm, mul_one,
      Matrix.det_conjTranspose, norm_star, Complex.normSq_eq_norm_sq, sq]
  rw [← ENNReal.ofReal_mul (inv_nonneg.mpr (pow_nonneg (Complex.normSq_nonneg _) _)),
    ← ENNReal.ofReal_mul (inv_nonneg.mpr (pow_nonneg (Complex.normSq_nonneg _) _))]
  congr 1
  rw [e1, e2, e3, e4, show n * m = (m + S.card) * m from congrArg (· * m) hn,
    inv_pow_mul_inv_pow_eq_two_pow_div_pow _ m S.card hN]

end PI.AprimeInfW
