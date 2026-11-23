import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HighestWeightUniqueness.UnitaryOfBlockWMem

open Matrix

noncomputable section

namespace PI.HwUniqW

open PI.UpqRep

variable {k r : ℕ}

private lemma Hpk_mul_self_eq_one : Hpk k r * Hpk k r = 1 := by
  ext i j
  rw [Matrix.mul_apply, Matrix.one_apply]
  have hi := i.isLt
  have hj := j.isLt
  obtain ⟨p, hp⟩ : ∃ p : Fin (2 * r + k + 1),
      (p : ℕ) = if (i : ℕ) < r ∨ r + k < (i : ℕ) then 2 * r + k - i else i :=
    ⟨⟨if (i : ℕ) < r ∨ r + k < (i : ℕ) then 2 * r + k - i else i, by split_ifs <;> omega⟩, rfl⟩
  rw [Finset.sum_eq_single p]
  · unfold Hpk
    simp only [Fin.ext_iff]
    split_ifs at hp ⊢ <;> first | omega | (norm_num; done) | (simp; done)
  · intro l _ hl
    rw [Ne, Fin.ext_iff] at hl
    unfold Hpk
    simp only [Fin.ext_iff]
    split_ifs at hp ⊢ <;> first | omega | (simp; done) | (norm_num; done)
  · intro h
    exact absurd (Finset.mem_univ p) h

private lemma Hpk_conjTranspose_Hpk_mul_eq_one_of_mem_UH {a : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hU : a ∈ UH (Hpk k r)) : (Hpk k r * aᴴ * Hpk k r) * a = 1 := by
  have h : aᴴ * Hpk k r * a = Hpk k r := hU
  calc (Hpk k r * aᴴ * Hpk k r) * a = Hpk k r * (aᴴ * Hpk k r * a) := by simp only [Matrix.mul_assoc]
    _ = 1 := by rw [h, Hpk_mul_self_eq_one]

private lemma isUnit_det_of_mem_UH {a : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hU : a ∈ UH (Hpk k r)) : IsUnit a.det :=
  Matrix.isUnit_det_of_left_inverse (Hpk_conjTranspose_Hpk_mul_eq_one_of_mem_UH hU)

lemma inv_fix {a : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (hU : a ∈ UH (Hpk k r))
    {v : Fin (2 * r + k + 1) → ℂ} (hv : a *ᵥ v = v) : a⁻¹ *ᵥ v = v := by
  calc a⁻¹ *ᵥ v = a⁻¹ *ᵥ (a *ᵥ v) := by rw [hv]
    _ = v := by rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul a (isUnit_det_of_mem_UH hU), Matrix.one_mulVec]

lemma frame_inv_mulVec_negativeVector {z : Fin (2 * r + k + 1) → ℂ} {g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hg : IsFrameW k r z g) :
    g⁻¹ *ᵥ z = (((Real.sqrt (Tz k r z) : ℝ) : ℂ) • bvec (wI k r (Fin.last k))) := by
  obtain ⟨hU, -, hz⟩ := hg
  calc g⁻¹ *ᵥ z = g⁻¹ *ᵥ (g *ᵥ ((((Real.sqrt (Tz k r z) : ℝ) : ℂ)) • bvec (wI k r (Fin.last k)))) := by
        rw [hz]
    _ = _ := by rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul g (isUnit_det_of_mem_UH hU), Matrix.one_mulVec]

lemma fix_of_smul {m : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} {s : ℂ} (hs : s ≠ 0)
    {w : Fin (2 * r + k + 1) → ℂ} (h : m *ᵥ (s • w) = s • w) : m *ᵥ w = w := by
  rw [Matrix.mulVec_smul] at h
  exact smul_right_injective _ hs h

lemma sqrtT_ne {z : Fin (2 * r + k + 1) → ℂ} (hT : 0 < Tz k r z) :
    (((Real.sqrt (Tz k r z) : ℝ) : ℂ)) ≠ 0 := Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hT).ne'

private lemma mul_mem_UH_highest_weight_uniqueness {a b : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (ha : a ∈ UH (Hpk k r)) (hb : b ∈ UH (Hpk k r)) : a * b ∈ UH (Hpk k r) := by
  have ha' : aᴴ * Hpk k r * a = Hpk k r := ha
  have hb' : bᴴ * Hpk k r * b = Hpk k r := hb
  show (a * b)ᴴ * Hpk k r * (a * b) = Hpk k r
  calc (a * b)ᴴ * Hpk k r * (a * b) = bᴴ * (aᴴ * Hpk k r * a) * b := by
        simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = Hpk k r := by rw [ha', hb']

private lemma inv_mem_UH_highest_weight_uniqueness {a : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (ha : a ∈ UH (Hpk k r)) : a⁻¹ ∈ UH (Hpk k r) := by
  have ha' : aᴴ * Hpk k r * a = Hpk k r := ha
  show (a⁻¹)ᴴ * Hpk k r * a⁻¹ = Hpk k r
  calc (a⁻¹)ᴴ * Hpk k r * a⁻¹ = (a⁻¹)ᴴ * (aᴴ * Hpk k r * a) * a⁻¹ := by rw [ha']
    _ = (a * a⁻¹)ᴴ * Hpk k r * (a * a⁻¹) := by
        simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = Hpk k r := by
        rw [Matrix.mul_nonsing_inv a (isUnit_det_of_mem_UH ha), Matrix.conjTranspose_one, Matrix.one_mul,
          Matrix.mul_one]

lemma conj_UH {z : Fin (2 * r + k + 1) → ℂ} {g x : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hg : IsFrameW k r z g) (hx : x ∈ UWset k r z) : g⁻¹ * x * g ∈ UH (Hpk k r) := by
  obtain ⟨hxU, -, -⟩ := hx
  obtain ⟨hgU, -, -⟩ := hg
  exact mul_mem_UH_highest_weight_uniqueness (mul_mem_UH_highest_weight_uniqueness (inv_mem_UH_highest_weight_uniqueness hgU) hxU) hgU

lemma conj_fix {z : Fin (2 * r + k + 1) → ℂ} {g x : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hT : 0 < Tz k r z) (hg : IsFrameW k r z g) (hx : x ∈ UWset k r z) : FixEW k r (g⁻¹ * x * g) := by
  have hg0 := hg
  obtain ⟨hgU, hge, hgz⟩ := hg0
  obtain ⟨-, hxe, hxz⟩ := hx
  unfold FixEW
  refine ⟨fun a => ⟨?_, ?_⟩, ?_⟩
  · rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, (hge a).1, (hxe a).1, inv_fix hgU (hge a).1]
  · rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, (hge a).2, (hxe a).2, inv_fix hgU (hge a).2]
  · apply fix_of_smul (sqrtT_ne hT)
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hgz, hxz, frame_inv_mulVec_negativeVector hg]

lemma UW_eq_conj {z : Fin (2 * r + k + 1) → ℂ} {g x : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hT : 0 < Tz k r z) (hg : IsFrameW k r z g) (hx : x ∈ UWset k r z) :
    ∃ h ∈ UJset (allPos k), g⁻¹ * x * g = blockW k r h ∧ x = g * blockW k r h * g⁻¹ := by
  obtain ⟨hU, hb⟩ := fix_block (conj_UH hg hx) (conj_fix hT hg hx)
  refine ⟨_, hU, hb, ?_⟩
  rw [← hb]
  calc x = (g * g⁻¹) * x * (g * g⁻¹) := by rw [mul_inv_UH hg.1, Matrix.one_mul, Matrix.mul_one]
    _ = g * (g⁻¹ * x * g) * g⁻¹ := by simp only [Matrix.mul_assoc]

end PI.HwUniqW

end
