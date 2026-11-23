import Formalism.PeriodIntegrals.IsLowUnitH

open Matrix

noncomputable section

namespace PI.HwUniqW

open PI.UpqRep

variable {k r : ℕ}

def piI (k r : ℕ) (i : Fin (2 * r + k + 1)) : Fin (2 * r + k + 1) :=
  if r ≤ i.val ∧ i.val ≤ r + k then i else ⟨2 * r + k - i.val, by omega⟩

def epsI (k r : ℕ) (i : Fin (2 * r + k + 1)) : ℂ := if i.val = r + k then -1 else 1

lemma piI_val (i : Fin (2 * r + k + 1)) :
    (piI k r i).val = if r ≤ i.val ∧ i.val ≤ r + k then i.val else 2 * r + k - i.val := by
  unfold piI
  split_ifs <;> rfl

lemma piI_piI (i : Fin (2 * r + k + 1)) : piI k r (piI k r i) = i := by
  apply Fin.ext
  have := i.isLt
  simp only [piI_val]
  split_ifs <;> omega

lemma epsI_piI (i : Fin (2 * r + k + 1)) : epsI k r (piI k r i) = epsI k r i := by
  have := i.isLt
  simp only [epsI, piI_val]
  split_ifs <;> first | rfl | omega

lemma epsI_mul_self (i : Fin (2 * r + k + 1)) : epsI k r i * epsI k r i = 1 := by
  unfold epsI
  split_ifs <;> norm_num

lemma star_epsI (i : Fin (2 * r + k + 1)) : star (epsI k r i) = epsI k r i := by
  unfold epsI
  split_ifs <;> simp

lemma Hpk_apply (i j : Fin (2 * r + k + 1)) :
    Hpk k r i j = if j = piI k r i then epsI k r i else 0 := by
  have hj : j = piI k r i ↔
      j.val = (if r ≤ i.val ∧ i.val ≤ r + k then i.val else 2 * r + k - i.val) := by
    rw [Fin.ext_iff, piI_val]
  have := i.isLt
  have := j.isLt
  unfold Hpk epsI
  simp only [hj, Fin.ext_iff]
  split_ifs <;> first | rfl | omega | norm_num

lemma Hpk_mul_apply (X : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (i j) :
    (Hpk k r * X) i j = epsI k r i * X (piI k r i) j := by
  rw [Matrix.mul_apply, Fintype.sum_eq_single (piI k r i)]
  · rw [Hpk_apply, if_pos rfl]
  · intro l hl
    rw [Hpk_apply, if_neg hl, zero_mul]

lemma mul_Hpk_apply (X : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (i j) :
    (X * Hpk k r) i j = X i (piI k r j) * epsI k r j := by
  rw [Matrix.mul_apply, Fintype.sum_eq_single (piI k r j)]
  · rw [Hpk_apply, if_pos (piI_piI j).symm, epsI_piI]
  · intro l hl
    rw [Hpk_apply, if_neg, mul_zero]
    intro h
    apply hl
    rw [h, piI_piI]

lemma Hpk_mulVec_apply (v : Fin (2 * r + k + 1) → ℂ) (i) :
    (Hpk k r *ᵥ v) i = epsI k r i * v (piI k r i) := by
  simp only [Matrix.mulVec, dotProduct]
  rw [Fintype.sum_eq_single (piI k r i)]
  · rw [Hpk_apply, if_pos rfl]
  · intro l hl
    rw [Hpk_apply, if_neg hl, zero_mul]

lemma Hpk_mul_self : Hpk k r * Hpk k r = 1 := by
  ext i j
  rw [Hpk_mul_apply, Hpk_apply, piI_piI, epsI_piI, Matrix.one_apply]
  by_cases h : i = j
  · subst h
    simp [epsI_mul_self]
  · simp [h, Ne.symm h]

lemma Hpk_conjTranspose : (Hpk k r)ᴴ = Hpk k r := by
  ext i j
  rw [Matrix.conjTranspose_apply, Hpk_apply, Hpk_apply]
  by_cases h : j = piI k r i
  · subst h
    rw [piI_piI, if_pos rfl, if_pos rfl, star_epsI, epsI_piI]
  · have h' : ¬ i = piI k r j := fun h' => h (by rw [h', piI_piI])
    rw [if_neg h', if_neg h, star_zero]

lemma inv_mul_UH {g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (hg : g ∈ UH (Hpk k r)) :
    (Hpk k r * gᴴ * Hpk k r) * g = 1 := by
  have h : gᴴ * (Hpk k r * g) = Hpk k r := by
    rw [← Matrix.mul_assoc]
    exact hg
  simp only [Matrix.mul_assoc]
  rw [h, Hpk_mul_self]

lemma inv_eq_UH {g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (hg : g ∈ UH (Hpk k r)) :
    g⁻¹ = Hpk k r * gᴴ * Hpk k r := Matrix.inv_eq_left_inv (inv_mul_UH hg)

lemma mul_inv_UH {g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (hg : g ∈ UH (Hpk k r)) :
    g * g⁻¹ = 1 := by
  exact Matrix.mul_nonsing_inv g (Matrix.isUnit_det_of_left_inverse (inv_mul_UH hg))

lemma inv_mul_UH' {g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (hg : g ∈ UH (Hpk k r)) :
    g⁻¹ * g = 1 := by
  rw [inv_eq_UH hg]
  exact inv_mul_UH hg

lemma one_mem_UH : (1 : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) ∈ UH (Hpk k r) := by
  show (1 : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)ᴴ * Hpk k r * 1 = Hpk k r
  simp

lemma mul_mem_UH {a b : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (ha : a ∈ UH (Hpk k r)) (hb : b ∈ UH (Hpk k r)) : a * b ∈ UH (Hpk k r) := by
  show (a * b)ᴴ * Hpk k r * (a * b) = Hpk k r
  have ha' : aᴴ * Hpk k r * a = Hpk k r := ha
  have hb' : bᴴ * Hpk k r * b = Hpk k r := hb
  rw [Matrix.conjTranspose_mul]
  calc bᴴ * aᴴ * Hpk k r * (a * b) = bᴴ * (aᴴ * Hpk k r * a) * b := by
        simp only [Matrix.mul_assoc]
    _ = Hpk k r := by rw [ha', hb']

lemma inv_mem_UH {a : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (ha : a ∈ UH (Hpk k r)) : a⁻¹ ∈ UH (Hpk k r) := by
  show (a⁻¹)ᴴ * Hpk k r * a⁻¹ = Hpk k r
  have hh : ∀ X : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ,
      Hpk k r * (Hpk k r * X) = X := fun X => by
    rw [← Matrix.mul_assoc, Hpk_mul_self, Matrix.one_mul]
  have h1 : a * (Hpk k r * aᴴ * Hpk k r) = 1 := by
    rw [← inv_eq_UH ha]
    exact mul_inv_UH ha
  have h2 : a * Hpk k r * aᴴ = Hpk k r := by
    calc a * Hpk k r * aᴴ = a * (Hpk k r * aᴴ * Hpk k r) * Hpk k r := by
          simp only [Matrix.mul_assoc, Hpk_mul_self, Matrix.mul_one]
      _ = Hpk k r := by rw [h1, Matrix.one_mul]
  have e : (a⁻¹)ᴴ = Hpk k r * a * Hpk k r := by
    rw [inv_eq_UH ha]
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Hpk_conjTranspose,
      Matrix.mul_assoc]
  rw [e, inv_eq_UH ha]
  calc Hpk k r * a * Hpk k r * Hpk k r * (Hpk k r * aᴴ * Hpk k r)
      = Hpk k r * (a * Hpk k r * aᴴ) * Hpk k r := by simp only [Matrix.mul_assoc, hh]
    _ = Hpk k r := by rw [h2, Hpk_mul_self, Matrix.one_mul]

lemma Hpk_mul_mul_Hpk_apply (X : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (i j) :
    (Hpk k r * X * Hpk k r) i j = epsI k r i * X (piI k r i) (piI k r j) * epsI k r j := by
  rw [mul_Hpk_apply, Hpk_mul_apply]

end PI.HwUniqW
