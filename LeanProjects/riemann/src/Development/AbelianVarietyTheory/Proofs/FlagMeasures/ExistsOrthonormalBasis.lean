import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LayerProd
import Formalism.HarderNarasimhan.ShiftInvariance

open GlobalTheory.Count Formalism.MainNotions.S Formalism.HN Formalism.REAL Matrix NumberField MeasureTheory Finset
open scoped InnerProductSpace

namespace GlobalTheory.LieONB

variable {n : ℕ}

def sg (ε : Fin n → Bool) (a : Fin n) : ℝ := if ε a then 1 else -1

lemma sg_cases (ε : Fin n → Bool) (a : Fin n) : sg ε a = 1 ∨ sg ε a = -1 := by
  unfold sg
  split_ifs <;> simp

lemma Jm_eq (ε : Fin n → Bool) : Formalism.REAL.Jm ε = Matrix.diagonal fun a => ((sg ε a : ℝ) : ℂ) := by
  ext i j
  simp only [Formalism.REAL.Jm, Matrix.diagonal_apply, sg]
  split_ifs <;> simp

private lemma inG_iff_star_signed_entries_eq_zero (ε : Fin n → Bool) (X : Matrix (Fin n) (Fin n) ℂ) :
    inG ε X ↔ ∀ i j, star (X j i) * ((sg ε j : ℝ) : ℂ) + ((sg ε i : ℝ) : ℂ) * X i j = 0 := by
  unfold Formalism.REAL.inG
  rw [Jm_eq]
  constructor
  · intro h i j
    have := congrFun (congrFun h i) j
    simpa [Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.conjTranspose_apply] using this
  · intro h
    ext i j
    simpa [Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.conjTranspose_apply] using h i j

lemma inG_iff (ε : Fin n → Bool) (X : Matrix (Fin n) (Fin n) ℂ) :
    inG ε X ↔ ∀ a b, (X b a).re = -(sg ε a * sg ε b) * (X a b).re ∧
      (X b a).im = (sg ε a * sg ε b) * (X a b).im := by
  rw [inG_iff_star_signed_entries_eq_zero]
  have key : ∀ a b, (star (X b a) * ((sg ε b : ℝ) : ℂ) + ((sg ε a : ℝ) : ℂ) * X a b = 0 ↔
      ((X b a).re = -(sg ε a * sg ε b) * (X a b).re ∧
        (X b a).im = (sg ε a * sg ε b) * (X a b).im)) := by
    intro a b
    rw [Complex.ext_iff]
    simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.star_def, Complex.conj_re, Complex.conj_im, Complex.zero_re,
      Complex.zero_im, mul_zero, zero_mul, sub_zero, add_zero]
    rcases sg_cases ε a with ha | ha <;> rcases sg_cases ε b with hb | hb <;>
      simp only [ha, hb] <;> constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith
  exact ⟨fun h a b => (key a b).1 (h a b), fun h a b => (key a b).2 (h a b)⟩

noncomputable def bas (ε : Fin n → Bool) (a b : Fin n) : Matrix (Fin n) (Fin n) ℂ :=
  Matrix.single a b ((1 + Complex.I) / 2) +
    Matrix.single b a (-((sg ε a * sg ε b : ℝ) : ℂ) * ((1 - Complex.I) / 2))

lemma bas_re (ε : Fin n → Bool) (a b p q : Fin n) :
    (bas ε a b p q).re = (if a = p ∧ b = q then 1 / 2 else 0) +
      (if b = p ∧ a = q then -(sg ε a * sg ε b) / 2 else 0) := by
  simp only [bas, Matrix.add_apply, Matrix.single_apply, Complex.add_re]
  congr 1
  · split_ifs <;> simp
  · split_ifs <;> simp [Complex.mul_re]
    ring

lemma bas_im (ε : Fin n → Bool) (a b p q : Fin n) :
    (bas ε a b p q).im = (if a = p ∧ b = q then 1 / 2 else 0) +
      (if b = p ∧ a = q then (sg ε a * sg ε b) / 2 else 0) := by
  simp only [bas, Matrix.add_apply, Matrix.single_apply, Complex.add_im]
  congr 1
  · split_ifs <;> simp
  · split_ifs <;> simp [Complex.mul_im]
    ring

lemma bas_inG (ε : Fin n → Bool) (a b : Fin n) : inG ε (bas ε a b) := by
  rw [inG_iff]
  intro p q
  simp only [bas_re, bas_im]
  by_cases hX : a = p ∧ b = q
  · rw [← hX.1, ← hX.2]
    by_cases hab : a = b
    · rw [← hab]
      rcases sg_cases ε a with ha | ha <;> simp [ha] <;> norm_num
    · have n1 : ¬(a = b ∧ b = a) := fun h => hab h.1
      have n2 : ¬(b = a ∧ a = b) := fun h => hab h.2
      rcases sg_cases ε a with ha | ha <;> rcases sg_cases ε b with hb | hb <;>
        simp [n1, n2, ha, hb] <;> norm_num
  · by_cases hY : b = p ∧ a = q
    · rw [← hY.1, ← hY.2]
      rw [← hY.1, ← hY.2] at hX
      have n1 : ¬(b = a ∧ a = b) := fun h => hX ⟨h.2, h.1⟩
      rcases sg_cases ε a with ha | ha <;> rcases sg_cases ε b with hb | hb <;>
        simp [hX, n1, ha, hb] <;> norm_num
    · have n1 : ¬(a = q ∧ b = p) := fun h => hY ⟨h.2, h.1⟩
      have n2 : ¬(b = q ∧ a = p) := fun h => hX ⟨h.2, h.1⟩
      simp [hX, hY, n1, n2]

lemma bas_type (ε : Fin n → Bool) (a b : Fin n) : inK ε (bas ε a b) ∨ inP ε (bas ε a b) := by
  have hG := bas_inG ε a b
  unfold Formalism.REAL.inK Formalism.REAL.inP
  rw [Jm_eq]
  rcases sg_cases ε a with ha | ha <;> rcases sg_cases ε b with hb | hb
  · left
    refine ⟨hG, ?_⟩
    clear hG
    ext i j
    simp only [Matrix.mul_diagonal, Matrix.diagonal_mul, bas, Matrix.add_apply,
      Matrix.single_apply]
    by_cases hX : a = i ∧ b = j
    · rw [← hX.1, ← hX.2]
      by_cases hab : a = b
      · rw [← hab]
        ring
      · have n2 : ¬(b = a ∧ a = b) := fun h => hab h.2
        simp [n2, ha, hb]
    · by_cases hY : b = i ∧ a = j
      · rw [← hY.1, ← hY.2]
        rw [← hY.1, ← hY.2] at hX
        simp [hX, ha, hb]
      · simp [hX, hY]
  · right
    refine ⟨hG, ?_⟩
    clear hG
    ext i j
    simp only [Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.neg_apply, bas, Matrix.add_apply,
      Matrix.single_apply]
    by_cases hX : a = i ∧ b = j
    · rw [← hX.1, ← hX.2]
      by_cases hab : a = b
      · rw [← hab, ha] at hb
        norm_num at hb
      · have n2 : ¬(b = a ∧ a = b) := fun h => hab h.2
        simp [n2, ha, hb]
    · by_cases hY : b = i ∧ a = j
      · rw [← hY.1, ← hY.2]
        rw [← hY.1, ← hY.2] at hX
        simp [hX, ha, hb]
      · simp [hX, hY]
  · right
    refine ⟨hG, ?_⟩
    clear hG
    ext i j
    simp only [Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.neg_apply, bas, Matrix.add_apply,
      Matrix.single_apply]
    by_cases hX : a = i ∧ b = j
    · rw [← hX.1, ← hX.2]
      by_cases hab : a = b
      · rw [← hab, ha] at hb
        norm_num at hb
      · have n2 : ¬(b = a ∧ a = b) := fun h => hab h.2
        simp [n2, ha, hb]
    · by_cases hY : b = i ∧ a = j
      · rw [← hY.1, ← hY.2]
        rw [← hY.1, ← hY.2] at hX
        simp [hX, ha, hb]
      · simp [hX, hY]
  · left
    refine ⟨hG, ?_⟩
    clear hG
    ext i j
    simp only [Matrix.mul_diagonal, Matrix.diagonal_mul, bas, Matrix.add_apply,
      Matrix.single_apply]
    by_cases hX : a = i ∧ b = j
    · rw [← hX.1, ← hX.2]
      by_cases hab : a = b
      · rw [← hab]
        ring
      · have n2 : ¬(b = a ∧ a = b) := fun h => hab h.2
        simp [n2, ha, hb]
    · by_cases hY : b = i ∧ a = j
      · rw [← hY.1, ← hY.2]
        rw [← hY.1, ← hY.2] at hX
        simp [hX, ha, hb]
      · simp [hX, hY]

lemma trace_mul_single_conj (X : Matrix (Fin n) (Fin n) ℂ) (a b : Fin n) (c : ℂ) :
    (X * (Matrix.single a b c)ᴴ).trace = X a b * star c := by
  rw [Matrix.conjTranspose_single, Matrix.trace_mul_single, op_smul_eq_mul]

private lemma re_trace_mul_bas_conjTranspose_eq (ε : Fin n → Bool) (Y : Matrix (Fin n) (Fin n) ℂ) (p q : Fin n) :
    ((Y * (bas ε p q)ᴴ).trace).re = ((Y p q).re + (Y p q).im) / 2 -
      (sg ε p * sg ε q) * ((Y q p).re - (Y q p).im) / 2 := by
  rw [bas, Matrix.conjTranspose_add, Matrix.mul_add, Matrix.trace_add, trace_mul_single_conj,
    trace_mul_single_conj]
  simp [Complex.mul_re, Complex.mul_im]
  ring

lemma coeff (ε : Fin n → Bool) {X : Matrix (Fin n) (Fin n) ℂ} (hX : inG ε X) (a b : Fin n) :
    ((X * (bas ε a b)ᴴ).trace).re = (X a b).re + (X a b).im := by
  rw [re_trace_mul_bas_conjTranspose_eq]
  obtain ⟨h1, h2⟩ := (inG_iff ε X).1 hX a b
  rw [h1, h2]
  rcases sg_cases ε a with ha | ha <;> rcases sg_cases ε b with hb | hb <;> rw [ha, hb] <;> ring

lemma ortho (ε : Fin n → Bool) (a b p q : Fin n) :
    ((bas ε a b * (bas ε p q)ᴴ).trace).re = if (a, b) = (p, q) then 1 else 0 := by
  rw [re_trace_mul_bas_conjTranspose_eq]
  simp only [bas_re, bas_im, Prod.mk.injEq]
  by_cases hX : a = p ∧ b = q
  · rw [← hX.1, ← hX.2]
    by_cases hab : a = b
    · rw [← hab]
      rcases sg_cases ε a with ha | ha <;> simp [ha] <;> norm_num
    · have n1 : ¬(a = b ∧ b = a) := fun h => hab h.1
      have n2 : ¬(b = a ∧ a = b) := fun h => hab h.2
      rcases sg_cases ε a with ha | ha <;> rcases sg_cases ε b with hb | hb <;>
        simp [n1, n2, ha, hb] <;> norm_num
  · by_cases hY : b = p ∧ a = q
    · rw [← hY.1, ← hY.2]
      rw [← hY.1, ← hY.2] at hX
      have n1 : ¬(b = a ∧ a = b) := fun h => hX ⟨h.2, h.1⟩
      rcases sg_cases ε a with ha | ha <;> rcases sg_cases ε b with hb | hb <;>
        simp [hX, n1, ha, hb] <;> norm_num
    · have n1 : ¬(a = q ∧ b = p) := fun h => hY ⟨h.2, h.1⟩
      have n2 : ¬(b = q ∧ a = p) := fun h => hX ⟨h.2, h.1⟩
      simp [hX, hY, n1, n2]

private lemma smul_add_smul_mul_mul_smul_add_smul_of_mul_eq_zero (f : Fin n × Fin n → ℂ) (i j : Fin n) :
    (∑ z : Fin n × Fin n, if z.1 = i ∧ z.2 = j then f z else 0) = f (i, j) := by
  rw [Fintype.sum_eq_single (i, j)]
  · simp
  · intro z hz
    rw [if_neg]
    exact fun h => hz (Prod.ext h.1 h.2)

private lemma mulVec_fvec_eq_sum_uMap_smul_of_mem_Nset (f : Fin n × Fin n → ℂ) (i j : Fin n) :
    (∑ z : Fin n × Fin n, if z.2 = i ∧ z.1 = j then f z else 0) = f (j, i) := by
  rw [Fintype.sum_eq_single (j, i)]
  · simp
  · intro z hz
    rw [if_neg]
    exact fun h => hz (Prod.ext h.2 h.1)

lemma expand (ε : Fin n → Bool) {X : Matrix (Fin n) (Fin n) ℂ} (hX : inG ε X) :
    X = ∑ z : Fin n × Fin n, ((((X * (bas ε z.1 z.2)ᴴ).trace).re : ℝ) : ℂ) • bas ε z.1 z.2 := by
  simp_rw [coeff ε hX]
  ext i j
  rw [Matrix.sum_apply]
  simp only [Matrix.smul_apply, bas, Matrix.add_apply, Matrix.single_apply, smul_add,
    Finset.sum_add_distrib, smul_ite, smul_zero]
  rw [smul_add_smul_mul_mul_smul_add_smul_of_mul_eq_zero, mulVec_fvec_eq_sum_uMap_smul_of_mem_Nset]
  obtain ⟨h1, h2⟩ := (inG_iff ε X).1 hX i j
  apply Complex.ext
  · simp only [smul_eq_mul, Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.add_im, Complex.mul_im, Complex.neg_re, Complex.neg_im, Complex.ofReal_mul,
      Complex.div_ofNat_re, Complex.div_ofNat_im, Complex.sub_re, Complex.sub_im, Complex.one_re,
      Complex.one_im, Complex.I_re, Complex.I_im, h1, h2]
    rcases sg_cases ε i with hi | hi <;> rcases sg_cases ε j with hj | hj <;> simp only [hi, hj] <;> ring
  · simp only [smul_eq_mul, Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.add_im, Complex.mul_im, Complex.neg_re, Complex.neg_im, Complex.ofReal_mul,
      Complex.div_ofNat_re, Complex.div_ofNat_im, Complex.sub_re, Complex.sub_im, Complex.one_re,
      Complex.one_im, Complex.I_re, Complex.I_im, h1, h2]
    rcases sg_cases ε i with hi | hi <;> rcases sg_cases ε j with hj | hj <;> simp only [hi, hj] <;> ring

theorem exists_orthonormal_basis : ∀ (n : ℕ) (ε : Fin n → Bool), ∃ E : Fin (n ^ 2) → Matrix (Fin n) (Fin n) ℂ, (∀ i, inG ε (E i) ∧ (inK ε (E i) ∨ inP ε (E i))) ∧ (∀ i j, ((E i * (E j)ᴴ).trace).re = if i = j then 1 else 0) ∧ ∀ X, inG ε X → X = ∑ i, ((((X * (E i)ᴴ).trace).re : ℝ) : ℂ) • E i := by
  intro n ε
  obtain ⟨e⟩ : Nonempty (Fin (n ^ 2) ≃ Fin n × Fin n) :=
    ⟨(finCongr (pow_two n)).trans finProdFinEquiv.symm⟩
  refine ⟨fun i => bas ε (e i).1 (e i).2, fun i => ⟨bas_inG ε _ _, bas_type ε _ _⟩,
    fun i j => ?_, fun X hX => ?_⟩
  · show ((bas ε (e i).1 (e i).2 * (bas ε (e j).1 (e j).2)ᴴ).trace).re = if i = j then 1 else 0
    rw [ortho]
    simp only [Prod.mk.eta, EmbeddingLike.apply_eq_iff_eq]
  · exact (expand ε hX).trans (Equiv.sum_comp e (fun z : Fin n × Fin n =>
      ((((X * (bas ε z.1 z.2)ᴴ).trace).re : ℝ) : ℂ) • bas ε z.1 z.2)).symm

end GlobalTheory.LieONB
