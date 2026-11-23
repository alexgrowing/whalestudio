import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnimodularLocalStandard.RelIdxNeZeroOfLeLeft

noncomputable section
open scoped ComplexConjugate

namespace PI.UnitaryGroupMassFormula.UnimodLocStd
open PI.ULS

lemma stdH_apply (L : PeriodPair) (m : Type*) [Fintype m] [DecidableEq m] (x y : m → ℂ) :
    stdH L m x y = (∑ i, x i * conj (y i)) * ((area L : ℝ) : ℂ)⁻¹ := by
  simp only [PI.ULS.stdH, PI.ULS.matH, LinearMap.mk₂'ₛₗ_apply]
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_eq_single i]
  · simp only [Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one]
    ring
  · intro j _ hj
    simp only [Matrix.smul_apply, Matrix.one_apply_ne (Ne.symm hj), smul_eq_mul, mul_zero, zero_mul]
  · intro hi
    exact absurd (Finset.mem_univ i) hi

def detD (L : PeriodPair) : ℝ := (conj L.ω₁ * L.ω₂).im

private theorem detD_eq_re_mul_im_sub (L : PeriodPair) :
    detD L = L.ω₁.re * L.ω₂.im - L.ω₁.im * L.ω₂.re := by
  simp only [detD, Complex.mul_im, Complex.conj_re, Complex.conj_im]
  ring

lemma detD_ne (L : PeriodPair) : detD L ≠ 0 := by
  intro h
  have h' : L.ω₁.re * L.ω₂.im - L.ω₁.im * L.ω₂.re = 0 := by rw [← detD_eq_re_mul_im_sub]; exact h
  have hi := LinearIndependent.pair_iff.mp L.indep
  have key : ∀ s t : ℝ, s * L.ω₁.re + t * L.ω₂.re = 0 → s * L.ω₁.im + t * L.ω₂.im = 0 →
      s = 0 ∧ t = 0 := by
    intro s t h1 h2
    apply hi
    apply Complex.ext
    · simp only [Complex.add_re, Complex.smul_re, smul_eq_mul, Complex.zero_re]
      linarith
    · simp only [Complex.add_im, Complex.smul_im, smul_eq_mul, Complex.zero_im]
      linarith
  obtain ⟨e1, e2⟩ := key L.ω₂.im (-L.ω₁.im) (by linear_combination h') (by ring)
  obtain ⟨f1, f2⟩ := key L.ω₂.re (-L.ω₁.re) (by ring)
    (by linear_combination (-L.ω₂.re) * e2 + (-L.ω₁.re) * e1)
  exact one_ne_zero (key 1 0 (by linear_combination (-1 : ℝ) * f2)
    (by linear_combination (-1 : ℝ) * e2)).1

lemma area_eq (L : PeriodPair) : area L = |detD L| := rfl

lemma im_mul_conj (L : PeriodPair) (p q r s : ℝ) :
    ((p • L.ω₁ + q • L.ω₂) * conj (r • L.ω₁ + s • L.ω₂)).im = (q * r - p * s) * detD L := by
  rw [detD_eq_re_mul_im_sub]
  simp only [Complex.mul_im, Complex.add_re, Complex.add_im, Complex.smul_re,
    Complex.smul_im, Complex.conj_re, Complex.conj_im, smul_eq_mul]
  ring

lemma coords (L : PeriodPair) (z : ℂ) : ∃ s t : ℝ, z = s • L.ω₁ + t • L.ω₂ := by
  refine ⟨L.basis.repr z 0, L.basis.repr z 1, ?_⟩
  have h := L.basis.sum_repr z
  rw [Fin.sum_univ_two, L.basis_zero, L.basis_one] at h
  exact h.symm

lemma int_of_div (L : PeriodPair) {t : ℝ} {k : ℤ} (h : t * detD L / area L = k) : ∃ j : ℤ, t = j := by
  have hD := detD_ne L
  rw [area_eq] at h
  rcases abs_choice (detD L) with hA | hA
  · rw [hA, mul_div_assoc, div_self hD, mul_one] at h
    exact ⟨k, h⟩
  · rw [hA, mul_div_assoc, div_neg, div_self hD, mul_neg, mul_one] at h
    exact ⟨-k, by push_cast; linarith⟩

lemma lattice_iff (L : PeriodPair) (z : ℂ) : z ∈ L.lattice ↔ ∃ p q : ℤ, z = (p : ℝ) • L.ω₁ + (q : ℝ) • L.ω₂ := by
  rw [PeriodPair.lattice, Submodule.mem_span_pair]
  constructor
  · rintro ⟨p, q, h⟩
    refine ⟨p, q, ?_⟩
    rw [← h]
    simp [zsmul_eq_mul, Complex.real_smul]
  · rintro ⟨p, q, h⟩
    refine ⟨p, q, ?_⟩
    rw [h]
    simp [zsmul_eq_mul, Complex.real_smul]

end PI.UnitaryGroupMassFormula.UnimodLocStd
