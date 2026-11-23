import Formalism.HermitianCurvature.FiniteOrderIntersectionInSmooth
import Formalism.FormalDegreeBessel.FinalG

open Matrix Formalism.FourierDecayAlt Formalism.QuantumDeterminants
open scoped ComplexConjugate

namespace Formalism.FourierDecayAlt.P

theorem slice_exponent_identity : C2.SliceExponentIdentity := by
  intro s M
  ring

theorem slice_threshold_bound : C2.SliceThresholdBound := by
  intro c c₃ A a₁ r n hc3 hc3c hn hA ha
  have hn' : (1:ℝ) ≤ n := by exact_mod_cast hn
  have hr : (0:ℝ) ≤ r := Nat.cast_nonneg r
  have hn3 : (n:ℝ) ≤ (n:ℝ) ^ 3 := by
    nlinarith [mul_nonneg (mul_nonneg (by linarith : (0:ℝ) ≤ n) (by linarith : (0:ℝ) ≤ n - 1))
      (by linarith : (0:ℝ) ≤ n + 1)]
  have h1 : (r:ℝ) * n + 1 ≤ ((r:ℝ) + 1) * A := by
    nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ r + 1) (by linarith : (0:ℝ) ≤ A - (n:ℝ) ^ 3),
      mul_nonneg (by linarith : (0:ℝ) ≤ r + 1) (by linarith : (0:ℝ) ≤ (n:ℝ) ^ 3 - n)]
  have h2 : 0 ≤ ((r:ℝ) + 1) ^ 2 := by positivity
  have h3 : 0 ≤ A := by nlinarith
  calc c₃ * ((r:ℝ) + 1) ^ 2 * ((r:ℝ) * n + 1) ≤ c₃ * ((r:ℝ) + 1) ^ 2 * (((r:ℝ) + 1) * A) :=
        mul_le_mul_of_nonneg_left h1 (mul_nonneg hc3 h2)
    _ = c₃ * ((r:ℝ) + 1) ^ 3 * A := by ring
    _ ≤ c * ((r:ℝ) + 1) ^ 3 * A :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hc3c (by positivity)) h3
    _ ≤ a₁ := ha

theorem stabilizer_block_form : C2.StabBlock := by
  intro p s h lh uh gs ls us a b hh hgs
  simp only [Matrix.fromBlocks_multiply, Matrix.one_mul, Matrix.mul_one, Matrix.zero_mul, Matrix.mul_zero,
    add_zero, zero_add]
  rw [Matrix.fromBlocks_inj]
  simp only [Matrix.mul_assoc]
  constructor
  · rintro ⟨e11, e12, e21, e22⟩
    have hb : h * b = 0 := by
      calc h * b = (lh * (h * uh)) * b := by rw [e11]
        _ = lh * (h * (uh * b)) := by simp only [Matrix.mul_assoc]
        _ = 0 := e12
    have hb0 : b = 0 := by
      calc b = h⁻¹ * (h * b) := by rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hh, Matrix.one_mul]
        _ = 0 := by rw [hb, Matrix.mul_zero]
    have ha : a * h = 0 := by
      calc a * h = a * (lh * (h * uh)) := by rw [e11]
        _ = 0 := e21
    have ha0 : a = 0 := by
      calc a = (a * h) * h⁻¹ := by rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hh, Matrix.mul_one]
        _ = 0 := by rw [ha, Matrix.zero_mul]
    subst hb0
    subst ha0
    refine ⟨rfl, rfl, e11, ?_⟩
    simpa using e22
  · rintro ⟨rfl, rfl, e1, e2⟩
    simp [e1, e2]

theorem psi_neg_conj_identity : C2.PsiNegConj := by
  intro x
  have hre : ((-2 * Complex.I) * -(starRingEnd ℂ) x).re = ((-2 * Complex.I) * x).re := by
    simp [Complex.mul_re]
  simp only [C2.psiC, cStd, hre]

theorem relevant_pair_criterion : C2.RelevantPair := by
  intro m w d hd a b hab hw x
  have hab' : a ≠ b := ne_of_lt hab
  have hw' : w a ≠ w b := ne_of_gt hw
  have hdb := hd b
  set c : ℂ := -(x * d a / d b) with hc
  have hE1P : C2.Eij (w a) (w b) c * C2.monoP w d = C2.Eij (w a) b (c * d b) := by
    ext i j
    simp only [Matrix.mul_apply, C2.Eij, C2.monoP, Matrix.of_apply]
    rw [Finset.sum_eq_single (w b)]
    · by_cases hi : i = w a <;> by_cases hj : j = b
      · subst hj; simp [hi]
      · simp [hi, hj, Equiv.apply_eq_iff_eq, Ne.symm hj]
      · simp [hi]
      · simp [hi]
    · intro l _ hl
      simp [hl]
    · simp
  have hPE2 : C2.monoP w d * C2.Eij a b x = C2.Eij (w a) b (d a * x) := by
    ext i j
    simp only [Matrix.mul_apply, C2.Eij, C2.monoP, Matrix.of_apply]
    rw [Finset.sum_eq_single a]
    · by_cases hi : i = w a <;> by_cases hj : j = b <;> simp [hi, hj]
    · intro l _ hl
      simp [hl]
    · simp
  have hEE : ∀ v : ℂ, C2.Eij (w a) b v * C2.Eij a b x = 0 := by
    intro v
    ext i j
    simp only [Matrix.mul_apply, C2.Eij, Matrix.of_apply, Matrix.zero_apply]
    refine Finset.sum_eq_zero fun l _ => ?_
    by_cases hl : l = b
    · subst hl
      simp [Ne.symm hab']
    · simp [hl]
  have hsum : C2.Eij (w a) b (c * d b) + C2.Eij (w a) b (d a * x) = 0 := by
    ext i j
    simp only [C2.Eij, Matrix.of_apply, Matrix.add_apply, Matrix.zero_apply]
    split_ifs
    · rw [hc]
      field_simp
      ring
    · ring
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_, ?_⟩
  · intro i j hij
    simp only [Matrix.add_apply, Matrix.one_apply, C2.Eij, Matrix.of_apply]
    rw [if_neg (ne_of_lt hij), if_neg]
    · simp
    · rintro ⟨rfl, rfl⟩
      exact absurd hij (not_lt.2 hw.le)
  · intro i
    simp only [Matrix.add_apply, Matrix.one_apply_eq, C2.Eij, Matrix.of_apply]
    rw [if_neg]
    · simp
    · rintro ⟨h1, h2⟩
      exact hw' (h1.symm.trans h2)
  · intro i j hij
    simp only [Matrix.add_apply, Matrix.one_apply, C2.Eij, Matrix.of_apply]
    rw [if_neg (ne_of_gt hij), if_neg]
    · simp
    · rintro ⟨rfl, rfl⟩
      exact absurd hij (not_lt.2 hab.le)
  · intro i
    simp only [Matrix.add_apply, Matrix.one_apply_eq, C2.Eij, Matrix.of_apply]
    rw [if_neg]
    · simp
    · rintro ⟨h1, h2⟩
      exact hab' (h1.symm.trans h2)
  · have e : (1 + C2.Eij (w a) (w b) c) * C2.monoP w d * (1 + C2.Eij a b x) =
        C2.monoP w d + (C2.Eij (w a) (w b) c * C2.monoP w d + C2.monoP w d * C2.Eij a b x) +
          C2.Eij (w a) (w b) c * C2.monoP w d * C2.Eij a b x := by
      noncomm_ring
    rw [e, hE1P, hPE2, hsum, hEE, add_zero, add_zero]
  · have hL : C2.simpleLow (1 + C2.Eij (w a) (w b) c) =
        if (w a).val = (w b).val + 1 then c else 0 := by
      unfold C2.simpleLow
      rw [Finset.sum_eq_single (w b)]
      · by_cases hq : (w a).val = (w b).val + 1
        · have h : (w b).val + 1 < m := hq ▸ (w a).isLt
          rw [dif_pos h, if_pos hq]
          simp [C2.Eij, Matrix.add_apply, Matrix.one_apply, Fin.ext_iff, hq]
        · rw [if_neg hq]
          split_ifs with h
          · simp [C2.Eij, Matrix.add_apply, Matrix.one_apply, Fin.ext_iff]
            omega
          · rfl
      · intro l _ hl
        have hl' : l.val ≠ _ := fun h => hl (Fin.ext h)
        split_ifs with h
        · simp [C2.Eij, Matrix.add_apply, Matrix.one_apply, Fin.ext_iff, hl']
        · rfl
      · simp
    have hU : C2.simpleUp (1 + C2.Eij a b x) = if b.val = a.val + 1 then x else 0 := by
      unfold C2.simpleUp
      rw [Finset.sum_eq_single a]
      · by_cases hq : b.val = a.val + 1
        · have h : a.val + 1 < m := hq ▸ b.isLt
          rw [dif_pos h, if_pos hq]
          simp [C2.Eij, Matrix.add_apply, Matrix.one_apply, Fin.ext_iff, hq]
        · rw [if_neg hq]
          split_ifs with h
          · simp [C2.Eij, Matrix.add_apply, Matrix.one_apply, Fin.ext_iff]
            omega
          · rfl
      · intro l _ hl
        have hl' : l.val ≠ _ := fun h => hl (Fin.ext h)
        split_ifs with h
        · simp [C2.Eij, Matrix.add_apply, Matrix.one_apply, Fin.ext_iff, hl']
        · rfl
      · simp
    rw [hL, hU, hc]
    split_ifs <;> ring

theorem relevant_trivial_case : C2.RelevantTriv := by
  intro m w d c hd hc a b hab hw
  have key : ∀ κ : ℂ, (∀ x : ℂ, C2.psiC c (κ * x) = 1) ↔ κ = 0 := by
    intro κ
    constructor
    · intro h
      by_contra hκ
      have h1 := h (1 / (c * κ))
      have hcx : c * (κ * (1 / (c * κ))) = 1 := by field_simp
      simp only [C2.psiC, hcx, Complex.one_re, Complex.ofReal_one, mul_one] at h1
      rw [Complex.exp_eq_one_iff] at h1
      obtain ⟨n, hn⟩ := h1
      have hre : (1 : ℝ) = n * (2 * Real.pi) := by
        have := congrArg Complex.im hn
        simp at this
        linarith
      have hpi := Real.pi_gt_three
      rcases lt_trichotomy n 0 with hn0 | hn0 | hn0
      · have : (n : ℝ) ≤ -1 := by exact_mod_cast Int.le_sub_one_of_lt hn0
        nlinarith
      · subst hn0
        simp at hre
      · have : (1 : ℝ) ≤ n := by exact_mod_cast hn0
        nlinarith
    · rintro rfl x
      simp [C2.psiC]
  have hA : ∀ x : ℂ, ((if b.val = a.val + 1 then x else 0) -
      (if (w a).val = (w b).val + 1 then x * d a / d b else 0)) =
      ((if b.val = a.val + 1 then (1 : ℂ) else 0) - (if (w a).val = (w b).val + 1 then d a / d b else 0)) * x := by
    intro x
    split_ifs <;> ring
  simp only [hA, key]
  have hda := hd a
  have hdb := hd b
  by_cases hP : b.val = a.val + 1 <;> by_cases hQ : (w a).val = (w b).val + 1
  · simp only [hP, hQ, if_true, iff_self, true_and, forall_const]
    rw [sub_eq_zero, eq_comm, div_eq_one_iff_eq hdb]
  all_goals simp [hP, hQ, hda, hdb]

theorem determinant_nonzero : C2.DetNonzero := by
  intro k r z z' hz hz' g hG hdet
  have hD : Dmin k r z z' g (Fin.last (r + 1)) = (Zhat k r z z' g).det := rfl
  have h1 : Complex.normSq (Dmin k r z z' g (Fin.last (r + 1))) = 0 := by
    rw [hD, hdet, map_zero]
  unfold Gf at hG
  rw [h1] at hG
  have h2 := mul_nonneg (mul_nonneg hz.2.le hz'.2.le)
    (Complex.normSq_nonneg (Dmin k r z z' g ⟨r, by omega⟩))
  linarith

theorem stabilizer_fourth_condition : C2.C1iv := by
  intro k r z z' γ hstd hpos
  have hγ : IsUnit γ.det := Formalism.QuantumDeterminants.WeylGroupFacts.isUnit_of_uh hpos.1
  have hS : ∀ {w : Fin (2 * r + k + 1) → ℂ} {s : B.Mat k r}, s ∈ Sset k r w → IsUnit s.det := by
    rintro w s ⟨h, hh, m, hm, rfl⟩
    rw [Matrix.det_mul]
    exact (Formalism.QuantumDeterminants.WeylGroupFacts.isUnit_of_uh hh.1).mul (Formalism.QuantumDeterminants.WeylGroupFacts.isUnit_of_uh hm.1)
  have key : ∀ a : B.Mat k r, IsUnit a.det → a⁻¹ * γ * (γ⁻¹ * a * γ) = γ := by
    intro a ha
    simp only [Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_left _ _ hγ,
      Matrix.nonsing_inv_mul_cancel_left _ _ ha]
  ext ⟨a, b⟩
  simp only [Set.mem_setOf_eq, Set.mem_image, Prod.mk.injEq]
  constructor
  · rintro ⟨ha, hb, he⟩
    have h1 : γ * b = a * γ := by
      have := congrArg (a * ·) he
      simpa [Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_left _ _ (hS ha)] using this
    have hb' : b = γ⁻¹ * a * γ := by
      have := congrArg (γ⁻¹ * ·) h1
      simpa [Matrix.mul_assoc, Matrix.nonsing_inv_mul_cancel_left _ _ hγ] using this
    refine ⟨a, ⟨ha, b, hb, ?_⟩, rfl, hb'.symm⟩
    rw [hb']
    simp only [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hγ, Matrix.mul_one,
      Matrix.mul_nonsing_inv_cancel_left _ _ hγ]
  · rintro ⟨g, hgH, rfl, rfl⟩
    obtain ⟨hg, s', hs', hgs⟩ := hgH
    refine ⟨hg, ?_, key g (hS hg)⟩
    have hb : γ⁻¹ * g * γ = s' := by
      rw [hgs]
      simp only [Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hγ, Matrix.mul_one,
        Matrix.nonsing_inv_mul_cancel_left _ _ hγ]
    rw [hb]
    exact hs'

end Formalism.FourierDecayAlt.P
