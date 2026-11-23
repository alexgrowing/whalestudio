import Formalism.LocalToGlobal.TorsionIntegrality.TorsionTranslationPowers.StatementT

open PowerSeries

noncomputable section

namespace Formalism.L2.Th1.E

namespace Power

section Alg

variable {R : Type} [CommRing R] [IsDomain R]

theorem tri_succ (φ : ℕ → R) (m : ℕ) :
    ∏ j ∈ Finset.range (m + 1), φ (j + 1) ^ (m + 1 - j) =
      (∏ j ∈ Finset.range m, φ (j + 1) ^ (m - j)) * ∏ j ∈ Finset.range (m + 1), φ (j + 1) := by
  have h1 : ∏ j ∈ Finset.range m, φ (j + 1) ^ (m - j) =
      ∏ j ∈ Finset.range (m + 1), φ (j + 1) ^ (m - j) := by
    rw [Finset.prod_range_succ]; simp
  rw [h1, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun j hj => ?_
  have hj' : j ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  rw [← pow_succ]
  congr 1
  omega

theorem ratio (g φ : ℕ → R) (k : ℕ) (hne : ∀ j, j ≤ k → g j ≠ 0)
    (hrec : ∀ j, j + 1 ≤ k → g (j + 2) * g j = φ (j + 1) * g (j + 1) ^ 2) :
    ∀ m, m ≤ k → g (m + 1) * g 0 = (∏ j ∈ Finset.range m, φ (j + 1)) * g 1 * g m := by
  intro m
  induction m with
  | zero => intro _; simp
  | succ m ih =>
    intro hm
    have h1 := ih (by omega)
    have h2 := hrec m hm
    have h3 := hne m (by omega)
    apply mul_right_cancel₀ h3
    rw [Finset.prod_range_succ]
    calc g (m + 1 + 1) * g 0 * g m = (g (m + 2) * g m) * g 0 := by ring
      _ = φ (m + 1) * g (m + 1) * (g (m + 1) * g 0) := by rw [h2]; ring
      _ = _ := by rw [h1]; ring

theorem closed (g φ : ℕ → R) (e x : R) (k : ℕ) (h0 : g 0 = e * x) (hne : ∀ j, j ≤ k → g j ≠ 0)
    (hrec : ∀ j, j + 1 ≤ k → g (j + 2) * g j = φ (j + 1) * g (j + 1) ^ 2) :
    ∀ m, m ≤ k → e ^ m * g (m + 1) * x ^ m =
      g 1 ^ (m + 1) * ∏ j ∈ Finset.range m, φ (j + 1) ^ (m - j) := by
  intro m
  induction m with
  | zero => intro _; simp
  | succ m ih =>
    intro hm
    have h1 := ih (by omega)
    have h2 := ratio g φ k hne hrec (m + 1) hm
    rw [tri_succ]
    calc e ^ (m + 1) * g (m + 1 + 1) * x ^ (m + 1)
        = e ^ m * x ^ m * (g (m + 1 + 1) * (e * x)) := by ring
      _ = (e ^ m * g (m + 1) * x ^ m) * ((∏ j ∈ Finset.range (m + 1), φ (j + 1)) * g 1) := by
          rw [← h0, h2]; ring
      _ = _ := by rw [h1]; ring

end Alg

theorem scaled_x_eq_off_origin {K : Type} [Field K] (W : WeierstrassCurve K) (P : W.toAffine.Point) (hP : P ≠ 0) :
    x2 W P = X ^ 2 * xT W P := by
  cases P with
  | zero => exact absurd rfl hP
  | some x y h => rfl

theorem sum_add {A : Type} [AddCommGroup A] [Fintype A] (M : A → ℝ) (Q : A) :
    ∑ P, M (P + Q) = ∑ P, M P :=
  Equiv.sum_comp (Equiv.addRight Q) M

theorem sum_sub {A : Type} [AddCommGroup A] [Fintype A] (M : A → ℝ) (Q : A) :
    ∑ P, M (P - Q) = ∑ P, M P :=
  Equiv.sum_comp (Equiv.subRight Q) M

theorem sum_zero {A : Type} [AddCommGroup A] [Finite A] (M₀ : A → ℝ) (Q : A) (c : ℝ)
    (h : ∀ P : A, M₀ (P + Q) + M₀ (P - Q) - 2 * M₀ P = 2 * c) : c = 0 := by
  have := Fintype.ofFinite A
  have hs : ∑ P : A, (M₀ (P + Q) + M₀ (P - Q) - 2 * M₀ P) = ∑ _P : A, 2 * c :=
    Finset.sum_congr rfl fun P _ => h P
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, sum_add, sum_sub, ← Finset.mul_sum,
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hs
  have hc : (Fintype.card A : ℝ) ≠ 0 := by
    have : 0 < Fintype.card A := Fintype.card_pos
    exact_mod_cast this.ne'
  have : (Fintype.card A : ℝ) * (2 * c) = 0 := by rw [← hs]; ring
  rcases mul_eq_zero.mp this with h' | h'
  · exact absurd h' hc
  · linarith

end Power

theorem translate_power : TransPower := by
  intro K _ _ W T _ π G hG ε h0 t k hk
  obtain ⟨hG1, hG2, hG3⟩ := hG
  have hε : ε ≠ 0 := by
    obtain ⟨ε', hn, he⟩ := hG1 0 (map_zero π)
    have h1 : coeff 1 (C ε * X : K⟦X⟧) = coeff 1 (C ε' * X : K⟦X⟧) := by rw [← h0, ← he]
    simp only [coeff_C_mul, coeff_one_X, mul_one] at h1
    intro h
    rw [← h1, h, norm_zero] at hn
    exact zero_ne_one hn
  have hX : (X : K⟦X⟧) ≠ 0 := X_ne_zero
  have hne : ∀ j, j ≤ k → G (j • t) ≠ 0 := by
    intro j hj
    rcases Nat.eq_zero_or_pos j with rfl | hpos
    · rw [zero_smul, h0]
      exact mul_ne_zero (by simpa using hε) hX
    · intro h
      apply hG2 (j • t) (hk j hpos hj)
      rw [h, map_zero]
  have hrec : ∀ j, j + 1 ≤ k → G ((j + 2) • t) * G (j • t) =
      (C (constantCoeff (G t) ^ 2) * (C (px W (π t)) - xT W (π ((j + 1) • t)))) *
        G ((j + 1) • t) ^ 2 := by
    intro j hj
    have ht : π t ≠ 0 := by
      have := hk 1 le_rfl (by omega)
      rwa [one_smul] at this
    have h := hG3 ((j + 1) • t) t ht
    rw [Power.scaled_x_eq_off_origin W _ (hk (j + 1) (by omega) hj)] at h
    have e1 : (j + 1) • t + t = (j + 2) • t := by rw [← succ_nsmul]
    have e2 : (j + 1) • t - t = j • t := by rw [succ_nsmul]; abel
    rw [e1, e2] at h
    apply mul_left_cancel₀ (pow_ne_zero 2 hX)
    rw [h]; ring
  have h := Power.closed (fun j => G (j • t))
    (fun j => C (constantCoeff (G t) ^ 2) * (C (px W (π t)) - xT W (π (j • t)))) (C ε) X k
    (by simpa using h0) hne hrec k le_rfl
  simpa using h

theorem parallelogram_sum : ParSum := by
  intro A _ _ M h Q hQ
  exact Power.sum_zero M Q (M Q) fun P => h P Q hQ

theorem parallelogram_sum_two : ParSumTwo := by
  intro A _ _ M₀ m h
  have hm : ∀ Q : A, Q ≠ 0 → m Q = 0 := fun Q hQ => Power.sum_zero M₀ Q (m Q) fun P => h P Q hQ
  refine ⟨hm, ?_⟩
  have hpar : ∀ P Q : A, M₀ (P + Q) + M₀ (P - Q) = 2 * M₀ P := by
    intro P Q
    by_cases hQ : Q = 0
    · subst hQ; simp; ring
    · have := h P Q hQ
      rw [hm Q hQ] at this
      linarith
  have := Fintype.ofFinite A
  obtain ⟨P₀, -, hmax⟩ := Finset.exists_max_image (Finset.univ : Finset A) M₀ ⟨0, Finset.mem_univ 0⟩
  have hconst : ∀ R : A, M₀ R = M₀ P₀ := by
    intro R
    have h1 := hpar P₀ (R - P₀)
    have h2 := hmax (P₀ + (R - P₀)) (Finset.mem_univ _)
    have h3 := hmax (P₀ - (R - P₀)) (Finset.mem_univ _)
    have e : P₀ + (R - P₀) = R := by abel
    rw [e] at h1 h2
    linarith
  intro P
  rw [hconst P, hconst 0]

end Formalism.L2.Th1.E
