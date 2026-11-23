import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.PNTExplLocL

open Complex Classical

noncomputable section

namespace Formalism.HermitianLattices.Ext.PrimesInProgressions

open Formalism.ZeroFreeDirichlet

theorem exbox_round_abs_le (x : ℝ) (n : ℤ) (h : |x| ≤ n) : |round x| ≤ n := by
  have h1 := abs_sub_round x
  have h2 : ((|round x| : ℤ) : ℝ) < (n : ℝ) + 1 := by
    rw [Int.cast_abs]
    have h3 : |(round x : ℝ)| ≤ |x| + |x - round x| := by
      have h4 := abs_sub_abs_le_abs_sub (round x : ℝ) x
      rw [abs_sub_comm] at h4
      linarith
    linarith
  have h3 : |round x| < n + 1 := by exact_mod_cast h2
  exact Int.lt_add_one_iff.1 h3

theorem exbox_log_le {M : ℕ} (hM : 3 ≤ M) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : b ≤ a + 1) :
    Real.log ((M : ℝ) * (b + 2)) ≤ 2 * Real.log ((M : ℝ) * (a + 2)) := by
  have hM' : (3 : ℝ) ≤ M := by exact_mod_cast hM
  have h1 : 0 < (M : ℝ) * (b + 2) := by positivity
  have hX : 6 ≤ (M : ℝ) * (a + 2) := by nlinarith
  have h3 : (M : ℝ) * (b + 2) ≤ 2 * ((M : ℝ) * (a + 2)) := by nlinarith
  have h2 : (M : ℝ) * (b + 2) ≤ ((M : ℝ) * (a + 2)) ^ 2 := by nlinarith
  calc Real.log ((M : ℝ) * (b + 2)) ≤ Real.log (((M : ℝ) * (a + 2)) ^ 2) := Real.log_le_log h1 h2
    _ = 2 * Real.log ((M : ℝ) * (a + 2)) := by rw [Real.log_pow]; norm_num

theorem exbox_log_nonneg {M : ℕ} (hM : 3 ≤ M) {a : ℝ} (ha : 0 ≤ a) :
    0 ≤ Real.log ((M : ℝ) * (a + 2)) := by
  have hM' : (3 : ℝ) ≤ M := by exact_mod_cast hM
  apply Real.log_nonneg
  nlinarith

theorem exbox_sum_biUnion_le {ι : Type*} (s : Finset ι) (f : ι → Finset ℂ) (w : ℂ → ℕ) :
    ∑ x ∈ s.biUnion f, w x ≤ ∑ i ∈ s, ∑ x ∈ f i, w x := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.biUnion_insert, Finset.sum_insert ha]
    have h := Finset.sum_union_inter (s₁ := f a) (s₂ := s.biUnion f) (f := w)
    omega

theorem exbox_mem_ball {M : ℕ} [NeZero M] (χ : DirichletCharacter ℂ M) {ρ : ℂ} {u : ℝ}
    (h0 : exLF χ ρ = 0) (h1 : 9 / 10 ≤ ρ.re) (h2 : |ρ.im - u| ≤ 1 / 14) :
    ρ ∈ Metric.closedBall ((101 / 100 : ℂ) + u * I) (2 / 15) := by
  have h3 := exLF_re_lt_one χ h0
  have e : (101 / 100 : ℂ) = ((101 / 100 : ℝ) : ℂ) := by push_cast; rfl
  rw [Metric.mem_closedBall, dist_eq_norm]
  have h4 : ‖ρ - ((101 / 100 : ℂ) + u * I)‖ ^ 2 ≤ (2 / 15 : ℝ) ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, e]
    simp only [sub_re, add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self,
      add_zero, sub_im, add_im, mul_im, zero_add]
    obtain ⟨h5, h6⟩ := abs_le.1 h2
    nlinarith
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by norm_num) (by norm_num)).1 h4

theorem exbox_window {M : ℕ} [NeZero M] (χ : DirichletCharacter ℂ M) (hM : 3 ≤ M) {C0 : ℝ} (hC0 : 0 < C0)
    (D : ℝ → Finset ℂ)
    (hD : ∀ (u : ℝ) (ρ : ℂ), ρ ∈ D u ↔
      (ρ ∈ Metric.closedBall ((101 / 100 : ℂ) + u * I) (2 / 15) ∧ exLF χ ρ = 0))
    (hS : ∀ u : ℝ, ((∑ ρ ∈ D u, exOrd χ ρ : ℕ) : ℝ) ≤ C0 * Real.log ((M : ℝ) * (|u| + 2)))
    (Z : Finset ℂ) (hZ : ∀ ρ ∈ Z, exLF χ ρ = 0 ∧ 9 / 10 ≤ ρ.re) (t : ℝ) :
    ((∑ ρ ∈ Z.filter (fun ρ => |ρ.im - t| ≤ 1), exOrd χ ρ : ℕ) : ℝ) ≤
      30 * C0 * Real.log ((M : ℝ) * (|t| + 2)) := by
  have sub : Z.filter (fun ρ => |ρ.im - t| ≤ 1) ⊆
      (Finset.Icc (-7 : ℤ) 7).biUnion (fun k => D (t + (k : ℝ) / 7)) := by
    intro ρ hρ
    obtain ⟨hρZ, hρt⟩ := Finset.mem_filter.1 hρ
    obtain ⟨h0, h1⟩ := hZ ρ hρZ
    have hk : |round (7 * (ρ.im - t))| ≤ 7 := by
      apply exbox_round_abs_le
      rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 7)]
      push_cast
      linarith
    refine Finset.mem_biUnion.2 ⟨round (7 * (ρ.im - t)), Finset.mem_Icc.2 (abs_le.1 hk), ?_⟩
    refine (hD _ _).2 ⟨exbox_mem_ball χ h0 h1 ?_, h0⟩
    have h2 := abs_le.1 (abs_sub_round (7 * (ρ.im - t)))
    rw [abs_le]
    constructor <;> linarith [h2.1, h2.2]
  have h1 : (∑ ρ ∈ Z.filter (fun ρ => |ρ.im - t| ≤ 1), exOrd χ ρ) ≤
      ∑ k ∈ Finset.Icc (-7 : ℤ) 7, ∑ ρ ∈ D (t + (k : ℝ) / 7), exOrd χ ρ :=
    (Finset.sum_le_sum_of_subset sub).trans (exbox_sum_biUnion_le _ _ _)
  have h2 : ((∑ ρ ∈ Z.filter (fun ρ => |ρ.im - t| ≤ 1), exOrd χ ρ : ℕ) : ℝ) ≤
      ∑ k ∈ Finset.Icc (-7 : ℤ) 7, ((∑ ρ ∈ D (t + (k : ℝ) / 7), exOrd χ ρ : ℕ) : ℝ) := by
    have h3 : ((∑ ρ ∈ Z.filter (fun ρ => |ρ.im - t| ≤ 1), exOrd χ ρ : ℕ) : ℝ) ≤
      ((∑ k ∈ Finset.Icc (-7 : ℤ) 7, ∑ ρ ∈ D (t + (k : ℝ) / 7), exOrd χ ρ : ℕ) : ℝ) := by
      exact_mod_cast h1
    refine h3.trans (le_of_eq ?_)
    rw [Nat.cast_sum]
  have h3 : ∀ k ∈ Finset.Icc (-7 : ℤ) 7, ((∑ ρ ∈ D (t + (k : ℝ) / 7), exOrd χ ρ : ℕ) : ℝ) ≤
      2 * C0 * Real.log ((M : ℝ) * (|t| + 2)) := by
    intro k hk
    obtain ⟨hk1, hk2⟩ := Finset.mem_Icc.1 hk
    have hk1' : (-7 : ℝ) ≤ k := by exact_mod_cast hk1
    have hk2' : (k : ℝ) ≤ 7 := by exact_mod_cast hk2
    have h4 : |t + (k : ℝ) / 7| ≤ |t| + 1 := by
      refine (abs_add_le _ _).trans ?_
      have : |(k : ℝ) / 7| ≤ 1 := by rw [abs_le]; constructor <;> linarith
      linarith
    have h5 := exbox_log_le hM (abs_nonneg t) (abs_nonneg (t + (k : ℝ) / 7)) h4
    calc _ ≤ C0 * Real.log ((M : ℝ) * (|t + (k : ℝ) / 7| + 2)) := hS _
      _ ≤ C0 * (2 * Real.log ((M : ℝ) * (|t| + 2))) := mul_le_mul_of_nonneg_left h5 hC0.le
      _ = _ := by ring
  have h4 := Finset.sum_le_card_nsmul _ _ _ h3
  have h5 : (Finset.Icc (-7 : ℤ) 7).card = 15 := by simp
  rw [h5] at h4
  refine h2.trans (h4.trans (le_of_eq ?_))
  rw [nsmul_eq_mul]; push_cast; ring

theorem ex_box : ∃ C : ℝ, 0 < C ∧ ∀ (M : ℕ) [NeZero M] (χ : DirichletCharacter ℂ M) (T : ℝ), 3 ≤ M → 0 ≤ T →
    ∃ Z : Finset ℂ,
      (∀ ρ : ℂ, ρ ∈ Z ↔ (exLF χ ρ = 0 ∧ 9 / 10 ≤ ρ.re ∧ |ρ.im| ≤ T)) ∧
      (∀ t : ℝ, ((∑ ρ ∈ Z.filter (fun ρ => |ρ.im - t| ≤ 1), exOrd χ ρ : ℕ) : ℝ) ≤
        C * Real.log ((M : ℝ) * (|t| + 2))) ∧
      (Z.card : ℝ) ≤ C * (T + 1) * Real.log ((M : ℝ) * (T + 2)) := by
  obtain ⟨C0, hC0, hloc⟩ := ex_local
  refine ⟨180 * C0, by positivity, ?_⟩
  intro M _ χ T hM hT
  choose D hD hS _ using fun t : ℝ => hloc M χ t hM
  obtain ⟨N, hN⟩ : ∃ N : ℤ, N = ⌈T⌉ := ⟨_, rfl⟩
  have hTN : T ≤ N := by rw [hN]; exact Int.le_ceil T
  have hNT : (N : ℝ) < T + 1 := by rw [hN]; exact Int.ceil_lt_add_one T
  have hN0 : 0 ≤ N := by rw [hN]; exact Int.ceil_nonneg hT
  obtain ⟨Z, hZdef⟩ : ∃ Z : Finset ℂ, Z = ((Finset.Icc (-(7 * N)) (7 * N)).biUnion
      (fun k => D ((k : ℝ) / 7))).filter (fun ρ => exLF χ ρ = 0 ∧ 9 / 10 ≤ ρ.re ∧ |ρ.im| ≤ T) := ⟨_, rfl⟩
  have hZmem : ∀ ρ : ℂ, ρ ∈ Z ↔ (exLF χ ρ = 0 ∧ 9 / 10 ≤ ρ.re ∧ |ρ.im| ≤ T) := by
    intro ρ
    rw [hZdef]
    constructor
    · intro h
      exact (Finset.mem_filter.1 h).2
    · rintro ⟨h0, h1, h2⟩
      refine Finset.mem_filter.2 ⟨?_, h0, h1, h2⟩
      have hk : |round (7 * ρ.im)| ≤ 7 * N := by
        apply exbox_round_abs_le
        rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 7)]
        push_cast
        linarith
      refine Finset.mem_biUnion.2 ⟨round (7 * ρ.im), Finset.mem_Icc.2 (abs_le.1 hk), ?_⟩
      refine (hD _ _).2 ⟨exbox_mem_ball χ h0 h1 ?_, h0⟩
      have h3 := abs_le.1 (abs_sub_round (7 * ρ.im))
      rw [abs_le]
      constructor <;> linarith [h3.1, h3.2]
  have hZ' : ∀ ρ ∈ Z, exLF χ ρ = 0 ∧ 9 / 10 ≤ ρ.re :=
    fun ρ h => ⟨((hZmem ρ).1 h).1, ((hZmem ρ).1 h).2.1⟩
  have hW := exbox_window χ hM hC0 D hD hS Z hZ'
  refine ⟨Z, hZmem, ?_, ?_⟩
  · intro t
    have hL := exbox_log_nonneg hM (abs_nonneg t)
    refine (hW t).trans ?_
    have h1 : 0 ≤ C0 * Real.log ((M : ℝ) * (|t| + 2)) := mul_nonneg hC0.le hL
    nlinarith
  · have hL := exbox_log_nonneg hM hT
    have sub : Z ⊆ (Finset.Icc (-N) N).biUnion
        (fun j => Z.filter (fun ρ => |ρ.im - (j : ℝ)| ≤ 1)) := by
      intro ρ hρ
      obtain ⟨h0, h1, h2⟩ := (hZmem ρ).1 hρ
      have hk : |round ρ.im| ≤ N := exbox_round_abs_le _ _ (h2.trans hTN)
      refine Finset.mem_biUnion.2 ⟨round ρ.im, Finset.mem_Icc.2 (abs_le.1 hk), ?_⟩
      refine Finset.mem_filter.2 ⟨hρ, ?_⟩
      have h3 := abs_sub_round ρ.im
      linarith
    have h1 : Z.card ≤ ∑ ρ ∈ Z, exOrd χ ρ := by
      rw [Finset.card_eq_sum_ones]
      exact Finset.sum_le_sum (fun ρ h => exOrd_pos χ (hZ' ρ h).1)
    have h2 : Z.card ≤ ∑ j ∈ Finset.Icc (-N) N,
        ∑ ρ ∈ Z.filter (fun ρ => |ρ.im - (j : ℝ)| ≤ 1), exOrd χ ρ :=
      h1.trans ((Finset.sum_le_sum_of_subset sub).trans (exbox_sum_biUnion_le _ _ _))
    have h3 : (Z.card : ℝ) ≤ ∑ j ∈ Finset.Icc (-N) N,
        ((∑ ρ ∈ Z.filter (fun ρ => |ρ.im - (j : ℝ)| ≤ 1), exOrd χ ρ : ℕ) : ℝ) := by
      have h4 : (Z.card : ℝ) ≤ ((∑ j ∈ Finset.Icc (-N) N,
        ∑ ρ ∈ Z.filter (fun ρ => |ρ.im - (j : ℝ)| ≤ 1), exOrd χ ρ : ℕ) : ℝ) := by
        exact_mod_cast h2
      refine h4.trans (le_of_eq ?_)
      rw [Nat.cast_sum]
    have h4 : ∀ j ∈ Finset.Icc (-N) N,
        ((∑ ρ ∈ Z.filter (fun ρ => |ρ.im - (j : ℝ)| ≤ 1), exOrd χ ρ : ℕ) : ℝ) ≤
          60 * C0 * Real.log ((M : ℝ) * (T + 2)) := by
      intro j hj
      obtain ⟨hj1, hj2⟩ := Finset.mem_Icc.1 hj
      have hj1' : -(N : ℝ) ≤ j := by exact_mod_cast hj1
      have hj2' : (j : ℝ) ≤ N := by exact_mod_cast hj2
      have h5 : |(j : ℝ)| ≤ T + 1 := by
        rw [abs_le]
        constructor <;> linarith
      have h6 := exbox_log_le hM hT (abs_nonneg (j : ℝ)) h5
      calc _ ≤ 30 * C0 * Real.log ((M : ℝ) * (|(j : ℝ)| + 2)) := hW j
        _ ≤ 30 * C0 * (2 * Real.log ((M : ℝ) * (T + 2))) :=
          mul_le_mul_of_nonneg_left h6 (by positivity)
        _ = _ := by ring
    have h5 := Finset.sum_le_card_nsmul _ _ _ h4
    have hc : ((Finset.Icc (-N) N).card : ℝ) = 2 * N + 1 := by
      rw [Int.card_Icc]
      have h6 : ((N + 1 - -N).toNat : ℤ) = 2 * N + 1 := by
        rw [Int.toNat_of_nonneg (by omega)]
        ring
      exact_mod_cast h6
    rw [nsmul_eq_mul, hc] at h5
    refine h3.trans (h5.trans ?_)
    have h7 : 0 ≤ C0 * Real.log ((M : ℝ) * (T + 2)) := mul_nonneg hC0.le hL
    have h8 : (2 * (N : ℝ) + 1) ≤ 3 * (T + 1) := by linarith
    calc (2 * (N : ℝ) + 1) * (60 * C0 * Real.log ((M : ℝ) * (T + 2)))
        = (2 * (N : ℝ) + 1) * (60 * (C0 * Real.log ((M : ℝ) * (T + 2)))) := by ring
      _ ≤ (3 * (T + 1)) * (60 * (C0 * Real.log ((M : ℝ) * (T + 2)))) :=
          mul_le_mul_of_nonneg_right h8 (by positivity)
      _ = 180 * C0 * (T + 1) * Real.log ((M : ℝ) * (T + 2)) := by ring

end Formalism.HermitianLattices.Ext.PrimesInProgressions
