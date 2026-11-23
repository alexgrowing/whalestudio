import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.MomentEntryBounds.UnitaryConeEstimates.OmG

noncomputable section

open Matrix MeasureTheory Finset
open scoped ENNReal

namespace PositivityTheory.KB.MomentRationality.Cz.Pk

variable {ι : Type} {N : ℕ}

theorem chain (t : ℕ → ℝ) {τ : ℝ} {n : ℕ} (h : ∀ k, k + 1 ≤ n → t (k + 1) ≤ t k + τ) :
    ∀ d i, i + d ≤ n → t (i + d) ≤ t i + d * τ := by
  intro d
  induction d with
  | zero => intro i _; simp
  | succ d ih =>
    intro i hi
    have h1 := ih i (by omega)
    have h2 := h (i + d) (by omega)
    rw [show i + (d + 1) = i + d + 1 by omega]
    push_cast
    linarith

theorem chain' (t : ℕ → ℝ) {τ : ℝ} (hτ : 0 ≤ τ) {n : ℕ} (h : ∀ k, k + 1 ≤ n → t (k + 1) ≤ t k + τ)
    {i j : ℕ} (hij : i ≤ j) (hj : j ≤ n) : t j ≤ t i + n * τ := by
  have h1 := chain t h (j - i) i (by omega)
  rw [show i + (j - i) = j by omega] at h1
  have hle : ((j - i : ℕ) : ℝ) ≤ n := by exact_mod_cast (by omega : j - i ≤ n)
  have h2 : ((j - i : ℕ) : ℝ) * τ ≤ n * τ := mul_le_mul_of_nonneg_right hle hτ
  linarith

theorem phi_ge (t : ℕ → ℝ) {τ : ℝ} (hτ : 0 ≤ τ) : ∀ n : ℕ, (∀ k, k + 1 ≤ n → t (k + 1) ≤ t k + τ) →
    (n : ℝ) * (t 0 - t n) - (n : ℝ) ^ 3 * τ ≤ ∑ j ∈ range (n + 1), ∑ i ∈ range j, (t i - t j) := by
  intro n
  induction n with
  | zero => intro _; simp
  | succ n ih =>
    intro h
    have h' : ∀ k, k + 1 ≤ n → t (k + 1) ≤ t k + τ := fun k hk => h k (by omega)
    have IH := ih h'
    have hb : ∀ i ∈ range n, t n - t (n + 1) - n * τ ≤ t (i + 1) - t (n + 1) := by
      intro i hi
      have h3 := chain' t hτ h' (i := i + 1) (j := n) (by simp at hi; omega) le_rfl
      linarith
    have hs := Finset.sum_le_sum hb
    simp only [sum_const, card_range, nsmul_eq_mul] at hs
    rw [sum_range_succ (fun j => ∑ i ∈ range j, (t i - t j)) (n + 1),
      sum_range_succ' (fun i => t i - t (n + 1))]
    have hx : 0 ≤ (2 * (n : ℝ) ^ 2 + 3 * n + 1) * τ := by positivity
    push_cast
    nlinarith

theorem w_le (t : ℕ → ℝ) {τ : ℝ} (hτ : 0 ≤ τ) (n : ℕ) (h : ∀ k, k + 1 ≤ n → t (k + 1) ≤ t k + τ) :
    ∑ k ∈ range n, |t k - t (k + 1)| ≤ (t 0 - t n) + 2 * n * τ := by
  have hb : ∀ k ∈ range n, |t k - t (k + 1)| ≤ (t k - t (k + 1)) + 2 * τ := by
    intro k hk
    have h1 := h k (by simp at hk; omega)
    rw [abs_le']
    constructor <;> linarith
  have h2 := Finset.sum_le_sum hb
  rw [sum_add_distrib, sum_range_sub', sum_const, card_range, nsmul_eq_mul] at h2
  linarith

theorem abs_le_A (t : ℕ → ℝ) {τ : ℝ} (hτ : 0 ≤ τ) (n : ℕ) (h : ∀ k, k + 1 ≤ n → t (k + 1) ≤ t k + τ)
    (hs : ∑ k ∈ range (n + 1), t k = 0) {i : ℕ} (hi : i ≤ n) : |t i| ≤ (t 0 - t n) + 2 * n * τ := by
  have key : ∀ a b, a ≤ b →
      |t a - t b| ≤ ∑ k ∈ range b, |t k - t (k + 1)| - ∑ k ∈ range a, |t k - t (k + 1)| := by
    intro a b hab
    induction b, hab using Nat.le_induction with
    | base => simp
    | succ b hab ih =>
      rw [sum_range_succ]
      have e : t a - t (b + 1) = (t a - t b) + (t b - t (b + 1)) := by ring
      rw [e]
      have h1 := abs_add_le (t a - t b) (t b - t (b + 1))
      linarith
  have hW : ∀ a b, a ≤ n → b ≤ n → |t a - t b| ≤ ∑ k ∈ range n, |t k - t (k + 1)| := by
    have aux : ∀ a b, a ≤ b → b ≤ n → |t a - t b| ≤ ∑ k ∈ range n, |t k - t (k + 1)| := by
      intro a b hab hb
      have h1 := key a b hab
      have h2 : 0 ≤ ∑ k ∈ range a, |t k - t (k + 1)| := sum_nonneg fun _ _ => abs_nonneg _
      have h3 : ∑ k ∈ range b, |t k - t (k + 1)| ≤ ∑ k ∈ range n, |t k - t (k + 1)| :=
        sum_le_sum_of_subset_of_nonneg (range_mono hb) (fun _ _ _ => abs_nonneg _)
      linarith
    intro a b ha hb
    rcases le_total a b with hab | hab
    · exact aux a b hab hb
    · rw [abs_sub_comm]
      exact aux b a hab ha
  have e : ∑ j ∈ range (n + 1), (t i - t j) = ((n : ℝ) + 1) * t i := by
    rw [sum_sub_distrib, hs, sum_const, card_range, nsmul_eq_mul]
    push_cast
    ring
  have b1 := abs_sum_le_sum_abs (fun j => t i - t j) (range (n + 1))
  have b2 : ∑ j ∈ range (n + 1), |t i - t j| ≤
      ∑ j ∈ range (n + 1), ∑ k ∈ range n, |t k - t (k + 1)| :=
    sum_le_sum fun j hj => hW i j hi (by simp at hj; omega)
  rw [sum_const, card_range, nsmul_eq_mul] at b2
  rw [e, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < (n : ℝ) + 1)] at b1
  push_cast at b2
  have b3 : |t i| ≤ ∑ k ∈ range n, |t k - t (k + 1)| := by
    have hpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    exact le_of_mul_le_mul_left (b1.trans b2) hpos
  exact b3.trans (w_le t hτ n h)

theorem ineqN (n : ℕ) (hn : 1 ≤ n) (T B : ℝ) (hB : B < 2 * n) : ∃ c ε : ℝ, 0 < ε ∧ ∀ t : ℕ → ℝ,
    (∀ k, k + 1 ≤ n → t (k + 1) ≤ t k + T) → ∑ k ∈ range (n + 1), t k = 0 →
    B * ∑ k ∈ range n, |t k - t (k + 1)| - 2 * ∑ j ∈ range (n + 1), ∑ i ∈ range j, (t i - t j) ≤
      c - ε * ∑ k ∈ range (n + 1), |t k| := by
  set τ := max T 0 with hτdef
  have hτ : 0 ≤ τ := le_max_right _ _
  set Bp := max B 0 with hBpdef
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hBp : Bp < 2 * n := max_lt hB (by linarith)
  have hBp0 : 0 ≤ Bp := le_max_right _ _
  have hδ : 0 < 2 * (n : ℝ) - Bp := by linarith
  refine ⟨2 * n * Bp * τ + 2 * n ^ 3 * τ + (2 * n - Bp) * (2 * n * τ), (2 * n - Bp) / (n + 1),
    div_pos hδ (by positivity), ?_⟩
  intro t ht hs
  have h : ∀ k, k + 1 ≤ n → t (k + 1) ≤ t k + τ :=
    fun k hk => (ht k hk).trans (by linarith [le_max_left T 0])
  have hW := w_le t hτ n h
  have hΦ := phi_ge t hτ n h
  have hA : ∑ k ∈ range (n + 1), |t k| ≤ ((n : ℝ) + 1) * ((t 0 - t n) + 2 * n * τ) := by
    have h1 : ∑ k ∈ range (n + 1), |t k| ≤ ∑ k ∈ range (n + 1), ((t 0 - t n) + 2 * n * τ) :=
      sum_le_sum fun k hk => abs_le_A t hτ n h hs (by simp at hk; omega)
    rw [sum_const, card_range, nsmul_eq_mul] at h1
    push_cast at h1
    exact h1
  have hW0 : 0 ≤ ∑ k ∈ range n, |t k - t (k + 1)| := sum_nonneg fun _ _ => abs_nonneg _
  have hBW : B * ∑ k ∈ range n, |t k - t (k + 1)| ≤ Bp * ((t 0 - t n) + 2 * n * τ) :=
    (mul_le_mul_of_nonneg_right (le_max_left _ _) hW0).trans (mul_le_mul_of_nonneg_left hW hBp0)
  have hε : (2 * n - Bp) / (n + 1) * ∑ k ∈ range (n + 1), |t k| ≤
      (2 * n - Bp) * ((t 0 - t n) + 2 * n * τ) := by
    have hpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    rw [div_mul_eq_mul_div, div_le_iff₀ hpos]
    calc (2 * n - Bp) * ∑ k ∈ range (n + 1), |t k|
        ≤ (2 * n - Bp) * (((n : ℝ) + 1) * ((t 0 - t n) + 2 * n * τ)) :=
          mul_le_mul_of_nonneg_left hA hδ.le
      _ = (2 * n - Bp) * ((t 0 - t n) + 2 * n * τ) * (n + 1) := by ring
  nlinarith

theorem ineq (hN : 2 ≤ N) (T B : ℝ) (hB : B < 2 * ((N : ℝ) - 1)) : ∃ c ε : ℝ, 0 < ε ∧
    ∀ s : Fin N → ℝ, ∑ i, s i = 0 → Cone T s → B * W s - 2 * Phi s ≤ c - ε * ∑ i, |s i| := by
  obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := ⟨N - 1, by omega⟩
  have hn : 1 ≤ n := by omega
  have hB' : B < 2 * (n : ℝ) := by push_cast at hB; linarith
  obtain ⟨c, ε, hε, hc⟩ := ineqN n hn T B hB'
  refine ⟨c, ε, hε, ?_⟩
  intro s hs hC
  obtain ⟨t, ht⟩ : ∃ t : ℕ → ℝ, ∀ i : Fin (n + 1), s i = t i :=
    ⟨fun k => if h : k < n + 1 then s ⟨k, h⟩ else 0, fun i => by simp [i.isLt]⟩
  unfold Cone at hC
  unfold W Phi
  have hchain : ∀ k, k + 1 ≤ n → t (k + 1) ≤ t k + T := by
    intro k hk
    have h1 := hC ⟨k, by omega⟩ ⟨k + 1, by omega⟩ rfl
    rw [ht, ht] at h1
    simpa using h1
  simp only [ht] at hs ⊢
  have hs' : ∑ k ∈ range (n + 1), t k = 0 := by
    rw [Finset.sum_range]
    exact hs
  have e1 : ∑ i : Fin (n + 1), |t i| = ∑ k ∈ range (n + 1), |t k| :=
    (Finset.sum_range fun k => |t k|).symm
  have e2 : (∑ i : Fin (n + 1), ∑ j : Fin (n + 1),
      if (j : ℕ) = (i : ℕ) + 1 then |t i - t j| else 0) = ∑ k ∈ range n, |t k - t (k + 1)| := by
    calc (∑ i : Fin (n + 1), ∑ j : Fin (n + 1), if (j : ℕ) = (i : ℕ) + 1 then |t i - t j| else 0)
        = ∑ a ∈ range (n + 1), ∑ b ∈ range (n + 1), if b = a + 1 then |t a - t b| else 0 := by
          rw [Finset.sum_range]
          refine sum_congr rfl fun i _ => ?_
          rw [Finset.sum_range]
      _ = ∑ a ∈ range (n + 1), if a < n then |t a - t (a + 1)| else 0 := by
          refine sum_congr rfl fun a _ => ?_
          rw [Finset.sum_ite_eq']
          simp
      _ = ∑ k ∈ range n, |t k - t (k + 1)| := by
          rw [Finset.sum_range_succ, if_neg (lt_irrefl n), add_zero]
          exact sum_congr rfl fun a ha => if_pos (mem_range.mp ha)
  have e3 : (∑ i : Fin (n + 1), ∑ j : Fin (n + 1), if i < j then t i - t j else 0) =
      ∑ j ∈ range (n + 1), ∑ i ∈ range j, (t i - t j) := by
    calc (∑ i : Fin (n + 1), ∑ j : Fin (n + 1), if i < j then t i - t j else 0)
        = ∑ a ∈ range (n + 1), ∑ b ∈ range (n + 1), if a < b then t a - t b else 0 := by
          rw [Finset.sum_range]
          refine sum_congr rfl fun i _ => ?_
          rw [Finset.sum_range]
          exact sum_congr rfl fun j _ => if_congr Fin.lt_iff_val_lt_val rfl rfl
      _ = ∑ b ∈ range (n + 1), ∑ a ∈ range (n + 1), if a < b then t a - t b else 0 := sum_comm
      _ = ∑ j ∈ range (n + 1), ∑ i ∈ range j, (t i - t j) := by
          refine sum_congr rfl fun b hb => ?_
          rw [← Finset.sum_filter]
          congr 1
          ext a
          simp only [mem_filter, mem_range] at hb ⊢
          omega
  rw [e1, e2, e3]
  exact hc t hchain hs'

private theorem real_exp_neg_lt_one_of_pos (ε : ℝ) (hε : 0 < ε) : Real.exp (-ε) < 1 := by
  have h := Real.exp_lt_exp.mpr (by linarith : -ε < 0)
  simpa using h

theorem summ (ε : ℝ) (hε : 0 < ε) :
    ∑' m : Fin N → ℤ, ENNReal.ofReal (Real.exp (-(ε * ∑ i, |(m i : ℝ)|))) ≠ ⊤ := by
  have hs : Summable fun k : ℤ => Real.exp (-(ε * |(k : ℝ)|)) := by
    have g : Summable fun n : ℕ => Real.exp (-ε) ^ n :=
      summable_geometric_of_lt_one (Real.exp_pos _).le (real_exp_neg_lt_one_of_pos ε hε)
    rw [summable_int_iff_summable_nat_and_neg]
    constructor
    · refine g.congr fun n => ?_
      rw [← Real.exp_nat_mul]
      congr 1
      push_cast
      rw [abs_of_nonneg (Nat.cast_nonneg n)]
      ring
    · refine g.congr fun n => ?_
      rw [← Real.exp_nat_mul]
      congr 1
      push_cast
      rw [abs_neg, abs_of_nonneg (Nat.cast_nonneg n)]
      ring
  have ha : ∑' k : ℤ, ENNReal.ofReal (Real.exp (-(ε * |(k : ℝ)|))) ≠ ⊤ := by
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun _ => (Real.exp_pos _).le) hs]
    exact ENNReal.ofReal_ne_top
  have hprod : ∀ m : Fin N → ℤ, ENNReal.ofReal (Real.exp (-(ε * ∑ i, |(m i : ℝ)|))) =
      ∏ i, ENNReal.ofReal (Real.exp (-(ε * |(m i : ℝ)|))) := by
    intro m
    have e : -(ε * ∑ i, |(m i : ℝ)|) = ∑ i, -(ε * |(m i : ℝ)|) := by
      rw [Finset.mul_sum, Finset.sum_neg_distrib]
    rw [e, Real.exp_sum, ENNReal.ofReal_prod_of_nonneg (fun _ _ => (Real.exp_pos _).le)]
  rw [ENNReal.tsum_eq_iSup_sum]
  refine ne_top_of_le_ne_top (ENNReal.pow_ne_top (n := N) ha) ?_
  refine iSup_le fun F => ?_
  classical
  let S : Finset ℤ := F.biUnion fun m => Finset.univ.image m
  have hsub : F ⊆ Fintype.piFinset fun _ : Fin N => S := by
    intro m hm
    rw [Fintype.mem_piFinset]
    intro i
    exact mem_biUnion.2 ⟨m, hm, mem_image.2 ⟨i, mem_univ _, rfl⟩⟩
  calc ∑ m ∈ F, ENNReal.ofReal (Real.exp (-(ε * ∑ i, |(m i : ℝ)|)))
      ≤ ∑ m ∈ Fintype.piFinset (fun _ : Fin N => S),
          ENNReal.ofReal (Real.exp (-(ε * ∑ i, |(m i : ℝ)|))) :=
        Finset.sum_le_sum_of_subset hsub
    _ = ∑ m ∈ Fintype.piFinset (fun _ : Fin N => S),
          ∏ i, ENNReal.ofReal (Real.exp (-(ε * |(m i : ℝ)|))) :=
        sum_congr rfl fun m _ => hprod m
    _ = ∏ _i : Fin N, ∑ k ∈ S, ENNReal.ofReal (Real.exp (-(ε * |(k : ℝ)|))) :=
        Finset.sum_prod_piFinset S (fun _ k => ENNReal.ofReal (Real.exp (-(ε * |(k : ℝ)|))))
    _ ≤ ∏ _i : Fin N, ∑' k : ℤ, ENNReal.ofReal (Real.exp (-(ε * |(k : ℝ)|))) :=
        Finset.prod_le_prod' fun _ _ => ENNReal.sum_le_tsum S
    _ = (∑' k : ℤ, ENNReal.ofReal (Real.exp (-(ε * |(k : ℝ)|)))) ^ N := by
        rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]

end PositivityTheory.KB.MomentRationality.Cz.Pk

end
