import Mathlib

namespace GlobalTheory.SummableSeriesBounds

open PowerSeries Filter Topology

variable {C : Type} [NontriviallyNormedField C] [IsUltrametricDist C]

def bdd (C : Type) [NontriviallyNormedField C] [IsUltrametricDist C] :
    Subring (PowerSeries C) where
  carrier := {Φ | ∃ b : ℝ, ∀ n : ℕ, ‖coeff n Φ‖ ≤ b}
  mul_mem' := by
    rintro Φ Ψ ⟨a, ha⟩ ⟨b, hb⟩
    have ha0 : 0 ≤ a := (norm_nonneg _).trans (ha 0)
    have hb0 : 0 ≤ b := (norm_nonneg _).trans (hb 0)
    refine ⟨a * b, fun n => ?_⟩
    rw [coeff_mul]
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (mul_nonneg ha0 hb0) ?_
    intro p _
    rw [norm_mul]
    exact mul_le_mul (ha _) (hb _) (norm_nonneg _) ha0
  one_mem' := ⟨1, fun n => by
    rw [coeff_one]; split_ifs <;> simp⟩
  add_mem' := by
    rintro Φ Ψ ⟨a, ha⟩ ⟨b, hb⟩
    refine ⟨a + b, fun n => ?_⟩
    rw [map_add]
    exact (norm_add_le _ _).trans (add_le_add (ha n) (hb n))
  zero_mem' := ⟨0, fun n => by simp⟩
  neg_mem' := by
    rintro Φ ⟨a, ha⟩
    exact ⟨a, fun n => by simpa using ha n⟩

theorem summable_norm_mul_pow_of_bounded {π : C} (hπ : ‖π‖ < 1) {a : ℕ → C} {b : ℝ} (hb : ∀ n, ‖a n‖ ≤ b) :
    Summable fun n => ‖a n * π ^ n‖ := by
  refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun n => ?_)
    ((summable_geometric_of_lt_one (norm_nonneg π) hπ).mul_left b)
  rw [norm_mul, norm_pow]
  exact mul_le_mul_of_nonneg_right (hb n) (by positivity)

theorem summable_norm_bdd {π : C} (hπ : ‖π‖ < 1) (Φ : bdd C) :
    Summable fun n => ‖coeff n (Φ : PowerSeries C) * π ^ n‖ := by
  obtain ⟨b, hb⟩ := Φ.2
  exact summable_norm_mul_pow_of_bounded hπ hb

noncomputable def ev [CompleteSpace C] {π : C} (hπ : ‖π‖ < 1) : bdd C →+* C where
  toFun Φ := ∑' n, coeff n (Φ : PowerSeries C) * π ^ n
  map_one' := by
    rw [tsum_eq_single 0]
    · simp
    · intro n hn
      simp [coeff_one, hn]
  map_zero' := by simp
  map_add' Φ Ψ := by
    rw [← (summable_norm_bdd hπ Φ).of_norm.tsum_add (summable_norm_bdd hπ Ψ).of_norm]
    refine tsum_congr fun n => ?_
    simp [add_mul]
  map_mul' Φ Ψ := by
    rw [tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm (summable_norm_bdd hπ Φ)
      (summable_norm_bdd hπ Ψ)]
    refine tsum_congr fun n => ?_
    rw [Subring.coe_mul, coeff_mul, Finset.sum_mul]
    refine Finset.sum_congr rfl fun p hp => ?_
    have hp' : p.1 + p.2 = n := by simpa using hp
    rw [← hp', pow_add]
    ring

omit [IsUltrametricDist C] in
theorem coeff_zero_lin (π : C) (G : PowerSeries C) :
    coeff 0 ((X - PowerSeries.C π) * G) = -(π * coeff 0 G) := by
  rw [sub_mul, map_sub, coeff_C_mul]
  simp

omit [IsUltrametricDist C] in
theorem coeff_succ_lin (π : C) (G : PowerSeries C) (n : ℕ) :
    coeff (n + 1) ((X - PowerSeries.C π) * G) = coeff n G - π * coeff (n + 1) G := by
  rw [sub_mul, map_sub, coeff_C_mul, coeff_succ_X_mul]

noncomputable def lin (π : C) : bdd C :=
  ⟨X - PowerSeries.C π, ⟨1 + ‖π‖, fun n => by
    rw [map_sub]
    refine (norm_sub_le _ _).trans (add_le_add ?_ ?_)
    · rw [coeff_X]; split_ifs <;> simp
    · rw [coeff_C]; split_ifs <;> simp⟩⟩

theorem lin_ne_zero (π : C) : lin π ≠ 0 := by
  intro h
  have := congrArg (fun Φ : bdd C => coeff 1 (Φ : PowerSeries C)) h
  simp [lin, coeff_C, coeff_X] at this

theorem ev_lin [CompleteSpace C] {π : C} (hπ : ‖π‖ < 1) : ev hπ (lin π) = 0 := by
  change ∑' n, coeff n (X - PowerSeries.C π : PowerSeries C) * π ^ n = 0
  rw [tsum_eq_sum (s := Finset.range 2)]
  · simp [Finset.sum_range_succ, coeff_C, coeff_X]
  · intro n hn
    have h0 : n ≠ 0 := by rintro rfl; simp at hn
    have h1 : n ≠ 1 := by rintro rfl; simp at hn
    simp [coeff_C, coeff_X, h0, h1]

theorem lin_dvd [CompleteSpace C] {π : C} (hπ : ‖π‖ < 1) (Φ : bdd C) (h : ev hπ Φ = 0) :
    lin π ∣ Φ := by
  obtain ⟨b, hb⟩ := Φ.2
  have hs : ∀ m, Summable fun k => ‖coeff (k + m) (Φ : PowerSeries C) * π ^ k‖ :=
    fun m => summable_norm_mul_pow_of_bounded hπ (a := fun k => coeff (k + m) (Φ : PowerSeries C))
      (fun k => hb _)
  let g : ℕ → C := fun m => ∑' k, coeff (k + m) (Φ : PowerSeries C) * π ^ k
  have hg : ∀ m, g m = coeff m (Φ : PowerSeries C) + π * g (m + 1) := by
    intro m
    simp only [g]
    rw [(hs m).of_norm.tsum_eq_zero_add, ← tsum_mul_left]
    congr 1
    · simp
    · refine tsum_congr fun k => ?_
      rw [show k + 1 + m = k + (m + 1) by ring]
      ring
  have hg0 : g 0 = 0 := h
  have hgb : ∀ m, ‖g m‖ ≤ ∑' k, b * ‖π‖ ^ k := by
    intro m
    refine tsum_of_norm_bounded
      ((summable_geometric_of_lt_one (norm_nonneg π) hπ).mul_left b).hasSum fun k => ?_
    rw [norm_mul, norm_pow]
    exact mul_le_mul_of_nonneg_right (hb _) (by positivity)
  refine ⟨⟨PowerSeries.mk fun n => g (n + 1), ⟨_, fun n => by rw [coeff_mk]; exact hgb _⟩⟩, ?_⟩
  apply Subtype.ext
  change (Φ : PowerSeries C) = (X - PowerSeries.C π) * PowerSeries.mk fun n => g (n + 1)
  ext n
  cases n with
  | zero =>
    rw [coeff_zero_lin, coeff_mk]
    have := hg 0
    rw [hg0] at this
    linear_combination -this
  | succ n =>
    rw [coeff_succ_lin, coeff_mk, coeff_mk]
    linear_combination -hg (n + 1)

theorem bound_of_lin_mul {π : C} (hπ : ‖π‖ < 1) {G : PowerSeries C} {b c : ℝ}
    (hc : ∀ n, ‖coeff n G‖ ≤ c) (hb : ∀ n, ‖coeff n ((X - PowerSeries.C π) * G)‖ ≤ b) (m : ℕ) :
    ‖coeff m G‖ ≤ b := by
  have hb0 : 0 ≤ b := (norm_nonneg _).trans (hb 0)
  have key : ∀ k m, ‖coeff m G‖ ≤ max b (‖π‖ ^ k * c) := by
    intro k
    induction k with
    | zero => intro m; simpa using Or.inr (hc m)
    | succ k ih =>
      intro m
      have e : coeff m G = coeff (m + 1) ((X - PowerSeries.C π) * G) + π * coeff (m + 1) G := by
        rw [coeff_succ_lin]; ring
      rw [e]
      refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ((hb _).trans (le_max_left _ _)) ?_)
      rw [norm_mul]
      refine (mul_le_mul_of_nonneg_left (ih (m + 1)) (norm_nonneg _)).trans ?_
      rw [mul_max_of_nonneg _ _ (norm_nonneg _)]
      refine max_le_max (mul_le_of_le_one_left hb0 hπ.le) (le_of_eq (by ring))
  have ht : Tendsto (fun k : ℕ => max b (‖π‖ ^ k * c)) atTop (𝓝 (max b (0 * c))) :=
    tendsto_const_nhds.max ((tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg _) hπ).mul_const c)
  rw [zero_mul, max_eq_left hb0] at ht
  exact ge_of_tendsto' ht fun k => key k m

theorem bound_of_lin_pow_mul {π : C} (hπ : ‖π‖ < 1) {b : ℝ} (n : ℕ) (G : bdd C)
    (hb : ∀ m, ‖coeff m ((lin π ^ n * G : bdd C) : PowerSeries C)‖ ≤ b) (m : ℕ) :
    ‖coeff m (G : PowerSeries C)‖ ≤ b := by
  induction n generalizing m with
  | zero => simpa using hb m
  | succ n ih =>
    refine ih (fun j => ?_) m
    obtain ⟨c, hc⟩ := (lin π ^ n * G).2
    refine bound_of_lin_mul hπ hc (fun i => ?_) j
    have := hb i
    rwa [pow_succ', mul_assoc, Subring.coe_mul] at this

theorem decay {π : C} (hπ : ‖π‖ < 1) {b : ℝ} {G : PowerSeries C} (hb : ∀ m, ‖coeff m G‖ ≤ b)
    (n m : ℕ) : ‖coeff m ((X - PowerSeries.C π) ^ n * G)‖ ≤ ‖π‖ ^ (n - m) * b := by
  have hb0 : 0 ≤ b := (norm_nonneg _).trans (hb 0)
  induction n generalizing m with
  | zero => simpa using hb m
  | succ n ih =>
    rw [pow_succ', mul_assoc]
    cases m with
    | zero =>
      rw [coeff_zero_lin, norm_neg, norm_mul]
      refine (mul_le_mul_of_nonneg_left (ih 0) (norm_nonneg _)).trans (le_of_eq ?_)
      simp only [Nat.sub_zero]; ring
    | succ m =>
      rw [coeff_succ_lin, sub_eq_add_neg]
      refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
      · simpa using ih m
      · rw [norm_neg, norm_mul]
        refine (mul_le_mul_of_nonneg_left (ih (m + 1)) (norm_nonneg _)).trans ?_
        rw [← mul_assoc, ← pow_succ']
        refine mul_le_mul_of_nonneg_right ?_ hb0
        exact pow_le_pow_of_le_one (norm_nonneg _) hπ.le (by omega)

theorem eq_zero_of_forall_dvd {π : C} (hπ : ‖π‖ < 1) (Φ : bdd C) (h : ∀ n, lin π ^ n ∣ Φ) :
    Φ = 0 := by
  obtain ⟨b, hb⟩ := Φ.2
  apply Subtype.ext
  ext m
  have key : ∀ n, ‖coeff m (Φ : PowerSeries C)‖ ≤ ‖π‖ ^ n * b := by
    intro n
    obtain ⟨G, hG⟩ := h (n + m)
    have h1 := bound_of_lin_pow_mul hπ (n + m) G (by rw [← hG]; exact hb)
    have h2 := decay hπ h1 (n + m) m
    rw [Nat.add_sub_cancel] at h2
    rw [hG]
    exact h2
  have ht : Tendsto (fun k : ℕ => ‖π‖ ^ k * b) atTop (𝓝 (0 * b)) :=
    (tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg _) hπ).mul_const b
  rw [zero_mul] at ht
  have := ge_of_tendsto' ht key
  simpa using this

theorem main (C : Type) [NontriviallyNormedField C] [IsUltrametricDist C] [CompleteSpace C]
    (π : C) (hπ : ‖π‖ < 1) :
    ∃ (B : Subring (PowerSeries C)) (ev : B →+* C) (t : B),
      (∀ Φ : PowerSeries C, Φ ∈ B ↔ ∃ b : ℝ, ∀ n : ℕ, ‖coeff n Φ‖ ≤ b) ∧
      (∀ Φ : B, ev Φ = ∑' n : ℕ, coeff n (Φ : PowerSeries C) * π ^ n) ∧ t ≠ 0 ∧
      (∀ Φ : B, ev Φ = 0 ↔ t ∣ Φ) ∧ ∀ Φ : B, Φ ≠ 0 → ∃ n : ℕ, ¬ t ^ n ∣ Φ := by
  refine ⟨bdd C, ev hπ, lin π, fun _ => Iff.rfl, fun _ => rfl, lin_ne_zero π,
    fun Φ => ⟨lin_dvd hπ Φ, ?_⟩, fun Φ hΦ => ?_⟩
  · rintro ⟨G, rfl⟩
    rw [map_mul, ev_lin, zero_mul]
  · by_contra hc
    push_neg at hc
    exact hΦ (eq_zero_of_forall_dvd hπ Φ hc)

end GlobalTheory.SummableSeriesBounds
