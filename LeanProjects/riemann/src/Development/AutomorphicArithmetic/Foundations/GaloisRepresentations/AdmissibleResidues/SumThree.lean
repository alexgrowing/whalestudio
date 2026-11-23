import Mathlib

noncomputable section

namespace UpperTheory.GalN.V

def WinC (c s : ℝ) (B : Multiset ℂ) : Prop :=
  (∀ b ∈ B, c < s * ‖b‖ ∧ ‖b‖ < s * c) ∧ ‖B.prod‖ = c ^ B.card

def Win (q : ℕ) (wt : ℝ) (B : Multiset ℂ) : Prop := WinC ((q : ℝ) ^ (wt / 2)) (Real.sqrt q) B

theorem WinC.map_mul {c s : ℝ} {B : Multiset ℂ} (h : WinC c s B) {u : ℂ} (hu : u ≠ 0) :
    WinC (‖u‖ * c) s (B.map (u * ·)) := by
  have h0 : 0 < ‖u‖ := norm_pos_iff.2 hu
  refine ⟨fun b hb => ?_, ?_⟩
  · obtain ⟨a, ha, rfl⟩ := Multiset.mem_map.1 hb
    obtain ⟨h1, h2⟩ := h.1 a ha
    rw [norm_mul]
    constructor <;> nlinarith
  · rw [Multiset.prod_map_mul, Multiset.map_const', Multiset.prod_replicate, Multiset.map_id', norm_mul, norm_pow, h.2,
      Multiset.card_map, mul_pow]

theorem WinC.map_inv {c s : ℝ} {B : Multiset ℂ} (h : WinC c s B) (hc : 0 < c) (hs : 0 < s) : WinC c⁻¹ s (B.map (·⁻¹)) := by
  obtain ⟨h1, h2⟩ := h
  refine ⟨fun x hx => ?_, ?_⟩
  · obtain ⟨b, hb, rfl⟩ := Multiset.mem_map.mp hx
    beta_reduce
    obtain ⟨l, r⟩ := h1 b hb
    have hbpos : 0 < ‖b‖ := by
      by_contra hh
      push_neg at hh
      nlinarith [norm_nonneg b]
    rw [norm_inv]
    constructor
    · rw [← sub_pos]
      have e : s * ‖b‖⁻¹ - c⁻¹ = (s * c - ‖b‖) / (‖b‖ * c) := by
        field_simp
      rw [e]
      exact div_pos (by linarith) (mul_pos hbpos hc)
    · rw [← sub_pos]
      have e : s * c⁻¹ - ‖b‖⁻¹ = (s * ‖b‖ - c) / (‖b‖ * c) := by
        field_simp
      rw [e]
      exact div_pos (by linarith) (mul_pos hbpos hc)
  · rw [Multiset.prod_map_inv, Multiset.map_id', norm_inv, h2, Multiset.card_map, inv_pow]

theorem WinC.of_pow {c s : ℝ} {B : Multiset ℂ} {f : ℕ} (hf : 1 ≤ f) (hc : 0 ≤ c) (hs : 0 ≤ s)
    (h : WinC (c ^ f) (s ^ f) (B.map (· ^ f))) : WinC c s B := by
  obtain ⟨h1, h2⟩ := h
  have hf0 : f ≠ 0 := by omega
  refine ⟨fun b hb => ?_, ?_⟩
  · have key := h1 (b ^ f) (Multiset.mem_map_of_mem (· ^ f) hb)
    rw [norm_pow, ← mul_pow, ← mul_pow] at key
    exact ⟨lt_of_pow_lt_pow_left₀ f (mul_nonneg hs (norm_nonneg b)) key.1,
      lt_of_pow_lt_pow_left₀ f (mul_nonneg hs hc) key.2⟩
  · rw [Multiset.prod_map_pow, Multiset.map_id', norm_pow, Multiset.card_map, ← pow_mul,
      mul_comm, pow_mul] at h2
    exact (pow_left_inj₀ (norm_nonneg _) (pow_nonneg hc _) hf0).mp h2

theorem WinC.exists_le {c s : ℝ} {B : Multiset ℂ} (h : WinC c s B) (hc : 0 < c) (hB : B ≠ 0) : ∃ b ∈ B, ‖b‖ ≤ c := by
  by_contra hcon
  push_neg at hcon
  have key : ∀ C : Multiset ℂ, C ≠ 0 → (∀ b ∈ C, c < ‖b‖) → c ^ C.card < ‖C.prod‖ := by
    intro C
    induction C using Multiset.induction_on with
    | empty =>
      intro h0
      exact absurd rfl h0
    | cons a C ih =>
      intro _ hC
      rw [Multiset.card_cons, Multiset.prod_cons, norm_mul, pow_succ]
      have ha := hC a (by simp)
      by_cases hC0 : C = 0
      · subst hC0
        simpa using ha
      · have hP := ih hC0 (fun b hb => hC b (Multiset.mem_cons_of_mem hb))
        have hcn : 0 < c ^ C.card := pow_pos hc _
        have hm := mul_lt_mul'' hP ha hcn.le hc.le
        linarith [mul_comm ‖C.prod‖ ‖a‖]
  have hlt := key B hB hcon
  rw [h.2] at hlt
  exact lt_irrefl _ hlt

theorem WinC.sum_le {c s : ℝ} {B : Multiset ℂ} (h : WinC c s B) (hc : 0 < c) {n : ℕ} (hn : B.card = n + 1) :
    ‖B.sum‖ ≤ n * (s * c) + c := by
  obtain ⟨b0, hb0, hle⟩ := h.exists_le hc (by
    rintro rfl
    simp at hn)
  obtain ⟨B', rfl⟩ := Multiset.exists_cons_of_mem hb0
  rw [Multiset.card_cons] at hn
  have hB' : B'.card = n := by omega
  have hsum : ‖B'.sum‖ ≤ n * (s * c) := by
    refine (norm_multiset_sum_le _).trans ?_
    have hs' := Multiset.sum_le_card_nsmul (B'.map fun x => ‖x‖) (s * c) (by
      intro x hx
      obtain ⟨b, hb, rfl⟩ := Multiset.mem_map.mp hx
      exact (h.1 b (Multiset.mem_cons_of_mem hb)).2.le)
    rw [Multiset.card_map, hB', nsmul_eq_mul] at hs'
    exact hs'
  rw [Multiset.sum_cons]
  calc ‖b0 + B'.sum‖ ≤ ‖b0‖ + ‖B'.sum‖ := norm_add_le _ _
    _ ≤ n * (s * c) + c := by linarith

theorem Win.inv {q : ℕ} (hq : 0 < q) {wt : ℝ} {B : Multiset ℂ} (h : Win q (-wt) B) : Win q wt (B.map (·⁻¹)) := by
  unfold Win at *
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq
  have e : ((q : ℝ) ^ (-wt / 2))⁻¹ = (q : ℝ) ^ (wt / 2) := by
    rw [neg_div, Real.rpow_neg hq'.le, inv_inv]
  rw [← e]
  exact h.map_inv (Real.rpow_pos_of_pos hq' _) (Real.sqrt_pos.mpr hq')

theorem Win.of_pow {p f : ℕ} (hf : 1 ≤ f) {wt : ℝ} {B : Multiset ℂ} (h : Win (p ^ f) wt (B.map (· ^ f))) : Win p wt B := by
  unfold Win at *
  have hp : (0 : ℝ) ≤ p := Nat.cast_nonneg p
  refine WinC.of_pow hf (Real.rpow_nonneg hp _) (Real.sqrt_nonneg _) ?_
  have e1 : ((p : ℝ) ^ (wt / 2)) ^ f = (((p ^ f : ℕ) : ℝ)) ^ (wt / 2) := by
    push_cast
    rw [← Real.rpow_natCast ((p : ℝ) ^ (wt / 2)), ← Real.rpow_natCast (p : ℝ) f,
      ← Real.rpow_mul hp, ← Real.rpow_mul hp, mul_comm]
  have e2 : Real.sqrt (p : ℝ) ^ f = Real.sqrt (((p ^ f : ℕ) : ℝ)) := by
    push_cast
    rw [← Real.sqrt_sq (pow_nonneg (Real.sqrt_nonneg (p : ℝ)) f), ← pow_mul, mul_comm, pow_mul,
      Real.sq_sqrt hp]
  rw [e1, e2]
  exact h

end UpperTheory.GalN.V
