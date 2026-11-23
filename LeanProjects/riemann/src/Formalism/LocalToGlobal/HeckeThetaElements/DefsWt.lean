import Formalism.LocalToGlobal.HeckeThetaElements.IsHeckeElt

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Formalism.L2.Theta

namespace Formalism.L2.NTheta

def lamAt {R : Ranks} (h : HCParam R) (n : ℕ) : ℚ :=
  if hn : n < R.k - 1 then h.v ⟨n, hn⟩ else if hm : n - (R.k - 1) < R.m then -h.b ⟨n - (R.k - 1), hm⟩ else 0

def kapQ {R : Ranks} (h : HCParam R) (p q : ℕ) : Fin p ⊕ Fin q → ℚ :=
  Sum.elim (fun i => lamAt h i + (q : ℚ) / 2 - ((p : ℚ) - 1) / 2 + (i : ℚ))
    (fun c => lamAt h (p + c) - (p : ℚ) / 2 - ((q : ℚ) - 1) / 2 + (c : ℚ))

def kapW {R : Ranks} (h : HCParam R) (p q : ℕ) : Fin p ⊕ Fin q → ℤ := fun a => ⌊kapQ h p q a⌋

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

def wtOf (D : D7) (V : HSp D) (τ : D.what₂.Tau) : Fin (V.sig (tauE D τ)).1 ⊕ Fin (V.sig (tauE D τ)).2 → ℤ :=
  kapW (D.hc τ) _ _

private theorem lamAt_eq_v_of_lt {R : Ranks} (h : HCParam R) {n : ℕ} (hn : n < R.k - 1) :
    lamAt h n = h.v ⟨n, hn⟩ := by
  unfold lamAt
  rw [dif_pos hn]

private theorem lamAt_eq_neg_b_of_not_lt {R : Ranks} (h : HCParam R) {n : ℕ} (hn : ¬ n < R.k - 1)
    (hm : n - (R.k - 1) < R.m) : lamAt h n = -h.b ⟨n - (R.k - 1), hm⟩ := by
  unfold lamAt
  rw [dif_neg hn, dif_pos hm]

theorem lamAt_int {R : Ranks} (h : HCParam R) (n : ℕ) : ∃ z : ℤ, lamAt h n = z := by
  by_cases hn : n < R.k - 1
  · rw [lamAt_eq_v_of_lt h hn]
    exact h.v_int ⟨n, hn⟩
  · by_cases hm : n - (R.k - 1) < R.m
    · rw [lamAt_eq_neg_b_of_not_lt h hn hm]
      obtain ⟨z, hz⟩ := h.b_int ⟨n - (R.k - 1), hm⟩
      exact ⟨-z, by rw [hz, Int.cast_neg]⟩
    · refine ⟨0, ?_⟩
      unfold lamAt
      rw [dif_neg hn, dif_neg hm, Int.cast_zero]

private theorem b_congr {R : Ranks} (h : HCParam R) {i j : ℕ} (hi : i < R.m) (hj : j < R.m) (e : i = j) :
    h.b ⟨i, hi⟩ = h.b ⟨j, hj⟩ := by
  subst e
  rfl

private theorem u_congr {R : Ranks} (h : HCParam R) {i j : ℕ} (hi : i < R.k) (hj : j < R.k) (e : i = j) :
    h.u ⟨i, hi⟩ = h.u ⟨j, hj⟩ := by
  subst e
  rfl

theorem lamAt_lt {R : Ranks} (h : HCParam R) (n : ℕ) (hn : n + 1 < R.r) : lamAt h (n + 1) < lamAt h n := by
  have hr : R.r = R.k + R.m - 1 := rfl
  have hk5 := R.m_add_three_le_k
  have hm2 := R.two_le_m
  have hpos : (0 : ℚ) < ((R.t : ℚ) + 3) / 2 := by positivity
  by_cases h1 : n + 1 < R.k - 1
  · have h0 : n < R.k - 1 := by omega
    rw [lamAt_eq_v_of_lt h h1, lamAt_eq_v_of_lt h h0]
    have e1 : h.v ⟨n + 1, h1⟩ < h.u ⟨n + 1, by omega⟩ := h.u_gt_v ⟨n + 1, h1⟩
    have e2 : h.u ⟨n + 1, by omega⟩ < h.v ⟨n, h0⟩ := h.v_gt_u ⟨n, h0⟩
    exact lt_trans e1 e2
  · by_cases h0 : n < R.k - 1
    · have hm : n + 1 - (R.k - 1) < R.m := by omega
      have hmp : 0 < R.m := by omega
      have hkp : 0 < R.k := by omega
      rw [lamAt_eq_neg_b_of_not_lt h h1 hm, lamAt_eq_v_of_lt h h0]
      rw [b_congr h hm hmp (by omega : n + 1 - (R.k - 1) = 0)]
      have e1 : -h.b ⟨0, hmp⟩ < h.u ⟨R.k - 1, by omega⟩ := h.u_last_gt hkp hmp
      have e2 : h.u ⟨n + 1, by omega⟩ < h.v ⟨n, h0⟩ := h.v_gt_u ⟨n, h0⟩
      rw [u_congr h (by omega : n + 1 < R.k) (by omega : R.k - 1 < R.k) (by omega : n + 1 = R.k - 1)] at e2
      exact lt_trans e1 e2
    · have hm1 : n + 1 - (R.k - 1) < R.m := by omega
      have hm0 : n - (R.k - 1) < R.m := by omega
      have hj : n - (R.k - 1) + 1 < R.m := by omega
      rw [lamAt_eq_neg_b_of_not_lt h h1 hm1, lamAt_eq_neg_b_of_not_lt h h0 hm0]
      have g1 : ((R.t : ℚ) + 3) / 2 ≤ h.e ⟨n - (R.k - 1), hm0⟩ - h.b ⟨n - (R.k - 1), hm0⟩ :=
        h.gap_be ⟨n - (R.k - 1), hm0⟩
      have g2 : ((R.t : ℚ) + 3) / 2 ≤ h.b ⟨n - (R.k - 1) + 1, hj⟩ - h.e ⟨n - (R.k - 1), hm0⟩ :=
        h.gap_eb ⟨n - (R.k - 1), hm0⟩ hj
      rw [b_congr h hm1 hj (by omega : n + 1 - (R.k - 1) = n - (R.k - 1) + 1)]
      linarith

theorem lamAt_step {R : Ranks} (h : HCParam R) (n : ℕ) (hn : n + 1 < R.r) : lamAt h (n + 1) + 1 ≤ lamAt h n := by
  obtain ⟨a, ha⟩ := lamAt_int h (n + 1)
  obtain ⟨c, hc⟩ := lamAt_int h n
  have hlt := lamAt_lt h n hn
  rw [ha, hc] at hlt ⊢
  have hac : a < c := by exact_mod_cast hlt
  have hac' : a + 1 ≤ c := by omega
  exact_mod_cast hac'

theorem lamAt_add_add_le {R : Ranks} (h : HCParam R) : ∀ d n : ℕ, n + d < R.r → lamAt h (n + d) + d ≤ lamAt h n
  | 0, n, _ => by simp
  | d + 1, n, hd => by
    have h1 := lamAt_step h (n + d) (by omega)
    have h2 := lamAt_add_add_le h d n (by omega)
    rw [show n + (d + 1) = n + d + 1 by ring]
    push_cast
    linarith

theorem kapQ_int {R : Ranks} (h : HCParam R) (p q : ℕ) (hpq : Odd (p + q)) (a : Fin p ⊕ Fin q) :
    ∃ z : ℤ, kapQ h p q a = z := by
  obtain ⟨k, hk⟩ := hpq
  have hk' : (p : ℚ) + q = 2 * k + 1 := by exact_mod_cast hk
  cases a with
  | inl i =>
    obtain ⟨z, hz⟩ := lamAt_int h i
    refine ⟨z + ((k : ℤ) + 1 - p) + ((i : ℕ) : ℤ), ?_⟩
    simp only [kapQ, Sum.elim_inl]
    rw [hz]
    push_cast
    linarith
  | inr c =>
    obtain ⟨z, hz⟩ := lamAt_int h (p + c)
    refine ⟨z - k + ((c : ℕ) : ℤ), ?_⟩
    simp only [kapQ, Sum.elim_inr]
    rw [hz]
    push_cast
    linarith

theorem kapW_cast {R : Ranks} (h : HCParam R) (p q : ℕ) (hpq : Odd (p + q)) (a : Fin p ⊕ Fin q) :
    ((kapW h p q a : ℤ) : ℚ) = kapQ h p q a := by
  obtain ⟨z, hz⟩ := kapQ_int h p q hpq a
  simp only [kapW]
  rw [hz, Int.floor_intCast]

theorem holEnt_kapW {R : Ranks} (h : HCParam R) (p q : ℕ) (hpq : Odd (p + q)) (a : Fin p ⊕ Fin q) :
    holEnt p q (kapW h p q) a = Sum.elim (fun i : Fin p => lamAt h i) (fun c : Fin q => lamAt h (p + c)) a := by
  cases a with
  | inl i =>
    simp only [holEnt, Sum.elim_inl]
    rw [kapW_cast h p q hpq (Sum.inl i)]
    simp only [kapQ, Sum.elim_inl]
    ring
  | inr c =>
    simp only [holEnt, Sum.elim_inr]
    rw [kapW_cast h p q hpq (Sum.inr c)]
    simp only [kapQ, Sum.elim_inr]
    ring

theorem odd_r (R : Ranks) : Odd R.r := by
  obtain ⟨a, ha⟩ := R.k_even
  obtain ⟨c, hc⟩ := R.m_even
  have hk5 := R.m_add_three_le_k
  refine ⟨a + c - 1, ?_⟩
  show R.k + R.m - 1 = 2 * (a + c - 1) + 1
  omega

theorem holOK_kapW {R : Ranks} (h : HCParam R) (p q : ℕ) (hpq : p + q = R.r) : HolOK p q (kapW h p q) := by
  have hodd : Odd (p + q) := by
    rw [hpq]
    exact odd_r R
  refine ⟨fun i i' hii => ?_, fun c c' hcc => ?_, fun i c => ?_⟩
  · have hq : ((kapW h p q (Sum.inl i') : ℤ) : ℚ) ≤ ((kapW h p q (Sum.inl i) : ℤ) : ℚ) := by
      rw [kapW_cast h p q hodd, kapW_cast h p q hodd]
      simp only [kapQ, Sum.elim_inl]
      have hle : (i : ℕ) ≤ (i' : ℕ) := hii
      have hi' := i'.isLt
      have hm := lamAt_add_add_le h ((i' : ℕ) - i) i (by omega)
      have e : (i : ℕ) + ((i' : ℕ) - i) = i' := by omega
      rw [e] at hm
      have hc : (((i' : ℕ) - i : ℕ) : ℚ) = ((i' : ℕ) : ℚ) - ((i : ℕ) : ℚ) := by
        rw [Nat.cast_sub hle]
      rw [hc] at hm
      linarith
    exact_mod_cast hq
  · have hq : ((kapW h p q (Sum.inr c') : ℤ) : ℚ) ≤ ((kapW h p q (Sum.inr c) : ℤ) : ℚ) := by
      rw [kapW_cast h p q hodd, kapW_cast h p q hodd]
      simp only [kapQ, Sum.elim_inr]
      have hle : (c : ℕ) ≤ (c' : ℕ) := hcc
      have hc' := c'.isLt
      have hm := lamAt_add_add_le h ((c' : ℕ) - c) (p + c) (by omega)
      have e : p + (c : ℕ) + ((c' : ℕ) - c) = p + c' := by omega
      rw [e] at hm
      have hc : (((c' : ℕ) - c : ℕ) : ℚ) = ((c' : ℕ) : ℚ) - ((c : ℕ) : ℚ) := by
        rw [Nat.cast_sub hle]
      rw [hc] at hm
      linarith
    exact_mod_cast hq
  · rw [holEnt_kapW h p q hodd, holEnt_kapW h p q hodd]
    simp only [Sum.elim_inl, Sum.elim_inr]
    have hi := i.isLt
    have hc := c.isLt
    have hm := lamAt_add_add_le h (p + (c : ℕ) - i) i (by omega)
    have e : (i : ℕ) + (p + (c : ℕ) - i) = p + c := by omega
    rw [e] at hm
    have hd : (1 : ℚ) ≤ ((p + (c : ℕ) - i : ℕ) : ℚ) := by
      have h1 : 1 ≤ p + (c : ℕ) - i := by omega
      exact_mod_cast h1
    linarith

end Formalism.L2.NTheta
