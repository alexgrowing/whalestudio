import Formalism.LocalToGlobal.HermitianForms.FormsTied

namespace Formalism.L2.Forms
open Formalism.BasicNotions

def uN {R : Ranks} (h : HCParam R) (j : ℕ) : ℚ := if hj : j < R.k then h.u ⟨j, hj⟩ else 0
def vN {R : Ranks} (h : HCParam R) (j : ℕ) : ℚ := if hj : j < R.k - 1 then h.v ⟨j, hj⟩ else 0
def bN {R : Ranks} (h : HCParam R) (j : ℕ) : ℚ := if hj : j < R.m then h.b ⟨j, hj⟩ else 0
def eN {R : Ranks} (h : HCParam R) (j : ℕ) : ℚ := if hj : j < R.m then h.e ⟨j, hj⟩ else 0

theorem uN_eq {R : Ranks} (h : HCParam R) (j : ℕ) (hj : j < R.k) : h.u ⟨j, hj⟩ = uN h j := by simp [uN, hj]
theorem vN_eq {R : Ranks} (h : HCParam R) (j : ℕ) (hj : j < R.k - 1) : h.v ⟨j, hj⟩ = vN h j := by simp [vN, hj]
theorem bN_eq {R : Ranks} (h : HCParam R) (j : ℕ) (hj : j < R.m) : h.b ⟨j, hj⟩ = bN h j := by simp [bN, hj]
theorem eN_eq {R : Ranks} (h : HCParam R) (j : ℕ) (hj : j < R.m) : h.e ⟨j, hj⟩ = eN h j := by simp [eN, hj]

def lamQ (R : Ranks) (h : HCParam R) (n : ℕ) : ℚ :=
  if n < R.k then uN h n - (((R.k : ℚ) - 1) / 2 - n)
  else -wG R (eN h ((n - R.k) / (R.t + 1))) ((n - R.k) / (R.t + 1) + 1)

def sgQ (R : Ranks) (h : HCParam R) (n : ℕ) : ℚ :=
  ((R.m : ℚ) * ((R.t : ℚ) + 1)) / 2 +
  (if n < R.k - 1 then vN h n
   else if (n - (R.k - 1)) % (R.t + 1) = 0 then -bN h ((n - (R.k - 1)) / (R.t + 1))
     else -eN h ((n - (R.k - 1)) / (R.t + 1)) + ((R.t : ℚ) - 1) / 2 - ((((n - (R.k - 1)) % (R.t + 1) : ℕ) : ℚ) - 1))
  - (((R.k : ℚ) + (R.m : ℚ) * ((R.t : ℚ) + 1) - 2) / 2 - n)

theorem half_gap (a b : ℚ) (ha : ∃ z : ℤ, a = z + 1 / 2) (hb : ∃ z : ℤ, b = z) (hab : b < a) : b + 1 / 2 ≤ a := by
  obtain ⟨z, rfl⟩ := ha
  obtain ⟨z', rfl⟩ := hb
  have : z' ≤ z := by
    by_contra hc
    have h1 : z + 1 ≤ z' := by omega
    have h2 : ((z : ℚ) + 1) ≤ z' := by exact_mod_cast h1
    linarith
  have h2 : (z' : ℚ) ≤ z := by exact_mod_cast this
  linarith

theorem half_gap' (a b : ℚ) (ha : ∃ z : ℤ, a = z + 1 / 2) (hb : ∃ z : ℤ, b = z) (hab : a < b) : a + 1 / 2 ≤ b := by
  obtain ⟨z, rfl⟩ := ha
  obtain ⟨z', rfl⟩ := hb
  have : z + 1 ≤ z' := by
    by_contra hc
    have h1 : z' ≤ z := by omega
    have h2 : (z' : ℚ) ≤ z := by exact_mod_cast h1
    linarith
  have h2 : ((z : ℚ) + 1) ≤ z' := by exact_mod_cast this
  linarith

theorem interlaceQ (R : Ranks) (h : HCParam R) (n : ℕ) (hn : n < R.N R.m - 1) :
    sgQ R h n ≤ lamQ R h n ∧ lamQ R h (n + 1) ≤ sgQ R h n := by
  have hk := R.m_add_three_le_k
  have hm := R.two_le_m
  unfold Ranks.N at hn
  by_cases h1 : n < R.k - 1
  · have hnk : n < R.k := by omega
    have hnk1 : n + 1 < R.k := by omega
    have g1 := half_gap _ _ (h.u_half ⟨n, hnk⟩) (h.v_int ⟨n, h1⟩) (h.u_gt_v ⟨n, h1⟩)
    have g2 := half_gap' _ _ (h.u_half ⟨n + 1, hnk1⟩) (h.v_int ⟨n, h1⟩) (h.v_gt_u ⟨n, h1⟩)
    rw [uN_eq, vN_eq] at g1 g2
    simp only [sgQ, lamQ, if_pos h1, if_pos hnk, if_pos hnk1]
    push_cast
    constructor <;> linarith
  · obtain ⟨a, ha⟩ : ∃ a, n = R.k - 1 + a := ⟨n - (R.k - 1), by omega⟩
    have ha' : n - (R.k - 1) = a := by omega
    have hq : a / (R.t + 1) < R.m := by
      apply Nat.div_lt_of_lt_mul
      rw [Nat.mul_comm]; omega
    have hdm := Nat.div_add_mod a (R.t + 1)
    have hr := Nat.mod_lt a (Nat.succ_pos R.t)
    set q := a / (R.t + 1) with hqd
    set ρ := a % (R.t + 1) with hρd
    have hnQ : (n : ℚ) = (R.k : ℚ) - 1 + ((R.t : ℚ) + 1) * q + ρ := by
      have : n + 1 = R.k + ((R.t + 1) * q + ρ) := by omega
      have h2 : ((n + 1 : ℕ) : ℚ) = ((R.k + ((R.t + 1) * q + ρ) : ℕ) : ℚ) := by rw [this]
      push_cast at h2; linarith
    have hn1 : ¬ (n + 1 < R.k) := by omega
    have hi1 : (n + 1 - R.k) / (R.t + 1) = q := by
      have : n + 1 - R.k = a := by omega
      rw [this]
    have gbe := h.gap_be ⟨q, hq⟩
    rw [eN_eq, bN_eq] at gbe
    simp only [sgQ, lamQ, if_neg h1, if_neg hn1, ha', hi1, wG, ← hqd, ← hρd]
    by_cases hρ : ρ = 0
    · simp only [if_pos hρ]
      rw [hρ] at hnQ
      by_cases hq0 : q = 0
      · have hnk : n < R.k := by
          have : a = 0 := by rw [← hdm, hρ, hq0]; simp
          omega
        have hnk' : n = R.k - 1 := by omega
        have g0 := h.u_last_gt (by omega) (by omega)
        have g1 := half_gap _ _ (h.u_half ⟨R.k - 1, by omega⟩) (by
          obtain ⟨z, hz⟩ := h.b_int ⟨0, by omega⟩
          exact ⟨-z, by rw [hz]; push_cast; ring⟩) g0
        rw [uN_eq, bN_eq] at g1
        simp only [if_pos hnk]
        rw [hq0] at hnQ gbe ⊢
        rw [hnk']
        rw [hnk'] at hnQ
        push_cast at hnQ ⊢
        constructor <;> linarith
      · have hnk : ¬ n < R.k := by
          have : 0 < q := Nat.pos_of_ne_zero hq0
          have : R.t + 1 ≤ (R.t + 1) * q := Nat.le_mul_of_pos_right _ this
          omega
        obtain ⟨q', hq'⟩ : ∃ q', q = q' + 1 := Nat.exists_eq_succ_of_ne_zero hq0
        have hi0 : (n - R.k) / (R.t + 1) = q' := by
          have : n - R.k = (R.t + 1) * q' + R.t := by
            have h3 : a = (R.t + 1) * (q' + 1) := by rw [← hdm, hρ, hq']; simp
            rw [Nat.mul_add] at h3
            omega
          rw [this, Nat.mul_add_div (Nat.succ_pos _)]
          rw [Nat.div_eq_of_lt (Nat.lt_succ_self _)]; simp
        have geb := h.gap_eb ⟨q', by omega⟩ (by show q' + 1 < R.m; omega)
        rw [eN_eq] at geb
        have geb' : ((R.t : ℚ) + 3) / 2 ≤ bN h (q' + 1) - eN h q' := by
          rw [← bN_eq h (q' + 1) (by omega)]; exact geb
        simp only [if_neg hnk, hi0]
        rw [hq'] at hnQ gbe ⊢
        push_cast at hnQ ⊢
        constructor <;> nlinarith
    · simp only [if_neg hρ]
      have hnk : ¬ n < R.k := by omega
      have hi0 : (n - R.k) / (R.t + 1) = q := by
        obtain ⟨ρ', hρ'⟩ : ∃ ρ', ρ = ρ' + 1 := Nat.exists_eq_succ_of_ne_zero hρ
        have : n - R.k = (R.t + 1) * q + ρ' := by omega
        rw [this, Nat.mul_add_div (Nat.succ_pos _)]
        rw [Nat.div_eq_of_lt (by omega)]; simp
      simp only [if_neg hnk, hi0]
      push_cast
      constructor <;> nlinarith

theorem sg_interlace {D : D7} {u : D.what₂.Word} {K : ClsPTied u} (W : ValPTied u K) :
    (D.fm u).SgInterlace := by
  intro τ i
  have hi := i.2
  have key := interlaceQ D.R (D.hcW u τ) i.1 hi
  have hN : (((D.R.N D.R.m - 1 : ℕ)) : ℚ) = (D.R.k : ℚ) + (D.R.m : ℚ) * ((D.R.t : ℚ) + 1) - 1 := by
    rw [Nat.cast_sub (D.R.N_pos D.R.m)]; unfold Ranks.N; push_cast; ring
  have hs : (((D.fm u).sg τ).w i : ℚ) = sgQ D.R (D.hcW u τ) i.1 := by
    rw [W.sg τ i]
    unfold sgHC sgQ rhoVec
    rw [hN]
    by_cases h1 : i.1 < D.R.k - 1
    · simp only [dif_pos h1, if_pos h1, vN_eq]; ring
    · have h2 : (i.1 - (D.R.k - 1)) / (D.R.t + 1) < D.R.m := by
        apply Nat.div_lt_of_lt_mul
        have := D.R.m_add_three_le_k
        unfold Ranks.N at hi
        rw [Nat.mul_comm]; omega
      simp only [dif_neg h1, dif_pos h2, if_neg h1, bN_eq, eN_eq]; ring
  have hl : ∀ n (hn : n < D.R.N D.R.m), (((D.fm u).lam D.R.m τ).w ⟨n, hn⟩ : ℚ) = lamQ D.R (D.hcW u τ) n := by
    intro n hn
    rw [(D.fm u).lam_eq D.R.m le_rfl τ ⟨n, hn⟩]
    unfold lamQ
    by_cases h : n < D.R.k
    · simp only [dif_pos h, if_pos h, hcToWeightQ, rhoVec, uN_eq]
    · simp only [dif_neg h, if_neg h, eN_eq]
  constructor
  · have := key.1
    rw [← hs, ← hl i.1 (by omega)] at this
    exact_mod_cast this
  · have := key.2
    rw [← hs, ← hl (i.1 + 1) (by omega)] at this
    exact_mod_cast this

end Formalism.L2.Forms
