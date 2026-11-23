import Formalism.LocalToGlobal.Columns.AbelianHostFieldConditions

open NumberField IsDedekindDomain

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions

theorem mem_divs {A : Type} [CommRing A] [IsDedekindDomain A] {a : A} (ha : a ≠ 0) (P : HeightOneSpectrum A) :
    P ∈ divs a ↔ a ∈ P.asIdeal := by
  have hI : Ideal.span {a} ≠ ⊥ := by
    rwa [Ne, Ideal.span_singleton_eq_bot]
  have hfin : {P : HeightOneSpectrum A | a ∈ P.asIdeal}.Finite := by
    have h := Ideal.finite_factors hI
    simpa only [Ideal.dvd_span_singleton] using h
  unfold divs
  rw [dif_pos hfin, Set.Finite.mem_toFinset]
  rfl

theorem ofQ_w {N : ℕ} {x : Fin N → ℚ} (h : Antitone x) (hz : ∀ i, ∃ z : ℤ, x i = z) (i : Fin N) :
    ((ofQ x).w i : ℚ) = x i := by
  obtain ⟨z, hz'⟩ := hz i
  unfold ofQ
  rw [dif_pos h]
  simp [hz']

theorem anti_sub_rho {N : ℕ} (x : ℕ → ℚ) (h : ∀ n, n + 1 < N → x (n + 1) + 1 ≤ x n) :
    Antitone (fun i : Fin N => x i.1 - rhoVec N i) := by
  have key : ∀ d n : ℕ, n + d < N → x (n + d) + ((n + d : ℕ) : ℚ) ≤ x n + (n : ℚ) := by
    intro d
    induction d with
    | zero => intro n _; simp
    | succ d ih =>
      intro n hn
      have h1 := h (n + d) (by omega)
      have h2 := ih n (by omega)
      rw [show n + (d + 1) = n + d + 1 by omega]
      push_cast at h2 ⊢
      linarith
  intro i j hij
  have hle : i.1 ≤ j.1 := hij
  obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hle
  have hj := j.2
  have hk := key d i.1 (by omega)
  rw [← hd] at hk
  simp only [rhoVec]
  linarith

theorem int_gap {a b : ℚ} (ha : ∃ z : ℤ, a = z) (hb : ∃ z : ℤ, b = z) (h : a < b) : a + 1 ≤ b := by
  obtain ⟨x, rfl⟩ := ha
  obtain ⟨y, rfl⟩ := hb
  have hxy : x < y := by exact_mod_cast h
  have hxy' : x + 1 ≤ y := hxy
  exact_mod_cast hxy'

theorem divmod (c B ρ : ℕ) (h : ρ < c) : (B * c + ρ) / c = B ∧ (B * c + ρ) % c = ρ := by
  have hc : 0 < c := by omega
  refine ⟨?_, ?_⟩
  · rw [Nat.add_comm, Nat.add_mul_div_right _ _ hc, Nat.div_eq_of_lt h, Nat.zero_add]
  · rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt h]

namespace RowPar

variable {R : Ranks} (P : HCParam R)

theorem bAt_of {n : ℕ} (h : n < R.m) : (of P).bAt n = P.b ⟨n, h⟩ := by
  unfold RowPar.bAt
  rw [dif_pos h]
  rfl

theorem eAt_of {n : ℕ} (h : n < R.m) : (of P).eAt n = P.e ⟨n, h⟩ := by
  unfold RowPar.eAt
  rw [dif_pos h]
  rfl

theorem bAt_int (n : ℕ) : ∃ z : ℤ, (of P).bAt n = z := by
  unfold RowPar.bAt
  split_ifs with h
  · exact P.b_int ⟨n, h⟩
  · exact ⟨0, by simp⟩

theorem eAt_int (n : ℕ) : ∃ z : ℤ, (of P).eAt n = z := by
  unfold RowPar.eAt
  split_ifs with h
  · exact P.e_int ⟨n, h⟩
  · exact ⟨0, by simp⟩

theorem vb_lo {n : ℕ} (h : n < R.k - 1) : (of P).vb n = P.v ⟨n, h⟩ := by
  unfold RowPar.vb
  rw [dif_pos h]
  rfl

theorem vb_hi {n : ℕ} (h : ¬ n < R.k - 1) : (of P).vb n = -(of P).bAt (n - (R.k - 1)) := by
  unfold RowPar.vb
  rw [dif_neg h]

theorem vb_int (n : ℕ) : ∃ z : ℤ, (of P).vb n = z := by
  unfold RowPar.vb
  split_ifs with h
  · exact P.v_int ⟨n, h⟩
  · obtain ⟨z, hz⟩ := bAt_int P (n - (R.k - 1))
    exact ⟨-z, by rw [hz]; push_cast; ring⟩

theorem gap_be {c : ℕ} (h : c < R.m) : ((R.t : ℚ) + 3) / 2 ≤ (of P).eAt c - (of P).bAt c := by
  rw [eAt_of P h, bAt_of P h]
  exact P.gap_be ⟨c, h⟩

theorem gap_eb {c : ℕ} (h : c + 1 < R.m) : ((R.t : ℚ) + 3) / 2 ≤ (of P).bAt (c + 1) - (of P).eAt c := by
  rw [bAt_of P h, eAt_of P (by omega : c < R.m)]
  exact P.gap_eb ⟨c, by omega⟩ h

theorem b_step {c : ℕ} (h : c + 1 < R.m) : (of P).bAt c + 1 ≤ (of P).bAt (c + 1) := by
  have h1 := gap_be P (c := c) (by omega)
  have h2 := gap_eb P h
  have ht : (0 : ℚ) ≤ R.t := by positivity
  linarith

theorem vb_step {n : ℕ} (h : n + 1 < R.k - 1 + R.m) : (of P).vb (n + 1) + 1 ≤ (of P).vb n := by
  rcases lt_or_ge (n + 1) (R.k - 1) with h1 | h1
  · rw [vb_lo P h1, vb_lo P (by omega : n < R.k - 1)]
    have a1 := P.u_gt_v ⟨n + 1, h1⟩
    have a2 := P.v_gt_u ⟨n, by omega⟩
    exact int_gap (P.v_int _) (P.v_int _) (lt_trans a1 a2)
  · rcases lt_or_ge n (R.k - 1) with h2 | h2
    · have hm : 0 < R.m := by omega
      have hk : 0 < R.k := by omega
      have hn : n + 1 - (R.k - 1) = 0 := by omega
      rw [vb_hi P (n := n + 1) (by omega), vb_lo P h2, hn, bAt_of P hm]
      have a1 := P.u_last_gt hk hm
      have hu : (⟨R.k - 1, by omega⟩ : Fin R.k) = ⟨n + 1, by omega⟩ := Fin.ext (by show R.k - 1 = n + 1; omega)
      rw [hu] at a1
      have a2 := P.v_gt_u ⟨n, h2⟩
      obtain ⟨z, hz⟩ := P.b_int ⟨0, hm⟩
      exact int_gap ⟨-z, by rw [hz]; push_cast; ring⟩ (P.v_int _) (lt_trans a1 a2)
    · have e1 : n + 1 - (R.k - 1) = (n - (R.k - 1)) + 1 := by omega
      rw [vb_hi P (n := n + 1) (by omega), vb_hi P (n := n) (by omega), e1]
      have := b_step P (c := n - (R.k - 1)) (by omega)
      linarith

end RowPar

namespace RowPar

variable {R : Ranks} (P : HCParam R)

def sh (R : Ranks) : ℚ := ((R.m : ℚ) * ((R.t : ℚ) + 1)) / 2

theorem sgHC_lo (S : RowPar R) {n : ℕ} (h : n < R.k - 1) : S.sgHC n = sh R + S.vb n := by
  unfold RowPar.sgHC RowPar.vb RowPar.sh
  rw [dif_pos h, dif_pos h]

theorem sgHC_b (S : RowPar R) (B : ℕ) : S.sgHC (R.k - 1 + B * (R.t + 1)) = sh R - S.bAt B := by
  have h1 : ¬ (R.k - 1 + B * (R.t + 1) < R.k - 1) := by omega
  have e : R.k - 1 + B * (R.t + 1) - (R.k - 1) = B * (R.t + 1) := by omega
  have e2 : B * (R.t + 1) % (R.t + 1) = 0 := by simp
  have e3 : B * (R.t + 1) / (R.t + 1) = B := Nat.mul_div_cancel B (Nat.succ_pos _)
  unfold RowPar.sgHC RowPar.sh
  rw [dif_neg h1, e, if_pos e2, e3]
  ring

theorem sgHC_e (S : RowPar R) (B ρ : ℕ) (h1 : 1 ≤ ρ) (h2 : ρ ≤ R.t) :
    S.sgHC (R.k - 1 + B * (R.t + 1) + ρ) = sh R - S.eAt B + ((R.t : ℚ) - 1) / 2 - ((ρ : ℚ) - 1) := by
  have hd := divmod (R.t + 1) B ρ (by omega)
  have h1' : ¬ (R.k - 1 + B * (R.t + 1) + ρ < R.k - 1) := by omega
  have e : R.k - 1 + B * (R.t + 1) + ρ - (R.k - 1) = B * (R.t + 1) + ρ := by omega
  have hne : ¬ ((B * (R.t + 1) + ρ) % (R.t + 1) = 0) := by rw [hd.2]; omega
  unfold RowPar.sgHC RowPar.sh
  rw [dif_neg h1', e, if_neg hne, hd.1, hd.2]
  ring

theorem sgHC_step {n : ℕ} (hn : n + 1 < R.N R.m - 1) : (of P).sgHC (n + 1) + 1 ≤ (of P).sgHC n := by
  have hk3 := R.m_add_three_le_k
  have hm2 := R.two_le_m
  have ht5 := R.rank_add_five_le
  have hN : R.N R.m = R.k + R.m * (R.t + 1) := rfl
  rw [hN] at hn
  rcases lt_or_ge n (R.k - 1) with hlo | hhi
  · have hv := vb_step P (n := n) (by omega)
    have e0 : (of P).sgHC n = sh R + (of P).vb n := sgHC_lo (of P) hlo
    have e1 : (of P).sgHC (n + 1) = sh R + (of P).vb (n + 1) := by
      rcases lt_or_ge (n + 1) (R.k - 1) with h' | h'
      · exact sgHC_lo (of P) h'
      · have hn1 : n + 1 = R.k - 1 + 0 * (R.t + 1) := by omega
        rw [hn1, sgHC_b (of P) 0, ← hn1, vb_hi P (n := n + 1) (by omega),
          show n + 1 - (R.k - 1) = 0 by omega]
        ring
    rw [e0, e1]
    linarith
  · obtain ⟨B, ρ, hρ, hnB⟩ : ∃ B ρ : ℕ, ρ < R.t + 1 ∧ n = R.k - 1 + B * (R.t + 1) + ρ :=
      ⟨(n - (R.k - 1)) / (R.t + 1), (n - (R.k - 1)) % (R.t + 1), Nat.mod_lt _ (Nat.succ_pos _), by
        have hdm := Nat.div_add_mod (n - (R.k - 1)) (R.t + 1)
        rw [Nat.mul_comm] at hdm
        omega⟩
    subst hnB
    rcases Nat.eq_zero_or_pos ρ with h0 | hpos
    · subst h0
      have hBm : B < R.m := by
        by_contra hc
        push_neg at hc
        have hmul : R.m * (R.t + 1) ≤ B * (R.t + 1) := Nat.mul_le_mul_right _ hc
        omega
      have e0 : (of P).sgHC (R.k - 1 + B * (R.t + 1) + 0) = sh R - (of P).bAt B := by
        rw [Nat.add_zero]; exact sgHC_b (of P) B
      have e1 : (of P).sgHC (R.k - 1 + B * (R.t + 1) + 0 + 1) =
          sh R - (of P).eAt B + ((R.t : ℚ) - 1) / 2 - (((1 : ℕ) : ℚ) - 1) := by
        rw [Nat.add_zero]; exact sgHC_e (of P) B 1 le_rfl (by omega)
      rw [e0, e1]
      have hg := gap_be P hBm
      push_cast
      linarith
    · rcases lt_or_ge ρ R.t with hlt | hge
      · have e0 := sgHC_e (of P) B ρ hpos hlt.le
        have e1 := sgHC_e (of P) B (ρ + 1) (by omega) hlt
        rw [show R.k - 1 + B * (R.t + 1) + ρ + 1 = R.k - 1 + B * (R.t + 1) + (ρ + 1) by omega, e1, e0]
        push_cast
        linarith
      · have hρt : ρ = R.t := by omega
        subst hρt
        have emul : (B + 1) * (R.t + 1) = B * (R.t + 1) + R.t + 1 := by ring
        have hB1 : B + 1 < R.m := by
          by_contra hc
          push_neg at hc
          have hmul : R.m * (R.t + 1) ≤ (B + 1) * (R.t + 1) := Nat.mul_le_mul_right _ hc
          omega
        have e0 := sgHC_e (of P) B R.t (by omega) le_rfl
        have e1 : (of P).sgHC (R.k - 1 + B * (R.t + 1) + R.t + 1) = sh R - (of P).bAt (B + 1) := by
          rw [show R.k - 1 + B * (R.t + 1) + R.t + 1 = R.k - 1 + (B + 1) * (R.t + 1) by omega]
          exact sgHC_b (of P) (B + 1)
        rw [e1, e0]
        have hg := gap_eb P hB1
        linarith

theorem sgQ_anti : Antitone (of P).sgQ := by
  intro i j hij
  exact anti_sub_rho (of P).sgHC (fun n hn => sgHC_step P hn) hij

theorem sgHC_int (n : ℕ) : ∃ z : ℤ, (of P).sgHC n = z := by
  obtain ⟨a, ha⟩ := R.m_even
  obtain ⟨s, hs⟩ := R.t_odd
  have hsh : ((R.m : ℚ) * ((R.t : ℚ) + 1)) / 2 = ((a * (R.t + 1) : ℕ) : ℚ) := by
    rw [ha]; push_cast; ring
  have hth : ((R.t : ℚ) - 1) / 2 = (s : ℚ) := by
    rw [hs]; push_cast; ring
  unfold RowPar.sgHC
  rw [hsh]
  split_ifs with h1 h2
  · obtain ⟨z, hz⟩ : ∃ z : ℤ, (of P).v ⟨n, h1⟩ = z := P.v_int ⟨n, h1⟩
    exact ⟨((a * (R.t + 1) : ℕ) : ℤ) + z, by rw [hz]; push_cast; ring⟩
  · obtain ⟨z, hz⟩ := bAt_int P ((n - (R.k - 1)) / (R.t + 1))
    exact ⟨((a * (R.t + 1) : ℕ) : ℤ) - z, by rw [hz]; push_cast; ring⟩
  · obtain ⟨z, hz⟩ := eAt_int P ((n - (R.k - 1)) / (R.t + 1))
    rw [hth, hz]
    generalize (n - (R.k - 1)) % (R.t + 1) = r
    exact ⟨((a * (R.t + 1) : ℕ) : ℤ) - z + (s : ℤ) - (r : ℤ) + 1, by push_cast; ring⟩

theorem sgQ_int (i : Fin (R.N R.m - 1)) : ∃ z : ℤ, (of P).sgQ i = z := by
  have hk3 := R.m_add_three_le_k
  obtain ⟨z, hz⟩ := sgHC_int P i.1
  have hN1 : 1 ≤ R.N R.m := by
    show 1 ≤ R.k + R.m * (R.t + 1)
    omega
  have hNq : ((R.N R.m : ℕ) : ℚ) = (R.k : ℚ) + (R.m : ℚ) * ((R.t : ℚ) + 1) := by
    show ((R.k + R.m * (R.t + 1) : ℕ) : ℚ) = _
    push_cast; ring
  have hrho : rhoVec (R.N R.m - 1) i = ((R.k : ℚ) + (R.m : ℚ) * ((R.t : ℚ) + 1) - 2) / 2 - ((i.1 : ℕ) : ℚ) := by
    unfold rhoVec
    rw [Nat.cast_sub hN1, hNq]
    ring
  obtain ⟨a, ha⟩ := R.k_even
  obtain ⟨b, hb⟩ := R.m_even
  have hk : (R.k : ℚ) = a + a := by exact_mod_cast ha
  have hm : (R.m : ℚ) = b + b := by exact_mod_cast hb
  refine ⟨z - ((a : ℤ) + (b : ℤ) * ((R.t : ℤ) + 1) - 1 - ((i.1 : ℕ) : ℤ)), ?_⟩
  show (of P).sgHC i.1 - rhoVec (R.N R.m - 1) i = _
  rw [hz, hrho, hk, hm]
  push_cast
  ring

theorem sg_eq (i : Fin (R.N R.m - 1)) :
    (((of P).sg).w i : ℚ) = (of P).sgHC i.1 - rhoVec (R.N R.m - 1) i := by
  exact ofQ_w (sgQ_anti P) (sgQ_int P) i

end RowPar

namespace RowPar

variable {R : Ranks} (P : HCParam R)

def hcV (S : RowPar R) (j n : ℕ) : ℚ :=
  if n < pOf R j then S.vb n
  else if n < pOf R j + R.t then -S.eAt (j - 1) + ((R.t : ℚ) - 1) / 2 - ((n - pOf R j : ℕ) : ℚ)
  else -S.bAt (j + (n - (pOf R j + R.t)))

theorem cast_pOf {j : ℕ} (h1 : 1 ≤ j) : (pOf R j : ℚ) = (R.k : ℚ) + j - 1 := by
  unfold RowPar.pOf
  rw [Nat.cast_sub (by omega : 1 ≤ R.k + j)]
  push_cast
  ring

theorem cast_qOf {j : ℕ} (h2 : j ≤ R.m) : (qOf R j : ℚ) = (R.m : ℚ) - j := by
  unfold RowPar.qOf
  rw [Nat.cast_sub h2]

theorem cast_nV : (R.nV : ℚ) = (R.k : ℚ) + R.m - 1 + R.t := by
  have hk3 := R.m_add_three_le_k
  unfold Ranks.nV Ranks.r
  rw [Nat.cast_add, Nat.cast_sub (by omega : 1 ≤ R.k + R.m)]
  push_cast
  ring

theorem lamVQ_eq_hc (S : RowPar R) {j : ℕ} (h1 : 1 ≤ j) (h2 : j ≤ R.m) (i : Fin R.nV) :
    S.lamVQ j i = (S.hcV j i.1 - 1 / 2) - rhoVec R.nV i := by
  have hp := cast_pOf (R := R) h1
  have hq := cast_qOf (R := R) h2
  have hn := cast_nV (R := R)
  unfold RowPar.lamVQ RowPar.hcV RowPar.aPlus RowPar.aMinusRev RowPar.dV rhoVec
  split_ifs with c1 c2
  · rw [show i.1 + 1 - 1 = i.1 by omega]
    push_cast
    simp only [hp, hq, hn]
    ring
  · push_cast [Nat.cast_sub (show pOf R j ≤ i.1 by omega)]
    simp only [hp, hq, hn]
    ring
  · rw [show j + (i.1 - (pOf R j + R.t) + 1) - 1 = j + (i.1 - (pOf R j + R.t)) by omega]
    push_cast [Nat.cast_sub (show pOf R j + R.t ≤ i.1 by omega)]
    simp only [hp, hq, hn]
    ring

theorem hcV_step {j : ℕ} (h1 : 1 ≤ j) (h2 : j ≤ R.m) {n : ℕ} (hn : n + 1 < R.nV) :
    (of P).hcV j (n + 1) + 1 ≤ (of P).hcV j n := by
  have hk3 := R.m_add_three_le_k
  have ht1 : 1 ≤ R.t := by have := R.rank_add_five_le; omega
  have hp : pOf R j = R.k + j - 1 := rfl
  have hnV : R.nV = R.k + R.m - 1 + R.t := rfl
  rw [hnV] at hn
  unfold RowPar.hcV
  rcases lt_or_ge (n + 1) (pOf R j) with a1 | a1
  · rw [if_pos a1, if_pos (by omega : n < pOf R j)]
    exact vb_step P (n := n) (by omega)
  · rcases lt_or_ge n (pOf R j) with a2 | a2
    · rw [if_neg (by omega : ¬ n + 1 < pOf R j), if_pos (by omega : n + 1 < pOf R j + R.t), if_pos a2,
        vb_hi P (n := n) (by omega), show n - (R.k - 1) = j - 1 by omega,
        show n + 1 - pOf R j = 0 by omega]
      have hg := gap_be P (c := j - 1) (by omega)
      push_cast
      linarith
    · rcases lt_or_ge (n + 1) (pOf R j + R.t) with a3 | a3
      · rw [if_neg (by omega : ¬ n + 1 < pOf R j), if_pos a3, if_neg (by omega : ¬ n < pOf R j),
          if_pos (by omega : n < pOf R j + R.t), show n + 1 - pOf R j = (n - pOf R j) + 1 by omega]
        push_cast
        linarith
      · rcases lt_or_ge n (pOf R j + R.t) with a4 | a4
        · rw [if_neg (by omega : ¬ n + 1 < pOf R j), if_neg (by omega : ¬ n + 1 < pOf R j + R.t),
            if_neg (by omega : ¬ n < pOf R j), if_pos a4,
            show j + (n + 1 - (pOf R j + R.t)) = (j - 1) + 1 by omega,
            show n - pOf R j = R.t - 1 by omega, Nat.cast_sub (by omega : 1 ≤ R.t)]
          have hg := gap_eb P (c := j - 1) (by omega)
          push_cast
          linarith
        · rw [if_neg (by omega : ¬ n + 1 < pOf R j), if_neg (by omega : ¬ n + 1 < pOf R j + R.t),
            if_neg (by omega : ¬ n < pOf R j), if_neg (by omega : ¬ n < pOf R j + R.t),
            show j + (n + 1 - (pOf R j + R.t)) = (j + (n - (pOf R j + R.t))) + 1 by omega]
          have hg := b_step P (c := j + (n - (pOf R j + R.t))) (by omega)
          linarith

theorem lamVQ_anti {j : ℕ} (h1 : 1 ≤ j) (h2 : j ≤ R.m) : Antitone ((of P).lamVQ j) := by
  intro a b hab
  have H := anti_sub_rho (N := R.nV) (fun n => (of P).hcV j n - 1 / 2)
    (fun n hn => by
      show (of P).hcV j (n + 1) - 1 / 2 + 1 ≤ (of P).hcV j n - 1 / 2
      linarith [hcV_step P h1 h2 hn]) hab
  simp only at H
  rw [lamVQ_eq_hc (of P) h1 h2, lamVQ_eq_hc (of P) h1 h2]
  exact H

theorem hcV_int (j n : ℕ) : ∃ z : ℤ, (of P).hcV j n = z := by
  obtain ⟨s, hs⟩ := R.t_odd
  have hth : ((R.t : ℚ) - 1) / 2 = (s : ℚ) := by rw [hs]; push_cast; ring
  unfold RowPar.hcV
  split_ifs
  · exact vb_int P n
  · obtain ⟨z, hz⟩ := eAt_int P (j - 1)
    rw [hth, hz]
    generalize n - pOf R j = r
    exact ⟨-z + s - r, by push_cast; ring⟩
  · obtain ⟨z, hz⟩ := bAt_int P (j + (n - (pOf R j + R.t)))
    exact ⟨-z, by rw [hz]; push_cast; ring⟩

theorem lamVQ_int {j : ℕ} (h1 : 1 ≤ j) (h2 : j ≤ R.m) (i : Fin R.nV) : ∃ z : ℤ, (of P).lamVQ j i = z := by
  obtain ⟨z, hz⟩ := hcV_int P j i.1
  rw [lamVQ_eq_hc (of P) h1 h2, hz]
  obtain ⟨a, ha⟩ := R.k_even
  obtain ⟨b, hb⟩ := R.m_even
  obtain ⟨s, hs⟩ := R.t_odd
  have hn := cast_nV (R := R)
  have hk : (R.k : ℚ) = a + a := by exact_mod_cast ha
  have hm : (R.m : ℚ) = b + b := by exact_mod_cast hb
  have ht : (R.t : ℚ) = 2 * s + 1 := by exact_mod_cast hs
  unfold rhoVec
  rw [hn, hk, hm, ht]
  exact ⟨z - (a + b + s) + ((i.1 : ℕ) : ℤ), by push_cast; ring⟩

theorem lamV_eq {j : ℕ} (h1 : 1 ≤ j) (h2 : j ≤ R.m) (i : Fin R.nV) :
    ((((of P).lamV j).w i : ℤ) : ℚ) = (of P).lamVQ j i := by
  exact ofQ_w (lamVQ_anti P h1 h2) (lamVQ_int P h1 h2) i

end RowPar

theorem wG_int (R : Ranks) (z : ℤ) (j : ℕ) : ∃ y : ℤ, wG R (z : ℚ) j = y := by
  obtain ⟨a, ha⟩ := R.k_even
  obtain ⟨s, hs⟩ := R.t_odd
  refine ⟨z - a - (2 * (j : ℤ) - 1) * ((s : ℤ) + 1), ?_⟩
  have hk : (R.k : ℚ) = a + a := by exact_mod_cast ha
  have ht : (R.t : ℚ) = 2 * s + 1 := by exact_mod_cast hs
  unfold wG
  rw [hk, ht]
  push_cast
  ring

theorem cast_t_add_one_div_two (R : Ranks) : (((R.t + 1) / 2 : ℕ) : ℚ) = ((R.t : ℚ) + 1) / 2 := by
  obtain ⟨s, hs⟩ := R.t_odd
  rw [hs, show (2 * s + 1 + 1) / 2 = s + 1 by omega]
  push_cast
  ring

theorem lamOf_wtN {R : Ranks} (P : HCParam R) {j : ℕ} (hj : j ≤ R.m) (i : Fin (R.N j)) :
    ((Examples₂.lamOf P j).w i : ℚ) = Examples₂.wtN P i.1 := by
  have hint : ∃ z : ℤ, Examples₂.wtQ P j hj i = z := by
    unfold Examples₂.wtQ
    split_ifs with h
    · obtain ⟨z, hz⟩ := (P).u_half ⟨i.1, h⟩
      obtain ⟨a, ha⟩ := R.k_even
      have hk : (R.k : ℚ) = a + a := by exact_mod_cast ha
      refine ⟨z - a + 1 + ((i.1 : ℕ) : ℤ), ?_⟩
      simp only [hcToWeightQ, rhoVec, Fin.val_mk]
      rw [hz, hk]
      push_cast
      ring
    · obtain ⟨e, he⟩ := (P).e_int ⟨(i.1 - R.k) / (R.t + 1), R.blk_lt hj i h⟩
      obtain ⟨y, hy⟩ := wG_int R e ((i.1 - R.k) / (R.t + 1) + 1)
      exact ⟨-y, by rw [he, hy]; push_cast; ring⟩
  obtain ⟨z, hz⟩ := hint
  unfold Examples₂.lamOf
  rw [dif_pos hj]
  show ((⌊Examples₂.wtQ P j hj i⌋ : ℤ) : ℚ) = _
  rw [hz, Int.floor_intCast, ← hz]
  unfold Examples₂.wtQ Examples₂.wtN
  split_ifs with h1 h2
  · rfl
  · rfl
  · exact absurd (R.blk_lt hj i h1) h2

theorem wtN_new {R : Ranks} (P : HCParam R) {j : ℕ} (hj : j < R.m) {n : ℕ} (h1 : R.N j ≤ n) (h2 : n < R.N (j + 1)) :
    Examples₂.wtN P n = -wG R (P.e ⟨j, hj⟩) (j + 1) := by
  have h1' : R.k + j * (R.t + 1) ≤ n := h1
  have h2' : n < R.k + (j + 1) * (R.t + 1) := h2
  have hb : Examples₂.blkN R n = j :=
    Nat.div_eq_of_lt_le (by omega) (show n - R.k < (j + 1) * (R.t + 1) by omega)
  have hbm : Examples₂.blkN R n < R.m := hb ▸ hj
  unfold Examples₂.wtN
  rw [dif_neg (by omega : ¬ n < R.k), dif_pos hbm]
  have e : (⟨Examples₂.blkN R n, hbm⟩ : Fin R.m) = ⟨j, hj⟩ := Fin.ext hb
  rw [e, hb]

namespace Wts

variable {X : Fields} {Word : Type} {R : Ranks} (W : Wts X Word R)

theorem lamN_eq (u : Word) {j : ℕ} (hj : j ≤ R.m) (τ : X.Tau) (i : Fin (R.N j)) :
    ((W.lamN u j τ).w i : ℚ) =
      if h : i.1 < R.k then hcToWeightQ (W.hc u τ).u ⟨i.1, h⟩
      else -wG R ((W.hc u τ).e ⟨(i.1 - R.k) / (R.t + 1), R.blk_lt hj i h⟩) ((i.1 - R.k) / (R.t + 1) + 1) := by
  unfold Wts.lamN
  rw [lamOf_wtN (W.hc u τ) hj i]
  unfold Examples₂.wtN
  split_ifs with h1 h2
  · rfl
  · rfl
  · exact absurd (R.blk_lt hj i h1) h2

theorem lamTrue_eq (u : Word) (j : ℕ) (τ : X.Tau) (i : Fin (R.N j)) :
    ((W.lamTrue u j τ).w i : ℚ) = (W.lamN u j τ).w i - (j : ℚ) * (((R.t : ℚ) + 1) / 2) := by
  unfold Wts.lamTrue
  show (((W.lamN u j τ).w i + (-((j : ℤ) * (((R.t + 1) / 2 : ℕ) : ℤ))) : ℤ) : ℚ) = _
  simp only [Int.cast_add, Int.cast_neg, Int.cast_mul, Int.cast_natCast]
  rw [cast_t_add_one_div_two R]
  ring

theorem lamTrue_zero (u : Word) (τ : X.Tau) (i : Fin (R.N 0)) : (W.lamTrue u 0 τ).w i = (W.lamN u 0 τ).w i := by
  show (W.lamN u 0 τ).w i + -(((0 : ℕ) : ℤ) * (((R.t + 1) / 2 : ℕ) : ℤ)) = (W.lamN u 0 τ).w i
  simp

theorem lamTrue_old (u : Word) {j : ℕ} (hj : j < R.m) (τ : X.Tau) (i : Fin (R.N (j + 1))) (h : i.1 < R.N j) :
    ((W.lamTrue u (j + 1) τ).w i : ℚ) =
      (W.lamTrue u j τ).w ⟨i.1, h⟩ + sExp' R ((W.hc u τ).e ⟨j, hj⟩) (j + 1) - sExp R ((W.hc u τ).e ⟨j, hj⟩) (j + 1) := by
  have e1 := lamN_eq W u (by omega : j + 1 ≤ R.m) τ i
  have e2 := lamN_eq W u hj.le τ ⟨i.1, h⟩
  have hl : ((W.lamN u (j + 1) τ).w i : ℚ) = (W.lamN u j τ).w ⟨i.1, h⟩ := e1.trans e2.symm
  rw [lamTrue_eq W u (j + 1) τ i, lamTrue_eq W u j τ ⟨i.1, h⟩, hl]
  have hN1 : ((R.N (j + 1) : ℕ) : ℚ) = R.k + (j + 1) * (R.t + 1) := by
    unfold Ranks.N; push_cast; ring
  have hN0 : ((R.N (j + 1 - 1) : ℕ) : ℚ) = R.k + j * (R.t + 1) := by
    rw [Nat.add_sub_cancel]; unfold Ranks.N; push_cast; ring
  unfold sExp sExp'
  rw [hN1, hN0]
  push_cast
  ring

theorem lamTrue_new (u : Word) {j : ℕ} (hj : j < R.m) (τ : X.Tau) (i : Fin (R.N (j + 1))) (h : ¬ i.1 < R.N j) :
    ((W.lamTrue u (j + 1) τ).w i : ℚ) = -sExp R ((W.hc u τ).e ⟨j, hj⟩) (j + 1) := by
  have hk : ¬ i.1 < R.k := by
    have h1 : R.k + j * (R.t + 1) ≤ i.1 := Nat.le_of_not_lt h
    omega
  have hblk : (i.1 - R.k) / (R.t + 1) = j := by
    have h1 : R.k + j * (R.t + 1) ≤ i.1 := Nat.le_of_not_lt h
    have h2 : i.1 < R.k + (j + 1) * (R.t + 1) := i.2
    exact Nat.div_eq_of_lt_le (by omega) (show i.1 - R.k < (j + 1) * (R.t + 1) by omega)
  have hj1 : j + 1 ≤ R.m := by omega
  rw [lamTrue_eq W u (j + 1) τ i, lamN_eq W u hj1 τ i, dif_neg hk]
  have e : (⟨(i.1 - R.k) / (R.t + 1), R.blk_lt hj1 i hk⟩ : Fin R.m) = ⟨j, hj⟩ := Fin.ext hblk
  rw [e, hblk]
  have hN0 : ((R.N (j + 1 - 1) : ℕ) : ℚ) = R.k + j * (R.t + 1) := by
    rw [Nat.add_sub_cancel]; unfold Ranks.N; push_cast; ring
  unfold wG sExp
  rw [hN0]
  push_cast
  ring

theorem nuW_eq (u : Word) {j : ℕ} (hj : j < R.m) (τ : X.Tau) (i : Fin (R.N j)) :
    ((W.nuW u (j + 1) τ).w i : ℚ) = (W.lamN u j τ).w i + wG R ((W.hc u τ).e ⟨j, hj⟩) (j + 1) := by
  obtain ⟨e, he⟩ := (W.hc u τ).e_int ⟨j, hj⟩
  obtain ⟨y, hy⟩ := wG_int R e (j + 1)
  have hwe : wG R ((RowPar.of (W.hc u τ)).eAt j) (j + 1) = y := by
    rw [RowPar.eAt_of (W.hc u τ) hj, he, hy]
  show (((W.lamN u j τ).w i + ⌊wG R ((RowPar.of (W.hc u τ)).eAt j) (j + 1)⌋ : ℤ) : ℚ) = _
  rw [hwe, Int.floor_intCast]
  push_cast
  rw [← hwe, RowPar.eAt_of (W.hc u τ) hj]

theorem nuW_eq_true (u : Word) {j : ℕ} (hj : j < R.m) (τ : X.Tau) (i : Fin (R.N j)) :
    ((W.nuW u (j + 1) τ).w i : ℚ) = (W.lamTrue u j τ).w i + sExp' R ((W.hc u τ).e ⟨j, hj⟩) (j + 1) := by
  rw [nuW_eq W u hj τ i, lamTrue_eq W u j τ i]
  have hN1 : ((R.N (j + 1) : ℕ) : ℚ) = R.k + (j + 1) * (R.t + 1) := by
    unfold Ranks.N; push_cast; ring
  unfold wG sExp'
  rw [hN1]
  push_cast
  ring

variable {W}

theorem sgW_eq (hW : W.Ok) (τ : X.Tau) (i : Fin (R.N R.m - 1)) :
    ((W.sgW τ).w i : ℚ) = (W.row τ).sgHC i.1 - rhoVec (R.N R.m - 1) i := by
  obtain ⟨P, hP⟩ := hW.row_ok τ
  unfold Wts.sgW
  rw [← hP]
  exact RowPar.sg_eq P i

theorem lamV_eq (hW : W.Ok) {j : ℕ} (h1 : 1 ≤ j) (h2 : j ≤ R.m) (τ : X.Tau) (i : Fin R.nV) :
    ((W.lamV j τ).w i : ℚ) = (W.row τ).lamVQ j i := by
  obtain ⟨P, hP⟩ := hW.row_ok τ
  unfold Wts.lamV
  rw [← hP]
  exact RowPar.lamV_eq P h1 h2 i

end Wts

namespace RowPar

variable {R : Ranks} (P : HCParam R)

theorem sgTrue_eq (i : Fin (R.N R.m - 1)) :
    (((of P).sgTrue).w i : ℚ) = ((of P).sgHC i.1 - sh R) - rhoVec (R.N R.m - 1) i := by
  show ((((of P).sg.w i + -((R.m : ℤ) * (((R.t + 1) / 2 : ℕ) : ℤ))) : ℤ) : ℚ) = _
  simp only [Int.cast_add, Int.cast_neg, Int.cast_mul, Int.cast_natCast]
  rw [sg_eq P i, cast_t_add_one_div_two R]
  unfold RowPar.sh
  ring

end RowPar

namespace Wts

variable {X : Fields} {Word : Type} {R : Ranks} (W : Wts X Word R)

theorem degTrue_eq (u : Word) (τ : X.Tau) :
    W.degTrue u τ = W.deg u τ - (R.m : ℤ) * (((R.t + 1) / 2 : ℕ) : ℤ) := by
  have hN1 : 1 ≤ R.N R.m := by
    show 1 ≤ R.k + R.m * (R.t + 1)
    have := R.m_add_three_le_k
    omega
  unfold Wts.degTrue Wts.deg Wts.lamTrue Wts.sgTrue Wts.sgW RowPar.sgTrue
  simp only [shiftW, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, Nat.cast_sub hN1, Nat.cast_one]
  ring

end Wts

namespace Fields

variable (X : Fields)

theorem conjO_invol (x : 𝓞 X.E) : X.conjO (X.conjO x) = x := by
  apply RingOfIntegers.ext
  simp [Fields.conjO]

def conjOEquiv : 𝓞 X.E ≃+* 𝓞 X.E :=
  RingEquiv.ofRingHom X.conjO X.conjO (RingHom.ext X.conjO_invol) (RingHom.ext X.conjO_invol)

theorem absNorm_conjO (a : 𝓞 X.E) :
    Ideal.absNorm (Ideal.span {X.conjO a}) = Ideal.absNorm (Ideal.span {a}) := by
  have e : Ideal.span {X.conjO a} = Ideal.map X.conjOEquiv (Ideal.span {a}) := by
    rw [Ideal.map_span, Set.image_singleton]
    rfl
  rw [e, Ideal.absNorm_apply, Ideal.absNorm_apply, Submodule.cardQuot_apply, Submodule.cardQuot_apply]
  exact Nat.card_congr (Ideal.quotientEquiv _ _ X.conjOEquiv rfl).toEquiv.symm

theorem absNorm_nat (n : ℕ) : Ideal.absNorm (Ideal.span {(n : 𝓞 X.E)}) = n ^ Module.finrank ℚ X.E := by
  rw [Ideal.absNorm_span_singleton]
  have h : ((n : 𝓞 X.E)) = algebraMap ℤ (𝓞 X.E) (n : ℤ) := by simp
  rw [h, Algebra.norm_algebraMap, NumberField.RingOfIntegers.rank]
  simp

variable {X}

theorem Ok.rankQ (hX : X.Ok) : Module.finrank ℚ X.E = 2 * X.f := by
  have h := Module.finrank_mul_finrank ℚ X.F X.E
  rw [hX.rankE, ← hX.card_Tau] at h
  unfold Fields.f
  rw [← h]
  ring

end Fields

namespace Primes

variable {X : Fields} {Pr : Primes X}

theorem Ok.piT_ne_zero (hPr : Pr.Ok) (u : Pr.Word) : Pr.piT u ≠ 0 := by
  intro h0
  have h := hPr.piT_norm u
  rw [h0, zero_mul] at h
  have hT := (hPr.T_prime u).pos
  have hne : ((Pr.T u : ℕ) : 𝓞 X.E) ≠ 0 := by exact_mod_cast hT.ne'
  exact hne h.symm

theorem Ok.absNorm_piT (hX : X.Ok) (hPr : Pr.Ok) (u : Pr.Word) :
    Ideal.absNorm (Ideal.span {Pr.piT u}) = Pr.T u ^ X.f := by
  have hmul : Ideal.span {Pr.piT u} * Ideal.span {X.conjO (Pr.piT u)} =
      Ideal.span {((Pr.T u : ℕ) : 𝓞 X.E)} := by
    rw [Ideal.span_singleton_mul_span_singleton, hPr.piT_norm u]
  have h : Ideal.absNorm (Ideal.span {Pr.piT u} * Ideal.span {X.conjO (Pr.piT u)}) =
      Ideal.absNorm (Ideal.span {((Pr.T u : ℕ) : 𝓞 X.E)}) := by rw [hmul]
  rw [map_mul, Fields.absNorm_conjO X, Fields.absNorm_nat X, hX.rankQ] at h
  have h2 : Ideal.absNorm (Ideal.span {Pr.piT u}) ^ 2 = (Pr.T u ^ X.f) ^ 2 := by
    rw [sq, h]; ring
  exact Nat.pow_left_injective (by norm_num) h2

theorem Ok.piT_notMem_sq (hX : X.Ok) (hPr : Pr.Ok) (u : Pr.Word) {P : HeightOneSpectrum (𝓞 X.E)} (hP : P ∈ Pr.vT u) :
    Pr.piT u ∉ P.asIdeal ^ 2 := by
  classical
  intro hmem
  have hne := hPr.piT_ne_zero u
  have hT2 : 2 ≤ Pr.T u := (hPr.T_prime u).two_le
  have hQ : ∀ Q ∈ Pr.vT u, Q.asIdeal ∣ Ideal.span {Pr.piT u} := fun Q hQ' => by
    rw [Ideal.dvd_span_singleton]
    exact (mem_divs hne Q).1 hQ'
  have hmax : ∀ A B : HeightOneSpectrum (𝓞 X.E), A ≠ B → IsCoprime A.asIdeal B.asIdeal := by
    intro A B hAB
    rw [Ideal.isCoprime_iff_sup_eq]
    exact Ideal.IsMaximal.coprime_of_ne A.isMaximal B.isMaximal (fun h => hAB (HeightOneSpectrum.ext h))
  let g : HeightOneSpectrum (𝓞 X.E) → Ideal (𝓞 X.E) := fun Q => if Q = P then P.asIdeal ^ 2 else Q.asIdeal
  have hg : ∀ Q ∈ Pr.vT u, g Q ∣ Ideal.span {Pr.piT u} := by
    intro Q hQ'
    show (if Q = P then P.asIdeal ^ 2 else Q.asIdeal) ∣ _
    by_cases h : Q = P
    · rw [if_pos h, Ideal.dvd_span_singleton]
      exact hmem
    · rw [if_neg h]
      exact hQ Q hQ'
  have hcop : ((Pr.vT u : Finset (HeightOneSpectrum (𝓞 X.E))) : Set (HeightOneSpectrum (𝓞 X.E))).Pairwise
      (Function.onFun IsCoprime g) := by
    intro Q _ Q' _ hQQ'
    show IsCoprime (if Q = P then P.asIdeal ^ 2 else Q.asIdeal) (if Q' = P then P.asIdeal ^ 2 else Q'.asIdeal)
    by_cases h1 : Q = P
    · have h2 : Q' ≠ P := fun h => hQQ' (h1.trans h.symm)
      rw [if_pos h1, if_neg h2]
      exact (hmax P Q' (Ne.symm h2)).pow_left
    · by_cases h2 : Q' = P
      · rw [if_neg h1, if_pos h2]
        exact (hmax Q P h1).pow_right
      · rw [if_neg h1, if_neg h2]
        exact hmax Q Q' hQQ'
  have hdvd := Finset.prod_dvd_of_coprime hcop hg
  have hN := map_dvd Ideal.absNorm hdvd
  have hprod : ∀ Q ∈ Pr.vT u, Ideal.absNorm (g Q) = Pr.T u * (if Q = P then Pr.T u else 1) := by
    intro Q hQ'
    show Ideal.absNorm (if Q = P then P.asIdeal ^ 2 else Q.asIdeal) = _
    by_cases h : Q = P
    · rw [if_pos h, if_pos h, map_pow, hPr.vT_norm u P hP]
      ring
    · rw [if_neg h, if_neg h, hPr.vT_norm u Q hQ', mul_one]
  rw [map_prod, hPr.absNorm_piT hX u, Finset.prod_congr rfl hprod] at hN
  simp only [Finset.prod_mul_distrib, Finset.prod_const, Finset.prod_ite_eq', if_pos hP, hPr.vT_card u] at hN
  rw [← pow_succ] at hN
  have hle := (Nat.pow_dvd_pow_iff_le_right (by omega : 1 < Pr.T u)).1 hN
  omega

end Primes

end Formalism.L2.Col
