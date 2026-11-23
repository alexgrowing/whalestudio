import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.FamilyFourthBound
import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.SegmentStatementHolds
import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.ThresholdLowerBounds

noncomputable section

namespace Formalism.MainNotions.ColumnSystems.Pf

open Formalism.MainNotions.G

variable {s r : ℕ}

theorem coarseA_mul (p : ℕ) (S : SegData s) (b : SegBlock s r) (i : Fin s) :
    (coarseA p S b i : ℝ) * (p : ℝ) ^ (S.G - S.d i) ≤ (S.bTop i : ℝ) := by
  have h : coarseA p S b i * p ^ (S.G - S.d i) ≤ S.bTop i := by
    unfold coarseA SegData.P
    exact (Nat.div_mul_le_self _ _).trans (Nat.sub_le _ _)
  exact_mod_cast h

theorem cap_le (p : ℕ) (S : SegData s) (b : SegBlock s r) (l : ℕ) :
    (cap p S b l : ℝ) ≤ (S.A0 p : ℝ) + ∑ i : Fin s, if (i : ℕ) < l then (coarseA p S b i : ℝ) else 0 := by
  unfold cap
  push_cast
  apply add_le_add le_rfl
  apply Finset.sum_le_sum
  intro i _
  split_ifs
  · have h0 : (0 : ℝ) ≤ (oEff S b i : ℝ) := Nat.cast_nonneg _
    linarith
  · exact le_rfl

theorem base_exponent_le_a (p : ℕ) (hp : 0 < p) (S : SegData s) (hE : 0 ≤ S.E0) :
    (S.A0 p : ℝ) ≤ (S.a : ℝ) / (p : ℝ) ^ S.G := by
  unfold SegData.A0 SegData.Qj
  push_cast
  have hp' : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp
  have hq : (0 : ℝ) < (p : ℝ) ^ S.G := pow_pos hp' _
  refine (Int.floor_le _).trans ?_
  gcongr
  linarith

structure SegHyp (p : ℕ) (S : SegData s) (b' de be aS Q : ℝ) : Prop where
  p5 : 5 ≤ p
  G2 : 2 ≤ S.G
  dlt : ∀ i, 0 < S.d i ∧ S.d i < S.G
  dodd : ∀ i, Odd (S.d i)
  dmono : StrictMono S.d
  sig : ∀ i : Fin s, (i : ℕ) < S.sigma ↔ (p : ℝ) ^ (S.d i) < (S.a : ℝ) / b'
  bpos : 0 < b'
  La0 : 0 ≤ S.La
  errorNonneg : 0 ≤ S.E0
  bT : ∀ i, b' * (1 - be) ≤ S.bTop i ∧ (S.bTop i : ℝ) ≤ b' * (1 + be)
  bP : (S.bPlus : ℝ) ≤ b' * (1 + be)
  be0 : 0 ≤ be
  beLe : be ≤ de / 2
  de6 : de < 1 / 6
  band : ∀ d : ℕ, Odd d → ¬ (((S.a : ℝ) / b') * (1 - 2 * de) ≤ (p : ℝ) ^ d ∧
    (p : ℝ) ^ d ≤ ((S.a : ℝ) / b') * (1 + 2 * de))
  aS : (S.a : ℝ) ≤ aS
  sp : (s : ℝ) ≤ p
  Q : (p : ℝ) ^ S.G ≤ Q

variable {p : ℕ} {S : SegData s} {b' de be aS Q : ℝ}

theorem SegHyp.p0 (H : SegHyp p S b' de be aS Q) : (5 : ℝ) ≤ (p : ℝ) := by
  exact_mod_cast H.p5

theorem SegHyp.top_degree_le_two_b (H : SegHyp p S b' de be aS Q) (i : Fin s) : (S.bTop i : ℝ) ≤ 2 * b' := by
  have h1 := (H.bT i).2
  have hb := H.bpos
  have hbe : be ≤ 1 := by linarith [H.beLe, H.de6, H.be0]
  have h2 : b' * be ≤ b' * 1 := mul_le_mul_of_nonneg_left hbe hb.le
  nlinarith [h1, h2]

private theorem mul_sum_pow_lt_le_pow_of_segHyp (H : SegHyp p S b' de be aS Q) :
    ∀ n : ℕ, ∀ hn : n < s, (p : ℝ) * (∑ j : Fin s, if (j : ℕ) < n then (p : ℝ) ^ (S.d j) else 0) ≤
      (p : ℝ) ^ (S.d ⟨n, hn⟩) := by
  have hp : (5 : ℝ) ≤ p := H.p0
  intro n
  induction n with
  | zero =>
    intro hn
    simp only [Nat.not_lt_zero, if_false, Finset.sum_const_zero, mul_zero]
    positivity
  | succ n ih =>
    intro hn
    have hn' : n < s := Nat.lt_of_succ_lt hn
    have hterm : ∀ j : Fin s, (if (j : ℕ) < n + 1 then (p : ℝ) ^ (S.d j) else 0) =
        (if (j : ℕ) < n then (p : ℝ) ^ (S.d j) else 0) +
          (if j = ⟨n, hn'⟩ then (p : ℝ) ^ (S.d j) else 0) := by
      intro j
      by_cases h1 : (j : ℕ) < n
      · have h2 : j ≠ ⟨n, hn'⟩ := by
          intro h
          rw [h] at h1
          exact lt_irrefl _ h1
        have h1' : (j : ℕ) < n + 1 := by omega
        simp [h1, h2, h1']
      · by_cases h3 : j = ⟨n, hn'⟩
        · subst h3
          simp
        · have h4 : ¬ (j : ℕ) < n + 1 := by
            intro h
            exact h3 (Fin.ext (by show (j : ℕ) = n; omega))
          simp [h1, h3, h4]
    have hsplit : (∑ j : Fin s, if (j : ℕ) < n + 1 then (p : ℝ) ^ (S.d j) else 0) =
        (∑ j : Fin s, if (j : ℕ) < n then (p : ℝ) ^ (S.d j) else 0) + (p : ℝ) ^ (S.d ⟨n, hn'⟩) := by
      rw [Finset.sum_congr rfl (fun j _ => hterm j), Finset.sum_add_distrib, Finset.sum_ite_eq']
      simp
    rw [hsplit]
    have hgap : S.d ⟨n, hn'⟩ + 2 ≤ S.d ⟨n + 1, hn⟩ := by
      have hlt : S.d ⟨n, hn'⟩ < S.d ⟨n + 1, hn⟩ :=
        H.dmono (show (⟨n, hn'⟩ : Fin s) < ⟨n + 1, hn⟩ from Nat.lt_succ_self n)
      obtain ⟨u, hu⟩ := H.dodd ⟨n, hn'⟩
      obtain ⟨v, hv⟩ := H.dodd ⟨n + 1, hn⟩
      omega
    have ihn := ih hn'
    have hpe : (0 : ℝ) ≤ (p : ℝ) ^ (S.d ⟨n, hn'⟩) := by positivity
    have h12 : (1 : ℝ) + p ≤ (p : ℝ) ^ 2 := by nlinarith
    calc (p : ℝ) * ((∑ j : Fin s, if (j : ℕ) < n then (p : ℝ) ^ (S.d j) else 0) +
          (p : ℝ) ^ (S.d ⟨n, hn'⟩))
        ≤ (p : ℝ) ^ (S.d ⟨n, hn'⟩) * (1 + p) := by nlinarith
      _ ≤ (p : ℝ) ^ (S.d ⟨n, hn'⟩) * (p : ℝ) ^ 2 := mul_le_mul_of_nonneg_left h12 hpe
      _ = (p : ℝ) ^ (S.d ⟨n, hn'⟩ + 2) := (pow_add _ _ _).symm
      _ ≤ (p : ℝ) ^ (S.d ⟨n + 1, hn⟩) := pow_le_pow_right₀ (by linarith) hgap

theorem SegHyp.Pcap (H : SegHyp p S b' de be aS Q) (b : SegBlock s r) (i : Fin s) :
    (p : ℝ) ^ (S.G - S.d i) * (cap p S b i : ℝ) ≤ (S.a : ℝ) / (p : ℝ) ^ (S.d i) + 2 * (b' / p) := by
  have hp5 : (5 : ℝ) ≤ p := H.p0
  have hp0 : (0 : ℝ) < p := by linarith
  have hdi : S.d i < S.G := (H.dlt i).2
  have hX : (0 : ℝ) < (p : ℝ) ^ (S.G - S.d i) := pow_pos hp0 _
  have hdi0 : (0 : ℝ) < (p : ℝ) ^ (S.d i) := pow_pos hp0 _
  have hXn : (p : ℝ) ^ (S.G - S.d i) ≠ 0 := hX.ne'
  have hqn : (p : ℝ) ^ (S.d i) ≠ 0 := hdi0.ne'
  have hpn : (p : ℝ) ≠ 0 := hp0.ne'
  have hGi : (p : ℝ) ^ S.G = (p : ℝ) ^ (S.G - S.d i) * (p : ℝ) ^ (S.d i) := by
    rw [← pow_add, Nat.sub_add_cancel hdi.le]
  have hA : (p : ℝ) ^ (S.G - S.d i) * (S.A0 p : ℝ) ≤ (S.a : ℝ) / (p : ℝ) ^ (S.d i) := by
    have h1 := base_exponent_le_a p (by have := H.p5; omega) S H.errorNonneg
    calc (p : ℝ) ^ (S.G - S.d i) * (S.A0 p : ℝ)
        ≤ (p : ℝ) ^ (S.G - S.d i) * ((S.a : ℝ) / (p : ℝ) ^ S.G) :=
          mul_le_mul_of_nonneg_left h1 hX.le
      _ = (S.a : ℝ) / (p : ℝ) ^ (S.d i) := by
          rw [hGi]
          field_simp
  have hj : ∀ j : Fin s, (p : ℝ) ^ (S.G - S.d i) *
      (if (j : ℕ) < (i : ℕ) then (coarseA p S b j : ℝ) else 0) ≤
      (2 * b' / (p : ℝ) ^ (S.d i)) * (if (j : ℕ) < (i : ℕ) then (p : ℝ) ^ (S.d j) else 0) := by
    intro j
    split_ifs with hji
    · have hdj : S.d j < S.d i := H.dmono (show j < i from hji)
      have hdjG : S.d j ≤ S.G := (H.dlt j).2.le
      have hc := coarseA_mul p S b j
      have hb := H.top_degree_le_two_b j
      have hGj : (p : ℝ) ^ S.G = (p : ℝ) ^ (S.G - S.d j) * (p : ℝ) ^ (S.d j) := by
        rw [← pow_add, Nat.sub_add_cancel hdjG]
      have hpj : (0 : ℝ) ≤ (p : ℝ) ^ (S.d j) := by positivity
      have key : (p : ℝ) ^ (S.G - S.d i) * (coarseA p S b j : ℝ) * (p : ℝ) ^ (S.d i) ≤
          2 * b' * (p : ℝ) ^ (S.d j) := by
        have e1 : (p : ℝ) ^ (S.G - S.d i) * (coarseA p S b j : ℝ) * (p : ℝ) ^ (S.d i) =
            ((coarseA p S b j : ℝ) * (p : ℝ) ^ (S.G - S.d j)) * (p : ℝ) ^ (S.d j) := by
          calc (p : ℝ) ^ (S.G - S.d i) * (coarseA p S b j : ℝ) * (p : ℝ) ^ (S.d i)
              = (coarseA p S b j : ℝ) * ((p : ℝ) ^ (S.G - S.d i) * (p : ℝ) ^ (S.d i)) := by ring
            _ = (coarseA p S b j : ℝ) * ((p : ℝ) ^ (S.G - S.d j) * (p : ℝ) ^ (S.d j)) := by
                rw [← hGi, hGj]
            _ = ((coarseA p S b j : ℝ) * (p : ℝ) ^ (S.G - S.d j)) * (p : ℝ) ^ (S.d j) := by ring
        rw [e1]
        exact mul_le_mul_of_nonneg_right (hc.trans hb) hpj
      rw [div_mul_eq_mul_div, le_div_iff₀ hdi0]
      exact key
    · simp
  have hsum : (p : ℝ) ^ (S.G - S.d i) *
      (∑ j : Fin s, if (j : ℕ) < (i : ℕ) then (coarseA p S b j : ℝ) else 0) ≤
      (2 * b' / (p : ℝ) ^ (S.d i)) * (∑ j : Fin s, if (j : ℕ) < (i : ℕ) then (p : ℝ) ^ (S.d j) else 0) := by
    rw [Finset.mul_sum, Finset.mul_sum]
    exact Finset.sum_le_sum (fun j _ => hj j)
  have hK := mul_sum_pow_lt_le_pow_of_segHyp H (i : ℕ) i.2
  rw [Fin.eta] at hK
  have hb0 : 0 ≤ 2 * b' / (p : ℝ) ^ (S.d i) := by
    have := H.bpos
    positivity
  have hS : (∑ j : Fin s, if (j : ℕ) < (i : ℕ) then (p : ℝ) ^ (S.d j) else 0) ≤
      (p : ℝ) ^ (S.d i) / p := by
    rw [le_div_iff₀ hp0, mul_comm]
    exact hK
  have hT : (2 * b' / (p : ℝ) ^ (S.d i)) *
      (∑ j : Fin s, if (j : ℕ) < (i : ℕ) then (p : ℝ) ^ (S.d j) else 0) ≤ 2 * (b' / p) := by
    calc (2 * b' / (p : ℝ) ^ (S.d i)) *
          (∑ j : Fin s, if (j : ℕ) < (i : ℕ) then (p : ℝ) ^ (S.d j) else 0)
        ≤ (2 * b' / (p : ℝ) ^ (S.d i)) * ((p : ℝ) ^ (S.d i) / p) := mul_le_mul_of_nonneg_left hS hb0
      _ = 2 * (b' / p) := by
          field_simp
  have hc := cap_le p S b (i : ℕ)
  calc (p : ℝ) ^ (S.G - S.d i) * (cap p S b i : ℝ)
      ≤ (p : ℝ) ^ (S.G - S.d i) * ((S.A0 p : ℝ) +
          ∑ j : Fin s, if (j : ℕ) < (i : ℕ) then (coarseA p S b j : ℝ) else 0) :=
        mul_le_mul_of_nonneg_left hc hX.le
    _ = (p : ℝ) ^ (S.G - S.d i) * (S.A0 p : ℝ) + (p : ℝ) ^ (S.G - S.d i) *
          (∑ j : Fin s, if (j : ℕ) < (i : ℕ) then (coarseA p S b j : ℝ) else 0) := mul_add _ _ _
    _ ≤ (S.a : ℝ) / (p : ℝ) ^ (S.d i) + 2 * (b' / p) := add_le_add hA (hsum.trans hT)

def errTop (p r : ℕ) (S : SegData s) (b' : ℝ) : ℝ :=
  2 * (b' / p) + 2 * (S.La * b' / ((r : ℝ) + 1)) + 8 * (b' / (p : ℝ) ^ 2) + S.La * S.a / ((p : ℝ) * ((r : ℝ) + 1)) +
    2 * (S.La * b' / ((p : ℝ) * ((r : ℝ) + 1)))

theorem SegHyp.de0 (H : SegHyp p S b' de be aS Q) : 0 ≤ de := by
  linarith [H.be0, H.beLe]

theorem SegHyp.top_ord (H : SegHyp p S b' de be aS Q) {aTop : Fin s → ℕ} {b : SegBlock s r}
    (hK : Kept p r S aTop b) (i : Fin s) :
    (p : ℝ) ^ (S.G - S.d i) * (oEff S b i : ℝ) ≤
      min (S.bTop i : ℝ) (aS / (p : ℝ) ^ (S.d i)) + errTop p r S b' := by
  have hp5 := H.p0
  have hp0 : (0 : ℝ) < p := by linarith
  have hp1 : (1 : ℝ) ≤ p := by linarith
  have hb := H.bpos
  have hLa := H.La0
  have hde0 := H.de0
  have hde6 := H.de6
  have hbe0 := H.be0
  have hbeLe := H.beLe
  have hk : (0 : ℝ) < (r : ℝ) + 1 := by positivity
  have ha0 : (0 : ℝ) ≤ (S.a : ℝ) := Nat.cast_nonneg _
  have hP0 : 0 < (p : ℝ) ^ (S.G - S.d i) := by positivity
  have hx0 : 0 < (p : ℝ) ^ (S.d i) := by positivity
  have hxp : (p : ℝ) ≤ (p : ℝ) ^ (S.d i) := by
    calc (p : ℝ) = (p : ℝ) ^ 1 := (pow_one _).symm
      _ ≤ (p : ℝ) ^ (S.d i) := pow_le_pow_right₀ hp1 (H.dlt i).1
  have hcap := H.Pcap b i
  have hA := coarseA_mul p S b i
  have hB2 := H.top_degree_le_two_b i
  have hband := H.band (S.d i) (H.dodd i)
  have hab0 : 0 ≤ (S.a : ℝ) / b' := by positivity
  have hax : (S.a : ℝ) / (p : ℝ) ^ (S.d i) ≤ (S.a : ℝ) / p := div_le_div_of_nonneg_left ha0 hp0 hxp
  unfold errTop
  by_cases hs : (i : ℕ) < S.sigma
  · obtain ⟨-, -, -, hsum, -⟩ := hK.2.2.1 i hs
    have hlt := (H.sig i).mp hs
    have hlo : (p : ℝ) ^ (S.d i) < ((S.a : ℝ) / b') * (1 - 2 * de) := by
      by_contra hcon
      exact hband ⟨not_lt.mp hcon, by nlinarith⟩
    have hxb : (p : ℝ) ^ (S.d i) * b' < (S.a : ℝ) * (1 - 2 * de) := by
      have e : ((S.a : ℝ) / b') * (1 - 2 * de) = (S.a : ℝ) * (1 - 2 * de) / b' := by ring
      rw [e, lt_div_iff₀ hb] at hlo
      exact hlo
    have hbi : (S.bTop i : ℝ) ≤ aS / (p : ℝ) ^ (S.d i) := by
      rw [le_div_iff₀ hx0]
      have h1 : (S.bTop i : ℝ) * (p : ℝ) ^ (S.d i) ≤ (1 + be) * ((p : ℝ) ^ (S.d i) * b') := by
        have := mul_le_mul_of_nonneg_right (H.bT i).2 hx0.le
        linarith
      have h2 : (1 + be) * ((p : ℝ) ^ (S.d i) * b') ≤ (1 + be) * ((S.a : ℝ) * (1 - 2 * de)) :=
        mul_le_mul_of_nonneg_left hxb.le (by linarith)
      have h3 : (1 + be) * (1 - 2 * de) ≤ 1 := by nlinarith [mul_nonneg hbe0 hde0]
      have h4 : (1 + be) * ((S.a : ℝ) * (1 - 2 * de)) ≤ (S.a : ℝ) := by
        have := mul_le_mul_of_nonneg_left h3 ha0
        linarith
      linarith [H.aS]
    rw [min_eq_left hbi]
    have hoe : (oEff S b i : ℝ) = ((b.w i + b.sg i : ℕ) : ℝ) := by
      unfold oEff
      rw [if_pos hs]
    rw [hoe]
    have hm := mul_le_mul_of_nonneg_left hsum hP0.le
    have e1 : (p : ℝ) ^ (S.G - S.d i) * ((coarseA p S b i : ℝ) * (1 + 4 / (p : ℝ) ^ 2) +
        S.La * (cap p S b i : ℝ) / ((r : ℝ) + 1)) =
        ((coarseA p S b i : ℝ) * (p : ℝ) ^ (S.G - S.d i)) * (1 + 4 / (p : ℝ) ^ 2) +
        S.La / ((r : ℝ) + 1) * ((p : ℝ) ^ (S.G - S.d i) * (cap p S b i : ℝ)) := by ring
    rw [e1] at hm
    have h5 : ((coarseA p S b i : ℝ) * (p : ℝ) ^ (S.G - S.d i)) * (1 + 4 / (p : ℝ) ^ 2) ≤
        (S.bTop i : ℝ) + 8 * (b' / (p : ℝ) ^ 2) := by
      have h51 : ((coarseA p S b i : ℝ) * (p : ℝ) ^ (S.G - S.d i)) * (1 + 4 / (p : ℝ) ^ 2) ≤
          (S.bTop i : ℝ) * (1 + 4 / (p : ℝ) ^ 2) := mul_le_mul_of_nonneg_right hA (by positivity)
      have h52 : (S.bTop i : ℝ) * (4 / (p : ℝ) ^ 2) ≤ (2 * b') * (4 / (p : ℝ) ^ 2) :=
        mul_le_mul_of_nonneg_right hB2 (by positivity)
      have e : (2 * b') * (4 / (p : ℝ) ^ 2) = 8 * (b' / (p : ℝ) ^ 2) := by ring
      linarith
    have h6 : S.La / ((r : ℝ) + 1) * ((p : ℝ) ^ (S.G - S.d i) * (cap p S b i : ℝ)) ≤
        S.La * S.a / ((p : ℝ) * ((r : ℝ) + 1)) + 2 * (S.La * b' / ((p : ℝ) * ((r : ℝ) + 1))) := by
      have h61 : S.La / ((r : ℝ) + 1) * ((p : ℝ) ^ (S.G - S.d i) * (cap p S b i : ℝ)) ≤
          S.La / ((r : ℝ) + 1) * ((S.a : ℝ) / p + 2 * (b' / p)) :=
        mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      have e : S.La / ((r : ℝ) + 1) * ((S.a : ℝ) / p + 2 * (b' / p)) =
          S.La * S.a / ((p : ℝ) * ((r : ℝ) + 1)) + 2 * (S.La * b' / ((p : ℝ) * ((r : ℝ) + 1))) := by
        field_simp
      linarith
    have n1 : 0 ≤ b' / (p : ℝ) := by positivity
    have n2 : 0 ≤ S.La * b' / ((r : ℝ) + 1) := by positivity
    linarith
  · obtain ⟨-, hoc, -, -⟩ := hK.2.1 i (not_lt.mp hs)
    have hge : (S.a : ℝ) / b' ≤ (p : ℝ) ^ (S.d i) := not_lt.mp (fun h => hs ((H.sig i).mpr h))
    have hhi : ((S.a : ℝ) / b') * (1 + 2 * de) < (p : ℝ) ^ (S.d i) := by
      by_contra hcon
      exact hband ⟨by nlinarith, not_lt.mp hcon⟩
    have hxb : (S.a : ℝ) * (1 + 2 * de) < (p : ℝ) ^ (S.d i) * b' := by
      have e : ((S.a : ℝ) / b') * (1 + 2 * de) = (S.a : ℝ) * (1 + 2 * de) / b' := by ring
      rw [e, div_lt_iff₀ hb] at hhi
      exact hhi
    have hmin : (S.a : ℝ) / (p : ℝ) ^ (S.d i) ≤ min (S.bTop i : ℝ) (aS / (p : ℝ) ^ (S.d i)) := by
      apply le_min
      · rw [div_le_iff₀ hx0]
        have h1 : (1 - be) * ((p : ℝ) ^ (S.d i) * b') ≤ (S.bTop i : ℝ) * (p : ℝ) ^ (S.d i) := by
          have := mul_le_mul_of_nonneg_right (H.bT i).1 hx0.le
          linarith
        have h2 : (1 - be) * ((S.a : ℝ) * (1 + 2 * de)) ≤ (1 - be) * ((p : ℝ) ^ (S.d i) * b') :=
          mul_le_mul_of_nonneg_left hxb.le (by linarith)
        have h3 : 1 ≤ (1 - be) * (1 + 2 * de) := by nlinarith [mul_nonneg hbe0 hde0, mul_nonneg hde0 hde0]
        have h4 : (S.a : ℝ) ≤ (1 - be) * ((S.a : ℝ) * (1 + 2 * de)) := by
          have := mul_le_mul_of_nonneg_left h3 ha0
          linarith
        linarith
      · exact div_le_div_of_nonneg_right H.aS hx0.le
    have hoe : (oEff S b i : ℝ) = (b.o i : ℝ) := by
      unfold oEff
      rw [if_neg hs]
    rw [hoe]
    have hm := mul_le_mul_of_nonneg_left hoc hP0.le
    have e1 : (p : ℝ) ^ (S.G - S.d i) * ((cap p S b i : ℝ) + S.La * (coarseA p S b i : ℝ) / ((r : ℝ) + 1)) =
        (p : ℝ) ^ (S.G - S.d i) * (cap p S b i : ℝ) +
        S.La / ((r : ℝ) + 1) * ((coarseA p S b i : ℝ) * (p : ℝ) ^ (S.G - S.d i)) := by ring
    rw [e1] at hm
    have h6 : S.La / ((r : ℝ) + 1) * ((coarseA p S b i : ℝ) * (p : ℝ) ^ (S.G - S.d i)) ≤
        2 * (S.La * b' / ((r : ℝ) + 1)) := by
      have h61 : S.La / ((r : ℝ) + 1) * ((coarseA p S b i : ℝ) * (p : ℝ) ^ (S.G - S.d i)) ≤
          S.La / ((r : ℝ) + 1) * (2 * b') := mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      have e : S.La / ((r : ℝ) + 1) * (2 * b') = 2 * (S.La * b' / ((r : ℝ) + 1)) := by ring
      linarith
    have n1 : 0 ≤ b' / (p : ℝ) ^ 2 := by positivity
    have n2 : 0 ≤ S.La * S.a / ((p : ℝ) * ((r : ℝ) + 1)) := by positivity
    have n3 : 0 ≤ S.La * b' / ((p : ℝ) * ((r : ℝ) + 1)) := by positivity
    linarith

def Rerr (p r : ℕ) (S : SegData s) (b' Q : ℝ) : ℝ :=
  S.a / (p : ℝ) ^ 2 + b' / p + S.La * S.a / ((p : ℝ) * ((r : ℝ) + 1)) + S.La * b' / ((r : ℝ) + 1) + ((r : ℝ) + 1) * Q

theorem SegHyp.dig (H : SegHyp p S b' de be aS Q) {aTop : Fin s → ℕ} {b : SegBlock s r}
    (hK : Kept p r S aTop b) (i : Fin s) :
    (((∑ c : Fin (r + 1), if (c : ℕ) = 0 then 0 else b.rz i c) + b.ry i 0 : ℕ) : ℝ) ≤ 2 * (((r : ℝ) + 1) * Q) := by
  unfold Kept DigitsOK at hK
  have hD := hK.1.1
  have hP : ((S.P p i : ℕ) : ℝ) ≤ Q := by
    unfold SegData.P
    push_cast
    calc (p : ℝ) ^ (S.G - S.d i) ≤ (p : ℝ) ^ S.G :=
          pow_le_pow_right₀ (by linarith [H.p0]) (Nat.sub_le _ _)
      _ ≤ Q := H.Q
  set T := (∑ c : Fin (r + 1), if (c : ℕ) = 0 then 0 else b.rz i c) with hT
  have h1 : T ≤ (r + 1) * S.P p i := by
    calc T ≤ ∑ _c : Fin (r + 1), S.P p i := by
          apply Finset.sum_le_sum
          intro c _
          split_ifs
          · exact Nat.zero_le _
          · exact (hD i c).1.le
      _ = (r + 1) * S.P p i := by simp
  have h2 : b.ry i 0 ≤ S.P p i := (hD i 0).2.le
  have h1r : (T : ℝ) ≤ ((r : ℝ) + 1) * (S.P p i : ℝ) := by exact_mod_cast h1
  have h2r : (b.ry i 0 : ℝ) ≤ (S.P p i : ℝ) := by exact_mod_cast h2
  have hQ0 : (0 : ℝ) ≤ Q := (Nat.cast_nonneg _).trans hP
  have hr : (0 : ℝ) ≤ r := Nat.cast_nonneg r
  have h3 : ((r : ℝ) + 1) * (S.P p i : ℝ) ≤ ((r : ℝ) + 1) * Q :=
    mul_le_mul_of_nonneg_left hP (by linarith)
  have h4 : 0 ≤ (r : ℝ) * Q := mul_nonneg hr hQ0
  push_cast
  linarith

theorem SegHyp.oplus (H : SegHyp p S b' de be aS Q) (b : SegBlock s r) :
    Oplus p r S b ≤ S.a / (p : ℝ) ^ 2 + (s : ℝ) * (2 * (b' / p)) +
      (S.La / ((r : ℝ) + 1) + 4 / (p : ℝ) ^ 2) * ((s : ℝ) * (2 * (S.a : ℝ) / p)) + 2 * (S.La * b' / ((r : ℝ) + 1)) := by
  have hp5 : (5 : ℝ) ≤ p := H.p0
  have hp0 : (0 : ℝ) < p := by linarith
  have hb0 := H.bpos
  have hLa := H.La0
  have hr0 : (0 : ℝ) < (r : ℝ) + 1 := by positivity
  have ha0 : (0 : ℝ) ≤ (S.a : ℝ) := Nat.cast_nonneg _
  have hPi : ∀ i : Fin s, (p : ℝ) ≤ (S.P p i : ℝ) := by
    intro i
    have h1 : 1 ≤ S.G - S.d i := by
      have := (H.dlt i).2
      omega
    unfold SegData.P
    push_cast
    calc (p : ℝ) = (p : ℝ) ^ 1 := (pow_one _).symm
      _ ≤ (p : ℝ) ^ (S.G - S.d i) := pow_le_pow_right₀ (by linarith) h1
  have hcoarse : ∀ i : Fin s, (coarseA p S b i : ℝ) ≤ 2 * (b' / p) := by
    intro i
    have hc := coarseA_mul p S b i
    have hb := H.top_degree_le_two_b i
    have hP := hPi i
    have hP' : (S.P p i : ℝ) = (p : ℝ) ^ (S.G - S.d i) := by simp [SegData.P]
    rw [← hP'] at hc
    have hca : (0 : ℝ) ≤ (coarseA p S b i : ℝ) := Nat.cast_nonneg _
    rw [mul_div_assoc', le_div_iff₀ hp0]
    nlinarith [mul_le_mul_of_nonneg_left hP hca]
  have hcap : (cap p S b s : ℝ) ≤ (S.a : ℝ) / (p : ℝ) ^ 2 + (s : ℝ) * (2 * (b' / p)) := by
    have h1 := cap_le p S b s
    have h2 : (S.A0 p : ℝ) ≤ (S.a : ℝ) / (p : ℝ) ^ 2 := by
      have h3 := base_exponent_le_a p (by have := H.p5; omega) S H.errorNonneg
      have hq : (p : ℝ) ^ 2 ≤ (p : ℝ) ^ S.G := pow_le_pow_right₀ (by linarith) H.G2
      have hq0 : (0 : ℝ) < (p : ℝ) ^ 2 := by positivity
      exact h3.trans (div_le_div_of_nonneg_left ha0 hq0 hq)
    have h4 : (∑ i : Fin s, if (i : ℕ) < s then (coarseA p S b i : ℝ) else 0) ≤
        (s : ℝ) * (2 * (b' / p)) := by
      calc (∑ i : Fin s, if (i : ℕ) < s then (coarseA p S b i : ℝ) else 0)
          ≤ ∑ _i : Fin s, 2 * (b' / p) := by
            apply Finset.sum_le_sum
            intro i _
            rw [if_pos i.2]
            exact hcoarse i
        _ = (s : ℝ) * (2 * (b' / p)) := by simp
    linarith
  have hsumP : (∑ i, 2 * (S.a : ℝ) / (S.P p i : ℝ)) ≤ (s : ℝ) * (2 * (S.a : ℝ) / p) := by
    calc (∑ i, 2 * (S.a : ℝ) / (S.P p i : ℝ)) ≤ ∑ _i : Fin s, 2 * (S.a : ℝ) / p := by
          apply Finset.sum_le_sum
          intro i _
          exact div_le_div_of_nonneg_left (by positivity) hp0 (hPi i)
      _ = (s : ℝ) * (2 * (S.a : ℝ) / p) := by simp
  have hcoef : 0 ≤ S.La / ((r : ℝ) + 1) + 4 / (p : ℝ) ^ 2 :=
    add_nonneg (div_nonneg hLa hr0.le) (by positivity)
  have hbP : (S.bPlus : ℝ) ≤ 2 * b' := by
    have h1 := H.bP
    have hbe : be ≤ 1 := by linarith [H.beLe, H.de6, H.be0]
    nlinarith [mul_le_mul_of_nonneg_left hbe hb0.le]
  have h3 : S.La * (S.bPlus : ℝ) / ((r : ℝ) + 1) ≤ 2 * (S.La * b' / ((r : ℝ) + 1)) := by
    have hnum : S.La * (S.bPlus : ℝ) ≤ 2 * (S.La * b') := by
      nlinarith [mul_le_mul_of_nonneg_left hbP hLa]
    have hinv : 0 ≤ ((r : ℝ) + 1)⁻¹ := inv_nonneg.mpr hr0.le
    simp only [div_eq_mul_inv]
    nlinarith [mul_le_mul_of_nonneg_right hnum hinv]
  have h2 : (S.La / ((r : ℝ) + 1) + 4 / (p : ℝ) ^ 2) * (∑ i, 2 * (S.a : ℝ) / (S.P p i : ℝ)) ≤
      (S.La / ((r : ℝ) + 1) + 4 / (p : ℝ) ^ 2) * ((s : ℝ) * (2 * (S.a : ℝ) / p)) :=
    mul_le_mul_of_nonneg_left hsumP hcoef
  unfold Oplus
  linarith [hcap, h2, h3]

theorem SegHyp.seg_ord (H : SegHyp p S b' de be aS Q) {aTop : Fin s → ℕ} {b : SegBlock s r}
    (hK : Kept p r S aTop b) :
    (blockOrd p S b : ℝ) ≤ (∑ i : Fin s, min (S.bTop i : ℝ) (aS / (p : ℝ) ^ (S.d i))) +
      ((s : ℝ) + 1) * (30 * Rerr p r S b' Q) := by
  have hp5 : (5 : ℝ) ≤ p := H.p0
  have hp0 : (0 : ℝ) < p := by linarith
  have hb0 := H.bpos
  have hLa := H.La0
  have hr0 : (0 : ℝ) < (r : ℝ) + 1 := by positivity
  have ha0 : (0 : ℝ) ≤ (S.a : ℝ) := Nat.cast_nonneg _
  have hs0 : (0 : ℝ) ≤ (s : ℝ) := Nat.cast_nonneg _
  have hQ0 : 0 ≤ Q := by
    have h1 := H.Q
    have h2 : (0 : ℝ) ≤ (p : ℝ) ^ S.G := by positivity
    linarith
  have hinv : (p : ℝ)⁻¹ ≤ 1 / 5 := by
    rw [inv_eq_one_div]
    exact one_div_le_one_div_of_le (by norm_num) hp5
  have hA0 : 0 ≤ (S.a : ℝ) / (p : ℝ) ^ 2 := by positivity
  have hB0 : 0 ≤ b' / p := div_nonneg hb0.le hp0.le
  have hC0 : 0 ≤ S.La * S.a / ((p : ℝ) * ((r : ℝ) + 1)) :=
    div_nonneg (mul_nonneg hLa ha0) (mul_nonneg hp0.le hr0.le)
  have hD0 : 0 ≤ S.La * b' / ((r : ℝ) + 1) := div_nonneg (mul_nonneg hLa hb0.le) hr0.le
  have hE0 : 0 ≤ ((r : ℝ) + 1) * Q := mul_nonneg hr0.le hQ0
  have i1 : b' / (p : ℝ) ^ 2 = (b' / p) * (p : ℝ)⁻¹ := by
    simp only [div_eq_mul_inv, sq, mul_inv]
    ring
  have i2 : S.La * b' / ((p : ℝ) * ((r : ℝ) + 1)) = (S.La * b' / ((r : ℝ) + 1)) * (p : ℝ)⁻¹ := by
    simp only [div_eq_mul_inv, mul_inv]
    ring
  have j1 := mul_le_mul_of_nonneg_left hinv hB0
  have j2 := mul_le_mul_of_nonneg_left hinv hD0
  have hEt : errTop p r S b' ≤ 4 * (b' / p) + S.La * S.a / ((p : ℝ) * ((r : ℝ) + 1)) +
      4 * (S.La * b' / ((r : ℝ) + 1)) := by
    unfold errTop
    rw [i1, i2]
    linarith
  have i3 : (S.La / ((r : ℝ) + 1) + 4 / (p : ℝ) ^ 2) * ((s : ℝ) * (2 * (S.a : ℝ) / p)) =
      (s : ℝ) * (2 * (S.La * S.a / ((p : ℝ) * ((r : ℝ) + 1))) +
        8 * (((S.a : ℝ) / (p : ℝ) ^ 2) * (p : ℝ)⁻¹)) := by
    simp only [div_eq_mul_inv, sq, mul_inv]
    ring
  have j3 := mul_le_mul_of_nonneg_left hinv hA0
  have k3a : 2 * (S.La * S.a / ((p : ℝ) * ((r : ℝ) + 1))) +
      8 * (((S.a : ℝ) / (p : ℝ) ^ 2) * (p : ℝ)⁻¹) ≤
      2 * (S.La * S.a / ((p : ℝ) * ((r : ℝ) + 1))) + 2 * ((S.a : ℝ) / (p : ℝ) ^ 2) := by
    linarith
  have k3 := mul_le_mul_of_nonneg_left k3a hs0
  have hOB := H.oplus b
  rw [i3] at hOB
  have hi : ∀ i : Fin s, ((S.P p i * oEff S b i + (∑ c : Fin (r + 1), if (c : ℕ) = 0 then 0 else b.rz i c) +
      b.ry i 0 : ℕ) : ℝ) ≤ min (S.bTop i : ℝ) (aS / (p : ℝ) ^ (S.d i)) +
      (errTop p r S b' + 2 * (((r : ℝ) + 1) * Q)) := by
    intro i
    have h1 := H.top_ord hK i
    have h2 := H.dig hK i
    have hP' : ((S.P p i : ℕ) : ℝ) = (p : ℝ) ^ (S.G - S.d i) := by simp [SegData.P]
    have e : ((S.P p i * oEff S b i + (∑ c : Fin (r + 1), if (c : ℕ) = 0 then 0 else b.rz i c) +
        b.ry i 0 : ℕ) : ℝ) = (p : ℝ) ^ (S.G - S.d i) * (oEff S b i : ℝ) +
        (((∑ c : Fin (r + 1), if (c : ℕ) = 0 then 0 else b.rz i c) + b.ry i 0 : ℕ) : ℝ) := by
      rw [← hP', add_assoc, Nat.cast_add, Nat.cast_mul]
    rw [e]
    linarith
  have hsum := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hi i)
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul] at hsum
  have hO : (b.oPlus : ℝ) ≤ Oplus p r S b := by
    have h := hK
    unfold Kept at h
    exact h.2.2.2
  have hsE := mul_le_mul_of_nonneg_left hEt hs0
  have m1 := mul_nonneg hs0 hA0
  have m2 := mul_nonneg hs0 hB0
  have m3 := mul_nonneg hs0 hC0
  have m4 := mul_nonneg hs0 hD0
  have m5 := mul_nonneg hs0 hE0
  unfold blockOrd Rerr
  rw [Nat.cast_add, Nat.cast_sum]
  linarith [hsum, hO, hOB, k3, hsE, hA0, hB0, hC0, hD0, hE0, m1, m2, m3, m4, m5]

theorem segHyp_of {C0 Cde CE1 CE2 H : ℝ} {X : Loc} (St : Std C0 Cde CE1 CE2 H X) (j : Fin (numSeg X.TT)) :
    SegHyp X.p (X.seg C0 CE1 CE2 j) X.b' (X.de C0 Cde) (_root_.Formalism.MainNotions.ColumnSystems.Pf.be X C0) (X.aT (segStart X.TT j) : ℝ) X.Q where
  p5 := St.p5
  G2 := by
    show 2 ≤ segG X.TT j
    have h1 := segG_even St.nEven X.TT j
    have h2 : 0 < segG X.TT j := by
      unfold segG
      split_ifs with h
      · have := St.n2
        omega
      · omega
    rw [Nat.even_iff] at h1
    omega
  dlt := dist_pos_lt X.TT j
  dodd := dist_odd St.nEven X.TT j
  dmono := dist_strictMono X.TT j
  sig := fun i => sigma_iff X.p (by have := St.p5; omega) X.TT X.bT X.a X.b' X.Y _ _ j i
  bpos := St.bpos
  La0 := by
    show 0 ≤ X.La C0
    linarith [St.La1]
  errorNonneg := St.E0nn
  bT := fun i => St.winB _ (pos_mem X.TT j i).1
  bP := (St.winB _ (next_mem X.TT j).1).2
  be0 := St.be0
  beLe := by
    have h1 := St.beLe
    have h2 := St.La1
    have hk : 0 < X.k := by
      unfold Loc.k
      positivity
    have h3 : 0 ≤ 18 * (X.N1 : ℝ) * X.La C0 / X.k := by positivity
    linarith
  de6 := St.de6
  band := St.band
  aS := (St.winA _ (start_mem X.TT j).1).1
  sp := by
    have h1 : (segS X.TT j : ℝ) ≤ (X.N1 : ℝ) := by exact_mod_cast (St.segB j).2
    have h2 := St.N1k
    have h3 := St.pk
    have h4 := St.Y1
    have h5 : (0 : ℝ) ≤ (X.N1 : ℝ) := Nat.cast_nonneg _
    have hk1 : 1 ≤ X.k := by linarith
    have h6 : X.k ≤ X.k ^ 2 := by nlinarith
    have h7 : X.k ^ 2 * 1 ≤ X.k ^ 2 * X.Y ^ 2 := mul_le_mul_of_nonneg_left (by nlinarith) (by positivity)
    linarith
  Q := by
    show (X.p : ℝ) ^ (segG X.TT j) ≤ (X.p : ℝ) ^ X.G'
    have hp : (1 : ℝ) ≤ (X.p : ℝ) := by
      have := St.p5
      exact_mod_cast (by omega : 1 ≤ X.p)
    exact pow_le_pow_right₀ hp (St.segB j).1

theorem ord_all {C0 Cde CE1 CE2 H Ct : ℝ} {X : Loc} (St : Std C0 Cde CE1 CE2 H X) (hCt : 30 ≤ Ct)
    (bs : ∀ j : Fin (numSeg X.TT), SegBlock (segS X.TT j) X.m)
    (hK : ∀ j, Kept X.p X.m (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) (bs j)) :
    ((∑ j, blockOrd X.p (X.seg C0 CE1 CE2 j) (bs j) : ℕ) : ℝ) ≤ X.t0 C0 Ct := by
  obtain ⟨R, hRdef⟩ : ∃ R : ℝ, R = (X.a : ℝ) / (X.p : ℝ) ^ 2 + X.b' / X.p +
      X.La C0 * X.a / ((X.p : ℝ) * ((X.m : ℝ) + 1)) + X.La C0 * X.b' / ((X.m : ℝ) + 1) + ((X.m : ℝ) + 1) * X.Q :=
    ⟨_, rfl⟩
  have hp0 : (0 : ℝ) < (X.p : ℝ) := by
    have := St.p5
    exact_mod_cast (by omega : 0 < X.p)
  have hLa : 0 ≤ X.La C0 := by linarith [St.La1]
  have hb := St.bpos
  have hQ0 : 0 ≤ X.Q := by
    unfold Loc.Q
    positivity
  have hR0 : 0 ≤ R := by
    rw [hRdef]
    positivity
  have hseg : ∀ j, (blockOrd X.p (X.seg C0 CE1 CE2 j) (bs j) : ℝ) ≤
      (∑ i : Fin (segS X.TT j), min (X.bT (segPos X.TT j i) : ℝ)
        ((X.aT (segStart X.TT j) : ℝ) / (X.p : ℝ) ^ ((segDists X.TT j).get i))) +
      ((segS X.TT j : ℝ) + 1) * (30 * R) := by
    intro j
    have h := (segHyp_of St j).seg_ord (hK j)
    rw [hRdef]
    exact h
  have h1 : ((∑ j, blockOrd X.p (X.seg C0 CE1 CE2 j) (bs j) : ℕ) : ℝ) ≤
      ∑ j, ((∑ i : Fin (segS X.TT j), min (X.bT (segPos X.TT j i) : ℝ)
        ((X.aT (segStart X.TT j) : ℝ) / (X.p : ℝ) ^ ((segDists X.TT j).get i))) +
      ((segS X.TT j : ℝ) + 1) * (30 * R)) := by
    push_cast
    exact Finset.sum_le_sum fun j _ => hseg j
  have h2 : (∑ j : Fin (numSeg X.TT), ((segS X.TT j : ℝ) + 1)) ≤ (X.TT.card : ℝ) := by
    have h := sum_segS X.TT St.seg2
    have e : (∑ j : Fin (numSeg X.TT), ((segS X.TT j : ℝ) + 1)) = (((∑ j, segS X.TT j) + numSeg X.TT : ℕ) : ℝ) := by
      push_cast
      rw [Finset.sum_add_distrib]
      simp
    rw [e]
    exact_mod_cast h
  rw [Finset.sum_add_distrib, ← Finset.sum_mul] at h1
  refine le_trans h1 ?_
  unfold Loc.t0 t0G4
  apply add_le_add le_rfl
  have hc0 : (0 : ℝ) ≤ (X.c : ℝ) := Nat.cast_nonneg _
  have hQc : 0 ≤ X.Q * X.c := mul_nonneg hQ0 hc0
  have hcard : (0 : ℝ) ≤ (X.TT.card : ℝ) := Nat.cast_nonneg _
  have a1 : (∑ j : Fin (numSeg X.TT), ((segS X.TT j : ℝ) + 1)) * (30 * R) ≤ (X.TT.card : ℝ) * (30 * R) :=
    mul_le_mul_of_nonneg_right h2 (by positivity)
  have a3 : 30 * R ≤ Ct * (R + X.Q * X.c) := by
    have := mul_le_mul_of_nonneg_right hCt hR0
    have : 0 ≤ Ct * (X.Q * X.c) := mul_nonneg (by linarith) hQc
    linarith
  have a2 : (X.TT.card : ℝ) * (30 * R) ≤ (X.TT.card : ℝ) * (Ct * (R + X.Q * X.c)) :=
    mul_le_mul_of_nonneg_left a3 hcard
  refine le_trans (le_trans a1 a2) (le_of_eq ?_)
  rw [hRdef]
  push_cast
  ring

theorem restAlt3 (D : Formalism.BasicNotions.D7) : RemainderSegmentBoundThird D := by
  apply TransportedAlt.of_explicit (fun _ => 1) (fun _ _ => 1) (fun Cc _ CE1 CE2 _ => T2 CE1 CE2 Cc 1)
  intro C0 CYb Cde Ck CD Cb CE1 CE2 Cm Cc hCc hC0 _ h1 h2 _ _ _ _ _ _ _ _ _ t1 t2 t3 t4 t5
  refine ⟨30, by norm_num, fun Ct hCt => ?_⟩
  intro X hD hI hc bs hK
  have St : Std C0 Cde CE1 CE2 1 X := std_of hCc hC0 h1 h2 le_rfl t1 t2 t3 t4 t5 hD hI hc
  exact ord_all St hCt bs hK

end Formalism.MainNotions.ColumnSystems.Pf
