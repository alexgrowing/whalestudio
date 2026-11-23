import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.RealLeviDescent.MuQMemHarmSet

open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD
open Finset

namespace GlobalTheory.CompanionTheory.ConeSecondWeights

variable {n : ℕ}

def sgn0 (a b : Fin n) : ℝ := if a < b then 1 else if b < a then -1 else 0

def triT (a b c : Fin n) : ℝ := if a = b ∧ b = c then 0 else 1

def tri (e : Fin n → Fin n → ℝ) (a b c : Fin n) : ℝ :=
  e a b * e a c + e b a * e b c + e c a * e c b

theorem tri_sum (e : Fin n → Fin n → ℝ) :
    ∑ a, ∑ b, ∑ c, tri e a b c = 3 * ∑ a, (∑ b, e a b) ^ 2 := by
  have h1 : ∑ a, (∑ b, e a b) ^ 2 = ∑ a, ∑ b, ∑ c, e a b * e a c := by
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [sq, Finset.sum_mul_sum]
  have h2 : ∑ a, ∑ b, ∑ c, e b a * e b c = ∑ a, ∑ b, ∑ c, e a b * e a c := Finset.sum_comm
  have h3 : ∑ a, ∑ b, ∑ c, e c a * e c b = ∑ a, ∑ b, ∑ c, e a b * e a c :=
    (Finset.sum_congr rfl fun a _ => Finset.sum_comm).trans Finset.sum_comm
  unfold tri
  simp only [Finset.sum_add_distrib]
  rw [h1, h2, h3]
  ring

theorem tri_le (e : Fin n → Fin n → ℝ) (h0 : ∀ a, e a a = 0) (ha : ∀ a b, e b a = - e a b)
    (hs : ∀ a b, a ≠ b → e a b = 1 ∨ e a b = -1) (a b c : Fin n) : tri e a b c ≤ triT a b c := by
  unfold tri triT
  rw [ha a b, ha a c, ha b c]
  by_cases hab : a = b
  · subst hab
    by_cases hac : a = c
    · subst hac
      simp [h0]
    · have hn : ¬ (a = a ∧ a = c) := fun h => hac h.2
      rw [if_neg hn, h0 a]
      rcases hs a c hac with h | h <;> rw [h] <;> norm_num
  · have hn : ¬ (a = b ∧ b = c) := fun h => hab h.1
    rw [if_neg hn]
    by_cases hbc : b = c
    · subst hbc
      rw [h0 b]
      rcases hs a b hab with h | h <;> rw [h] <;> norm_num
    · by_cases hac : a = c
      · subst hac
        rw [h0 a, ha a b]
        rcases hs a b hab with h | h <;> rw [h] <;> norm_num
      · rcases hs a b hab with h | h <;> rcases hs b c hbc with h' | h' <;>
          rcases hs a c hac with h'' | h'' <;> rw [h, h', h''] <;> norm_num

theorem cone_sign_self (a : Fin n) : sgn0 a a = 0 := by simp [sgn0]

theorem cone_sign_antisymmetric (a b : Fin n) : sgn0 b a = - sgn0 a b := by
  unfold sgn0
  rcases lt_trichotomy a b with h | h | h
  · simp [h, h.not_gt]
  · simp [h]
  · simp [h, h.not_gt]

theorem tri_sgn (a b c : Fin n) : tri sgn0 a b c = triT a b c := by
  unfold tri triT sgn0
  rcases lt_trichotomy a b with h1 | h1 | h1 <;> rcases lt_trichotomy b c with h2 | h2 | h2 <;>
    rcases lt_trichotomy a c with h3 | h3 | h3 <;>
    first
    | (exfalso; order)
    | (subst_vars; simp [*, ne_of_lt, ne_of_gt, not_lt_of_gt, lt_asymm]; done)
    | (subst_vars; simp [*, ne_of_lt, ne_of_gt, not_lt_of_gt, lt_asymm]; norm_num; done)

theorem sum_sgn (a : Fin n) : ∑ b, sgn0 a b = 2 * rhoV n a := by
  have h : ∀ b, sgn0 a b = (if a < b then (1:ℝ) else 0) - (if b < a then (1:ℝ) else 0) := by
    intro b
    unfold sgn0
    rcases lt_trichotomy a b with h | h | h
    · simp [h, h.not_gt]
    · simp [h]
    · simp [h, h.not_gt]
  simp only [h, Finset.sum_sub_distrib, Finset.sum_boole]
  have c1 : ((univ.filter fun b => a < b).card : ℝ) = (n : ℝ) - 1 - (a : ℕ) := by
    have : (univ.filter fun b => a < b) = Finset.Ioi a := by ext; simp
    rw [this, Fin.card_Ioi]
    have := a.isLt
    rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
    push_cast; ring
  have c2 : ((univ.filter fun b => b < a).card : ℝ) = (a : ℕ) := by
    have : (univ.filter fun b => b < a) = Finset.Iio a := by ext; simp
    rw [this, Fin.card_Iio]
  rw [c1, c2]
  unfold rhoV
  ring

def sgnB (B : Finset (Fin n × Fin n)) (a b : Fin n) : ℝ :=
  sgn0 a b - 2 * ((if (a, b) ∈ B then 1 else 0) - (if (b, a) ∈ B then 1 else 0))

theorem sgnB_self (B : Finset (Fin n × Fin n)) (a : Fin n) : sgnB B a a = 0 := by
  simp [sgnB, cone_sign_self]

theorem sgnB_anti (B : Finset (Fin n × Fin n)) (a b : Fin n) : sgnB B b a = - sgnB B a b := by
  unfold sgnB
  rw [cone_sign_antisymmetric a b]
  ring

theorem sgnB_sign {B : Finset (Fin n × Fin n)} (hB : ∀ p ∈ B, p.1 < p.2) (a b : Fin n) (hab : a ≠ b) :
    sgnB B a b = 1 ∨ sgnB B a b = -1 := by
  unfold sgnB sgn0
  rcases lt_or_gt_of_ne hab with h | h
  · have hn : (b, a) ∉ B := fun hm => absurd (hB _ hm) (not_lt_of_gt h)
    by_cases hm : (a, b) ∈ B <;> simp [h, hn, hm] <;> norm_num
  · have hn : (a, b) ∉ B := fun hm => absurd (hB _ hm) (not_lt_of_gt h)
    by_cases hm : (b, a) ∈ B <;> simp [h, h.not_gt, hn, hm] <;> norm_num

theorem card_fst (B : Finset (Fin n × Fin n)) (a : Fin n) :
    (B.filter fun p => p.1 = a).card = (univ.filter fun b => (a, b) ∈ B).card := by
  refine Finset.card_bij (fun p _ => p.2) ?_ ?_ ?_
  · intro p hp
    obtain ⟨h1, h2⟩ := Finset.mem_filter.1 hp
    refine Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_⟩
    rw [← h2]
    exact h1
  · intro p hp q hq h
    exact Prod.ext (((Finset.mem_filter.1 hp).2).trans ((Finset.mem_filter.1 hq).2).symm) h
  · intro b hb
    exact ⟨(a, b), Finset.mem_filter.2 ⟨(Finset.mem_filter.1 hb).2, rfl⟩, rfl⟩

theorem card_snd (B : Finset (Fin n × Fin n)) (a : Fin n) :
    (B.filter fun p => p.2 = a).card = (univ.filter fun b => (b, a) ∈ B).card := by
  refine Finset.card_bij (fun p _ => p.1) ?_ ?_ ?_
  · intro p hp
    obtain ⟨h1, h2⟩ := Finset.mem_filter.1 hp
    refine Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_⟩
    rw [← h2]
    exact h1
  · intro p hp q hq h
    exact Prod.ext h (((Finset.mem_filter.1 hp).2).trans ((Finset.mem_filter.1 hq).2).symm)
  · intro b hb
    exact ⟨(b, a), Finset.mem_filter.2 ⟨(Finset.mem_filter.1 hb).2, rfl⟩, rfl⟩

theorem sum_sgnB (B : Finset (Fin n × Fin n)) (a : Fin n) :
    ∑ b, sgnB B a b = 2 * (rhoV n a - wtB B a) := by
  unfold sgnB
  rw [Finset.sum_sub_distrib, sum_sgn, ← Finset.mul_sum, Finset.sum_sub_distrib, Finset.sum_boole,
    Finset.sum_boole]
  unfold wtB
  rw [card_fst, card_snd]
  ring

theorem nsq_rho_sub_le {B : Finset (Fin n × Fin n)} (hB : ∀ p ∈ B, p.1 < p.2) :
    nsq (rhoV n - wtB B) ≤ nsq (rhoV n) := by
  have h : ∑ a, ∑ b, ∑ c, tri (sgnB B) a b c ≤ ∑ a, ∑ b, ∑ c, tri sgn0 a b c :=
    Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ => Finset.sum_le_sum fun c _ => by
      rw [tri_sgn]
      exact tri_le _ (sgnB_self B) (sgnB_anti B) (sgnB_sign hB) a b c
  rw [tri_sum, tri_sum] at h
  simp only [sum_sgnB, sum_sgn, mul_pow, ← Finset.mul_sum] at h
  unfold nsq
  simp only [Pi.sub_apply]
  linarith

theorem dot_wtB (f : Fin n → ℝ) (B : Finset (Fin n × Fin n)) :
    ∑ c, f c * wtB B c = ∑ p ∈ B, (f p.1 - f p.2) := by
  have h : ∀ c, wtB B c = ∑ p ∈ B, ((if p.1 = c then (1:ℝ) else 0) - (if p.2 = c then (1:ℝ) else 0)) := by
    intro c
    rw [Finset.sum_sub_distrib, Finset.sum_boole, Finset.sum_boole]
    rfl
  simp only [h, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun p _ => ?_
  simp [mul_sub, Finset.sum_sub_distrib]

theorem dot_cone (f : Fin n → ℝ) (c : Fin n → Fin n → ℕ) (Q : Fin n → ℝ)
    (hQ : ∀ x, Q x = ∑ a, ∑ b, (c a b : ℝ) * ((if x = a then 1 else 0) - (if x = b then 1 else 0))) :
    ∑ x, f x * Q x = ∑ a, ∑ b, (c a b : ℝ) * (f a - f b) := by
  simp only [hQ, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => ?_
  have : ∀ x, f x * ((c a b : ℝ) * ((if x = a then 1 else 0) - (if x = b then 1 else 0))) =
      (c a b : ℝ) * ((if x = a then f x else 0) - (if x = b then f x else 0)) := by
    intro x
    split_ifs <;> ring
  simp only [this, ← Finset.mul_sum, Finset.sum_sub_distrib]
  simp

theorem nsq_add (x y : Fin n → ℝ) : nsq (x + y) = nsq x + 2 * ∑ a, x a * y a + nsq y := by
  unfold nsq
  rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun a _ => by simp only [Pi.add_apply]; ring

theorem nsq_sub (x y : Fin n → ℝ) : nsq (x - y) = nsq x - 2 * ∑ a, x a * y a + nsq y := by
  unfold nsq
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun a _ => by simp only [Pi.sub_apply]; ring

theorem lt_of_lev {lam : Fin n → ℤ} {lev : Fin n → ℕ} (hlev : IsLev lam lev) {a b : Fin n}
    (h : lev a < lev b) : a < b := by
  by_contra hn
  exact absurd (hlev.1 (not_lt.1 hn)) (not_le.2 h)

theorem rhoV_gap {a b : Fin n} (h : a < b) : 0 < rhoV n a - rhoV n b := by
  unfold rhoV
  have : ((a : ℕ) : ℝ) < ((b : ℕ) : ℝ) := by exact_mod_cast h
  linarith

theorem muQ_gap {lam : Fin n → ℤ} (hlam : Antitone lam) {lev : Fin n → ℕ} (hlev : IsLev lam lev)
    {a b : Fin n} (h : lev a < lev b) : 0 < muQ lam lev a - muQ lam lev b := by
  have hab := lt_of_lev hlev h
  have h1 : (lam b : ℝ) ≤ lam a := by exact_mod_cast hlam hab.le
  have h2 : (univ.filter fun c => lev b < lev c).card < (univ.filter fun c => lev a < lev c).card := by
    refine Finset.card_lt_card ⟨fun c hc => ?_, fun hs => ?_⟩
    · have := (Finset.mem_filter.1 hc).2
      exact Finset.mem_filter.2 ⟨Finset.mem_univ _, h.trans this⟩
    · have := hs (Finset.mem_filter.2 ⟨Finset.mem_univ b, h⟩)
      exact lt_irrefl _ (Finset.mem_filter.1 this).2
  have h3 : (univ.filter fun c => lev c < lev a).card ≤ (univ.filter fun c => lev c < lev b).card := by
    refine Finset.card_le_card fun c hc => ?_
    have := (Finset.mem_filter.1 hc).2
    exact Finset.mem_filter.2 ⟨Finset.mem_univ _, this.trans h⟩
  have h2' : ((univ.filter fun c => lev b < lev c).card : ℝ) < ((univ.filter fun c => lev a < lev c).card : ℝ) := by
    exact_mod_cast h2
  have h3' : ((univ.filter fun c => lev c < lev a).card : ℝ) ≤ ((univ.filter fun c => lev c < lev b).card : ℝ) := by
    exact_mod_cast h3
  unfold muQ rhoU
  linarith

theorem cone_weight_not_in_second : ConeWeightsNotSecondType := by
  intro n lam hlam lev hlev ν hc hN
  obtain ⟨B, hne, hBl, -, w, hw⟩ := hN
  obtain ⟨c, hcl, hcQ⟩ := hc
  have hB : ∀ p ∈ B, p.1 < p.2 := fun p hp => lt_of_lev hlev (hBl p hp)

  have e1 : nsq (ν + rhoV n) = nsq (muQ lam lev + rhoV n - wtB B) := by
    rw [hw]
    unfold nsq
    exact Equiv.sum_comp w fun a => (muQ lam lev + rhoV n - wtB B) a ^ 2

  have e2 : nsq (muQ lam lev + rhoV n) ≤ nsq (ν + rhoV n) := by
    have hs : ν + rhoV n = (muQ lam lev + rhoV n) + (ν - muQ lam lev) := by abel
    rw [hs, nsq_add (muQ lam lev + rhoV n), dot_cone _ c _ hcQ]
    have hd : 0 ≤ ∑ a, ∑ b, (c a b : ℝ) *
        ((muQ lam lev + rhoV n) a - (muQ lam lev + rhoV n) b) := by
      refine Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun b _ => ?_
      by_cases h0 : c a b = 0
      · simp [h0]
      · have hl := hcl a b h0
        have g1 := muQ_gap hlam hlev hl
        have g2 := rhoV_gap (lt_of_lev hlev hl)
        simp only [Pi.add_apply]
        exact mul_nonneg (Nat.cast_nonneg _) (by linarith)
    have hq : 0 ≤ nsq (ν - muQ lam lev) := Finset.sum_nonneg fun a _ => sq_nonneg _
    linarith

  have e3 : nsq (muQ lam lev + rhoV n - wtB B) < nsq (muQ lam lev + rhoV n) := by
    have h1 := nsq_rho_sub_le hB
    rw [nsq_sub] at h1
    have hpos : 0 < ∑ a, muQ lam lev a * wtB B a := by
      rw [dot_wtB]
      exact Finset.sum_pos (fun p hp => muQ_gap hlam hlev (hBl p hp)) hne
    have hsplit : ∑ a, (muQ lam lev + rhoV n) a * wtB B a =
        ∑ a, muQ lam lev a * wtB B a + ∑ a, rhoV n a * wtB B a := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun a _ => by simp only [Pi.add_apply]; ring
    rw [nsq_sub, hsplit]
    linarith
  linarith

end GlobalTheory.CompanionTheory.ConeSecondWeights
