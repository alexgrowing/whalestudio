import Mathlib
import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.DiscreteSeriesCharacters.CapelliDeterminantBlockProduct
import Formalism.RealPlaceAnalysis.ThirdArithmeticHolds

open Finset

noncomputable section

namespace GlobalTheory.CompanionTheory.DSNormLt

open CompanionTheory.D.DSIC

variable {n : ℕ}

def sig (a b : Fin n) : ℝ := if a < b then 1 else if b < a then -1 else 0

theorem sig_anti (a b : Fin n) : sig b a = - sig a b := by
  unfold sig
  rcases lt_trichotomy a b with h | h | h
  · simp [h, h.not_gt]
  · simp [h]
  · simp [h, h.not_gt]

theorem sig_mul {y : Fin n → ℝ} (hy : Antitone y) (a b : Fin n) : sig a b * (y a - y b) = |y a - y b| := by
  unfold sig
  rcases lt_trichotomy a b with h | h | h
  · rw [if_pos h, one_mul, abs_of_nonneg (sub_nonneg.2 (hy h.le))]
  · simp [h]
  · rw [if_neg h.not_gt, if_pos h, abs_of_nonpos (sub_nonpos.2 (hy h.le))]; ring

theorem pair_eq (t : Fin n → Fin n → ℝ) (ht : ∀ a b, t b a = - t a b) (x : Fin n → ℝ) :
    4 * ∑ a, x a * ((∑ b, t a b) / 2) = ∑ a, ∑ b, t a b * (x a - x b) := by
  have h1 : ∑ a, ∑ b, t a b * x b = - ∑ a, ∑ b, t a b * x a := by
    rw [Finset.sum_comm, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [ht a b]; ring
  have h2 : ∑ a, x a * ((∑ b, t a b) / 2) = (∑ a, ∑ b, t a b * x a) / 2 := by
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← Finset.sum_mul]; ring
  simp only [mul_sub, Finset.sum_sub_distrib]
  rw [h1, h2]; ring

theorem term_le {s z : ℝ} (hs : |s| ≤ 1) : s * z ≤ |z| := by
  calc s * z ≤ |s * z| := le_abs_self _
    _ = |s| * |z| := abs_mul _ _
    _ ≤ 1 * |z| := by gcongr
    _ = |z| := one_mul _

theorem normSq_le (t : Fin n → Fin n → ℝ) (ht : ∀ a b, t b a = - t a b) (h1 : ∀ a b, |t a b| ≤ 1) :
    ∑ a, ((∑ b, t a b) / 2) ^ 2 ≤ ∑ a : Fin n, ((∑ b, sig a b) / 2) ^ 2 := by
  set x : Fin n → ℝ := fun a => (∑ b, t a b) / 2 with hx
  set r : Fin n → ℝ := fun a => (∑ b, sig a b) / 2 with hr
  let τ : Equiv.Perm (Fin n) := Tuple.sort (fun a => - x a)
  have hτ : Antitone (fun a => x (τ a)) := by
    intro a b hab
    have := Tuple.monotone_sort (fun a => - x a) hab
    simpa using this
  have e1 : 4 * ∑ a, x a ^ 2 ≤ 4 * ∑ a, x (τ a) * r a := by
    have := pair_eq t ht x
    have h2 := pair_eq sig sig_anti (fun a => x (τ a))
    calc 4 * ∑ a, x a ^ 2 = ∑ a, ∑ b, t a b * (x a - x b) := by
          rw [← this]; simp only [hx, sq]
      _ ≤ ∑ a, ∑ b, |x a - x b| :=
          Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ => term_le (h1 a b)
      _ = ∑ a, ∑ b, |x (τ a) - x (τ b)| := by
          rw [← Equiv.sum_comp τ]
          refine Finset.sum_congr rfl fun a _ => ?_
          rw [← Equiv.sum_comp τ]
      _ = ∑ a, ∑ b, sig a b * (x (τ a) - x (τ b)) :=
          Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => (sig_mul hτ a b).symm
      _ = _ := h2.symm
  have e2 : 2 * ∑ a, x (τ a) * r a ≤ ∑ a, x (τ a) ^ 2 + ∑ a, r a ^ 2 := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_le_sum fun a _ => by nlinarith [sq_nonneg (x (τ a) - r a)]
  have e3 : ∑ a, x (τ a) ^ 2 = ∑ a, x a ^ 2 := Equiv.sum_comp τ (fun a => x a ^ 2)
  show ∑ a, x a ^ 2 ≤ ∑ a, r a ^ 2
  linarith

theorem pair_lt (t : Fin n → Fin n → ℝ) (ht : ∀ a b, t b a = - t a b) (h1 : ∀ a b, |t a b| ≤ 1)
    {lam : Fin n → ℝ} (hl : StrictAnti lam) (c d : Fin n) (hcd : c ≠ d) (hne : t c d = - sig c d) :
    ∑ a, lam a * ((∑ b, t a b) / 2) < ∑ a, lam a * ((∑ b, sig a b) / 2) := by
  have e1 := pair_eq t ht lam
  have e2 := pair_eq sig sig_anti lam
  have hle : ∀ a b, t a b * (lam a - lam b) ≤ sig a b * (lam a - lam b) := fun a b => by
    rw [sig_mul hl.antitone]; exact term_le (h1 a b)
  have : ∑ a, ∑ b, t a b * (lam a - lam b) < ∑ a, ∑ b, sig a b * (lam a - lam b) := by
    refine Finset.sum_lt_sum (fun a _ => Finset.sum_le_sum fun b _ => hle a b) ⟨c, mem_univ _, ?_⟩
    refine Finset.sum_lt_sum (fun b _ => hle c b) ⟨d, mem_univ _, ?_⟩
    rw [hne, neg_mul, sig_mul hl.antitone]
    have : 0 < |lam c - lam d| := abs_pos.2 (sub_ne_zero.2 fun h => hcd (hl.injective h))
    linarith
  linarith

open Classical in

def ind {ε : Fin n → Bool} (A : Finset (NC ε)) (a b : Fin n) : ℝ :=
  if ∃ h : ε a = true ∧ ε b = false, (⟨(a, b), h⟩ : NC ε) ∈ A then 1 else 0

theorem wtA_eq {ε : Fin n → Bool} (A : Finset (NC ε)) (c : Fin n) :
    wtA A c = ∑ b, (ind A c b - ind A b c) := by
  classical
  rw [Finset.sum_sub_distrib]
  unfold wtA ind
  rw [Finset.sum_boole, Finset.sum_boole]
  congr 2
  · refine Finset.card_bij (fun i _ => i.1.2) ?_ ?_ ?_
    · rintro ⟨⟨a, b⟩, h⟩ hi
      simp only [mem_filter] at hi
      obtain ⟨hi, rfl⟩ := hi
      simp only [mem_filter, mem_univ, true_and]
      exact ⟨h, hi⟩
    · rintro ⟨⟨a, b⟩, h⟩ hi ⟨⟨a', b'⟩, h'⟩ hi' e
      simp only [mem_filter] at hi hi' e
      obtain ⟨_, rfl⟩ := hi
      obtain ⟨_, rfl⟩ := hi'
      subst e
      rfl
    · intro b hb
      simp only [mem_filter, mem_univ, true_and] at hb
      obtain ⟨h, hb⟩ := hb
      exact ⟨⟨(c, b), h⟩, mem_filter.2 ⟨hb, rfl⟩, rfl⟩
  · refine Finset.card_bij (fun i _ => i.1.1) ?_ ?_ ?_
    · rintro ⟨⟨a, b⟩, h⟩ hi
      simp only [mem_filter] at hi
      obtain ⟨hi, rfl⟩ := hi
      simp only [mem_filter, mem_univ, true_and]
      exact ⟨h, hi⟩
    · rintro ⟨⟨a, b⟩, h⟩ hi ⟨⟨a', b'⟩, h'⟩ hi' e
      simp only [mem_filter] at hi hi' e
      obtain ⟨_, rfl⟩ := hi
      obtain ⟨_, rfl⟩ := hi'
      subst e
      rfl
    · intro b hb
      simp only [mem_filter, mem_univ, true_and] at hb
      obtain ⟨h, hb⟩ := hb
      exact ⟨⟨(b, c), h⟩, mem_filter.2 ⟨hb, rfl⟩, rfl⟩

theorem ind_of_not {ε : Fin n → Bool} (A : Finset (NC ε)) {a b : Fin n} (h : ¬ (ε a = true ∧ ε b = false)) :
    ind A a b = 0 := by
  unfold ind
  rw [if_neg]
  rintro ⟨h', _⟩
  exact h h'

theorem ind_of {ε : Fin n → Bool} (A : Finset (NC ε)) {a b : Fin n} (h : ε a = true ∧ ε b = false) :
    ind A a b = if (⟨(a, b), h⟩ : NC ε) ∈ A then 1 else 0 := by
  unfold ind
  congr 1
  simp [h]

def tt {ε : Fin n → Bool} (A : Finset (NC ε)) (a b : Fin n) : ℝ :=
  sig a b + 2 * ((ind (A1 ε) a b - ind (A1 ε) b a) - (ind A a b - ind A b a))

theorem tt_anti {ε : Fin n → Bool} (A : Finset (NC ε)) (a b : Fin n) : tt A b a = - tt A a b := by
  unfold tt; rw [sig_anti a b]; ring

theorem tt_of {ε : Fin n → Bool} (A : Finset (NC ε)) {a b : Fin n} (h : ε a = true ∧ ε b = false) :
    tt A a b = if ((⟨(a, b), h⟩ : NC ε) ∈ A ↔ (⟨(a, b), h⟩ : NC ε) ∈ A1 ε) then sig a b else - sig a b := by
  have h' : ¬ (ε b = true ∧ ε a = false) := by simp [h.1]
  have hab : a ≠ b := by rintro rfl; simp [h.1] at h
  unfold tt
  rw [ind_of_not _ h', ind_of_not _ h', ind_of _ h, ind_of _ h]
  have hm : (⟨(a, b), h⟩ : NC ε) ∈ A1 ε ↔ b < a := by simp [A1]
  simp only [hm]
  unfold sig
  rcases lt_or_gt_of_ne hab with h1 | h1 <;> by_cases h2 : (⟨(a, b), h⟩ : NC ε) ∈ A <;>
    simp [h1, h1.not_gt, h2] <;> norm_num

theorem abs_sig (a b : Fin n) : |sig a b| ≤ 1 := by
  unfold sig; split_ifs <;> simp

theorem abs_tt {ε : Fin n → Bool} (A : Finset (NC ε)) (a b : Fin n) : |tt A a b| ≤ 1 := by
  have key : ∀ a b : Fin n, (ε a = true ∧ ε b = false) → |tt A a b| ≤ 1 := fun a b h => by
    rw [tt_of A h]
    split_ifs
    · exact abs_sig a b
    · rw [abs_neg]; exact abs_sig a b
  by_cases h : ε a = true ∧ ε b = false
  · exact key a b h
  by_cases h' : ε b = true ∧ ε a = false
  · rw [tt_anti, abs_neg]; exact key b a h'
  unfold tt
  rw [ind_of_not _ h', ind_of_not _ h', ind_of_not _ h, ind_of_not _ h]
  simpa using abs_sig a b

theorem rho_eq (ε : Fin n → Bool) (a : Fin n) :
    PI.UpqRep.rhoC ε a + PI.UpqRep.rhoN ε a = (∑ b, sig a b) / 2 := by
  unfold PI.UpqRep.rhoC PI.UpqRep.rhoN
  rw [← add_div]
  congr 1
  simp only [Finset.card_filter, Nat.cast_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun b _ => ?_
  unfold sig
  rcases lt_trichotomy a b with h | h | h
  · by_cases h2 : ε b = ε a <;> simp [h, h.not_gt, h2]
  · simp [h]
  · by_cases h2 : ε b = ε a <;> simp [h, h.not_gt, h2]

theorem normLt : CompanionTheory.D.DSIC.NormLt := by
  intro n ε lam hl A hA
  obtain ⟨⟨⟨c, d⟩, h⟩, hi⟩ : ∃ i : NC ε, ¬ (i ∈ A ↔ i ∈ A1 ε) := by
    by_contra hc
    push Not at hc
    exact hA (Finset.ext fun i => by simpa using hc i)
  have hcd : c ≠ d := by rintro rfl; simp [h.1] at h
  have hne : tt A c d = - sig c d := by rw [tt_of A h, if_neg hi]
  have i1 := pair_lt (tt A) (tt_anti A) (abs_tt A) hl c d hcd hne
  have i2 := normSq_le (tt A) (tt_anti A) (abs_tt A)
  have f1 : ∀ a, (gam ε lam - wtA A + (2 : ℝ) • PI.UpqRep.rhoC ε) a = lam a + (∑ b, tt A a b) / 2 := fun a => by
    have := rho_eq ε a
    simp only [gam, PI.UpqRep.lowK, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, wtA_eq, tt,
      Finset.sum_add_distrib, ← Finset.mul_sum]
    rw [Finset.sum_sub_distrib (f := fun b => ind (A1 ε) a b - ind (A1 ε) b a)]
    linarith
  have f2 : ∀ a, (PI.UpqRep.lowK ε lam + (2 : ℝ) • PI.UpqRep.rhoC ε) a = lam a + (∑ b, sig a b) / 2 := fun a => by
    have := rho_eq ε a
    simp only [PI.UpqRep.lowK, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    linarith
  have ex : ∀ y : Fin n → ℝ, ∑ a, (lam a + y a) * (lam a + y a) =
      ∑ a, lam a ^ 2 + 2 * ∑ a, lam a * y a + ∑ a, y a ^ 2 := fun y => by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun a _ => by ring
  unfold PI.UpqRep.vNormSq PI.UpqRep.nsq PI.UpqRep.dot
  simp only [f1, f2]
  rw [ex, ex]
  linarith

end GlobalTheory.CompanionTheory.DSNormLt
