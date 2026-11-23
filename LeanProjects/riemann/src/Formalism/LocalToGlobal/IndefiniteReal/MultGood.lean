import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
import Formalism.LocalToGlobal.HeckeThetaElements.DefsWt

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.NTheta

namespace Formalism.IndefR.Mult

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem goodPar_of_enum {n p q : ℕ} (L : Fin n → ℚ) (s : Fin n → Bool) (hL : StrictAnti L)
    (hi : ∀ a, ∃ z : ℤ, (L a : ℝ) - ((n : ℝ) - 1) / 2 = z)
    (hp : (Finset.univ.filter fun a => s a = true).card = p)
    (hq : (Finset.univ.filter fun a => s a = false).card = q) :
    GoodPar n p q (Finset.univ.image fun a => (L a, s a)) :=
  ⟨fun a => (L a : ℝ), s, ⟨fun _ _ h => by dsimp only; exact_mod_cast hL h, L, fun _ => rfl, rfl⟩,
    ⟨fun _ _ h => by dsimp only; exact_mod_cast hL h, hi⟩, hp, hq⟩

theorem goodPar_dualPar {n p q : ℕ} {S : SPar} (h : GoodPar n p q S) : GoodPar n p q (dualPar S) := by
  obtain ⟨lam, ε, ⟨hanti, Q, hQ, rfl⟩, ⟨_, hint⟩, hp, hq⟩ := h
  refine ⟨fun a => -lam (Fin.rev a), fun a => ε (Fin.rev a),
    ⟨fun a b hab => neg_lt_neg (hanti (Fin.rev_lt_rev.mpr hab)), fun a => -Q (Fin.rev a), fun a => by simp [hQ], ?_⟩,
    ⟨fun a b hab => neg_lt_neg (hanti (Fin.rev_lt_rev.mpr hab)), fun a => ?_⟩, ?_, ?_⟩
  · unfold dualPar
    rw [Finset.image_image]
    ext ⟨x, s⟩
    simp only [Finset.mem_image, Finset.mem_univ, true_and, Function.comp_apply, Prod.mk.injEq]
    constructor
    · rintro ⟨a, ha⟩
      exact ⟨Fin.rev a, by simpa using ha⟩
    · rintro ⟨a, ha⟩
      exact ⟨_, ha⟩
  · obtain ⟨z, hz⟩ := hint (Fin.rev a)
    refine ⟨-z - ((n : ℤ) - 1), ?_⟩
    push_cast
    linarith
  · rw [← hp]
    exact Finset.card_equiv Fin.revPerm (by intro i; simp)
  · rw [← hq]
    exact Finset.card_equiv Fin.revPerm (by intro i; simp)

theorem card_false_eq {n : ℕ} (s : Fin n → Bool) :
    (Finset.univ.filter fun a => s a = false).card = n - (Finset.univ.filter fun a => s a = true).card := by
  have := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin n))) (fun a => s a = true)
  simp only [Bool.not_eq_true, Finset.card_univ, Fintype.card_fin] at this
  omega

theorem sum_first_or_even (K c : ℕ) :
    ∑ i ∈ Finset.range (K + 2 * c), (if i < K ∨ Even (i - K) then 1 else 0) = K + c := by
  induction c with
  | zero =>
    simp only [mul_zero, add_zero]
    rw [Finset.sum_congr rfl (fun i hi => if_pos (Or.inl (Finset.mem_range.mp hi)))]
    simp
  | succ c ih =>
    rw [show K + 2 * (c + 1) = K + 2 * c + 1 + 1 by ring, Finset.sum_range_succ, Finset.sum_range_succ, ih,
      if_pos (Or.inr ⟨c, by omega⟩), if_neg (by rintro (h | ⟨d, hd⟩) <;> omega)]
    omega

theorem sum_first (p q : ℕ) : ∑ i ∈ Finset.range (p + q), (if i < p then 1 else 0) = p := by
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, smul_eq_mul, mul_one]
  have : (Finset.range (p + q)).filter (fun i => i < p) = Finset.range p := by
    ext i; simp only [Finset.mem_filter, Finset.mem_range]; omega
  rw [this, Finset.card_range]

theorem lamAt_strictAnti {R : Ranks} (h : HCParam R) : StrictAnti fun a : Fin R.r => lamAt h a := by
  intro a b hab
  have hab' : (a : ℕ) < b := hab
  have := lamAt_add_add_le h ((b : ℕ) - a) a (by omega)
  rw [show (a : ℕ) + ((b : ℕ) - a) = b by omega] at this
  have h1 : (1 : ℚ) ≤ (((b : ℕ) - a : ℕ) : ℚ) := by
    have : 1 ≤ (b : ℕ) - a := by omega
    exact_mod_cast this
  show lamAt h b < lamAt h a
  linarith

theorem lamAt_half {R : Ranks} (h : HCParam R) (a : Fin R.r) :
    ∃ z : ℤ, ((lamAt h a : ℚ) : ℝ) - ((R.r : ℝ) - 1) / 2 = z := by
  obtain ⟨z, hz⟩ := lamAt_int h a
  obtain ⟨s, hs⟩ := odd_r R
  refine ⟨z - s, ?_⟩
  rw [hz, hs]
  push_cast
  ring

def sgA (R : Ranks) (a : ℕ) : Bool := decide (a < R.k - 1 ∨ Even (a - (R.k - 1)))

theorem parA_eq (D : D7) (eta : D.what₂.Tau → ℚ) (h : ∀ τ, eta τ = 1 / 2 ∨ eta τ = -(1 / 2)) (τ : D.what₂.Tau) :
    parA (tparHC D eta h) 0 τ = Finset.univ.image fun a : Fin D.R.r => (lamAt (D.hc τ) a, sgA D.R a) := by
  have hk := D.R.m_add_three_le_k
  have hrr : D.R.r = D.R.k + D.R.m - 1 := rfl
  unfold parA TPar.Dpar
  ext ⟨x, s⟩
  simp only [tparHC, Finset.mem_image, Finset.mem_union, Finset.mem_univ, true_and, Prod.mk.injEq,
    Finset.mem_biUnion, Finset.mem_filter, Nat.not_lt_zero, false_and, exists_false, or_false,
    Nat.not_odd_zero, if_false, add_zero]
  constructor
  · rintro ⟨⟨y, s'⟩, (⟨i, hi⟩ | ⟨i, hi⟩), rfl, rfl⟩
    · simp only [Prod.mk.injEq] at hi
      obtain ⟨rfl, rfl⟩ := hi
      refine ⟨⟨i, by have := i.2; omega⟩, ?_, ?_⟩
      · unfold lamAt; rw [dif_pos i.2]
      · unfold sgA; simp [i.2]
    · simp only [Prod.mk.injEq] at hi
      obtain ⟨rfl, rfl⟩ := hi
      refine ⟨⟨D.R.k - 1 + i, by have := i.2; omega⟩, ?_, ?_⟩
      · unfold lamAt
        rw [dif_neg (show ¬ (D.R.k - 1 + (i : ℕ) < D.R.k - 1) by omega),
          dif_pos (show D.R.k - 1 + (i : ℕ) - (D.R.k - 1) < D.R.m by have := i.2; omega)]
        simp only [Nat.add_sub_cancel_left]
      · unfold sgA
        simp only [Nat.even_iff]
        exact decide_eq_decide.mpr (by omega)
  · rintro ⟨a, rfl, rfl⟩
    have ha := a.2
    by_cases c : (a : ℕ) < D.R.k - 1
    · refine ⟨_, Or.inl ⟨⟨a, c⟩, rfl⟩, ?_, ?_⟩
      · change (D.hc τ).v ⟨a, c⟩ = lamAt (D.hc τ) a
        unfold lamAt; rw [dif_pos c]
      · change true = sgA D.R a
        unfold sgA; simp [c]
    · refine ⟨_, Or.inr ⟨⟨(a : ℕ) - (D.R.k - 1), by omega⟩, rfl⟩, ?_, ?_⟩
      · change -(D.hc τ).b _ = lamAt (D.hc τ) a
        unfold lamAt; rw [dif_neg c, dif_pos (by omega)]
      · change decide _ = sgA D.R a
        unfold sgA
        simp only [Nat.even_iff]
        exact decide_eq_decide.mpr (by omega)

theorem card_sgA (R : Ranks) :
    (Finset.univ.filter fun a : Fin R.r => sgA R a = true).card = R.k - 1 + R.m / 2 := by
  rw [Finset.card_filter, Fin.sum_univ_eq_sum_range (fun i => if sgA R i = true then 1 else 0) R.r]
  have hr : R.r = (R.k - 1) + 2 * (R.m / 2) := by
    have := R.m_add_three_le_k
    obtain ⟨c, hc⟩ := R.m_even
    unfold Ranks.r; omega
  rw [hr]
  simp only [sgA, decide_eq_true_eq]
  exact sum_first_or_even _ _

theorem goodPar_parA (D : D7) (eta : D.what₂.Tau → ℚ) (h : ∀ τ, eta τ = 1 / 2 ∨ eta τ = -(1 / 2))
    (τ : D.what₂.Tau) : GoodPar D.R.r D.R.sigY0.1 D.R.sigY0.2 (parA (tparHC D eta h) 0 τ) := by
  rw [parA_eq]
  have hk := D.R.m_add_three_le_k
  have hm := D.R.two_le_m
  obtain ⟨c, hc⟩ := D.R.m_even
  refine goodPar_of_enum _ _ (lamAt_strictAnti _) (lamAt_half _) ?_ ?_
  · rw [card_sgA]; simp only [Ranks.sigY0, Ranks.rS]; omega
  · rw [card_false_eq, card_sgA]; simp only [Ranks.sigY0, Ranks.rS, Ranks.r]; omega

theorem good_parameter_first_base_space (D : D7) (eta : D.what₂.Tau → ℚ) (h : ∀ τ, eta τ = 1 / 2 ∨ eta τ = -(1 / 2))
    (τ : D.what₂.Tau) :
    GoodPar (D.sp.Y 0).rank ((D.sp.Y 0).sig (tauE D τ)).1 ((D.sp.Y 0).sig (tauE D τ)).2
      (parA (tparHC D eta h) 0 τ) := by
  rw [D.sp.baseSpace_signature_eq, D.sp.Y_rank 0 (Nat.zero_le _)]
  have : D.R.rankY 0 = D.R.r := by simp [Ranks.rankY]
  rw [this]
  exact goodPar_parA D eta h τ

theorem good_parameter_second_base_space (D : D7) (eta : D.what₂.Tau → ℚ) (h : ∀ τ, eta τ = 1 / 2 ∨ eta τ = -(1 / 2))
    (τ : D.what₂.Tau) :
    GoodPar (D.sp.Y 0).rank ((D.sp.Y 0).sig (tauE D τ)).1 ((D.sp.Y 0).sig (tauE D τ)).2
      (parB (tparHC D eta h) 0 τ) :=
  goodPar_dualPar (good_parameter_first_base_space D eta h τ)

theorem goodPar_parA_rec (D : D7) : ∀ τ, GoodPar (D.sp.Y 0).rank ((D.sp.Y 0).sig (tauE D τ)).1
    ((D.sp.Y 0).sig (tauE D τ)).2 (parA (tparRec D) 0 τ) :=
  good_parameter_first_base_space D _ _

theorem goodPar_parB_rec (D : D7) : ∀ τ, GoodPar (D.sp.Y 0).rank ((D.sp.Y 0).sig (tauE D τ)).1
    ((D.sp.Y 0).sig (tauE D τ)).2 (parB (tparRec D) 0 τ) :=
  good_parameter_second_base_space D _ _

theorem holPar_kapW_eq {R : Ranks} (h : HCParam R) (p q : ℕ) (hpq : p + q = R.r) :
    holPar p q (kapW h p q) = Finset.univ.image fun a : Fin R.r => (lamAt h a, decide ((a : ℕ) < p)) := by
  have ho : Odd (p + q) := hpq ▸ odd_r R
  ext ⟨x, s⟩
  simp only [holPar, Finset.mem_image, Finset.mem_univ, true_and, Prod.mk.injEq, holEnt_kapW h p q ho]
  constructor
  · rintro ⟨a, rfl, rfl⟩
    cases a with
    | inl i => exact ⟨⟨i, by have := i.2; omega⟩, rfl, by simp⟩
    | inr c => exact ⟨⟨p + c, by have := c.2; omega⟩, rfl, by simp⟩
  · rintro ⟨a, rfl, rfl⟩
    by_cases hc : (a : ℕ) < p
    · exact ⟨Sum.inl ⟨a, hc⟩, rfl, by simp [hc]⟩
    · refine ⟨Sum.inr ⟨a - p, by have := a.2; omega⟩, ?_, by simp [hc]⟩
      simp only [Sum.elim_inr]
      rw [show p + ((a : ℕ) - p) = a by omega]

theorem card_lt_first {n : ℕ} (p q : ℕ) (hpq : p + q = n) :
    (Finset.univ.filter fun a : Fin n => decide ((a : ℕ) < p) = true).card = p := by
  rw [Finset.card_filter, Fin.sum_univ_eq_sum_range (fun i => if decide (i < p) = true then 1 else 0) n, ← hpq]
  simp only [decide_eq_true_eq]
  exact sum_first p q

theorem goodPar_parW (D : D7) (W : HSp D) (τ : D.what₂.Tau)
    (hr : (W.sig (tauE D τ)).1 + (W.sig (tauE D τ)).2 = D.R.r) :
    GoodPar D.R.r (W.sig (tauE D τ)).1 (W.sig (tauE D τ)).2 (parW W (wtOf D W) τ) := by
  show GoodPar D.R.r _ _ (holPar _ _ (kapW (D.hc τ) _ _))
  rw [holPar_kapW_eq _ _ _ hr]
  refine goodPar_of_enum _ _ (lamAt_strictAnti _) (lamAt_half _) (card_lt_first _ _ hr) ?_
  rw [card_false_eq, card_lt_first _ _ hr]
  omega

theorem goodPar_parW_rec (D : D7) (j : ℕ) (hj1 : 1 ≤ j) (hjm : j ≤ D.R.m) :
    ∀ τ, GoodPar (D.sp.W j).rank ((D.sp.W j).sig (tauE D τ)).1 ((D.sp.W j).sig (tauE D τ)).2
      (parW (D.sp.W j) (wtOf D (D.sp.W j)) τ) := by
  intro τ
  rw [D.sp.W_rank j hj1 hjm]
  refine goodPar_parW D _ τ ?_
  rw [D.sp.W_sigval j hj1 hjm]
  simp only [Ranks.sigW, Ranks.r]
  omega

end Formalism.IndefR.Mult
