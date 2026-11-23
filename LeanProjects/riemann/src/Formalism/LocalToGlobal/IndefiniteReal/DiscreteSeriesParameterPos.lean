import Formalism.LocalToGlobal.IndefiniteReal.DiscreteSeriesPlaces
import Formalism.LocalToGlobal.IndefiniteReal.MultGood
import Formalism.LocalRingCardinality.HeightBoundGeFourthPowerRank
import Formalism.LocalRingCardinality.PosOfIsomEmb
import Formalism.SharpRestriction.Divisibility.FunctionModelRallisFromInputs
import Mathlib
import Formalism.SharpRestriction.AdmissibleParameterJoins.SfromGLw
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.NTheta Formalism.IndefR.Mult Matrix

namespace Formalism.IndefR.DiscreteSeriesPlaces

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem lamAt_of_b {R : Ranks} (hc : HCParam R) (c : ℕ) (h1 : R.k - 1 ≤ c) (h2 : c - (R.k - 1) < R.m) :
    lamAt hc c = -hc.b ⟨c - (R.k - 1), h2⟩ := by
  unfold lamAt
  rw [dif_neg (by omega), dif_pos h2]

theorem lamAt_anti {R : Ranks} (hc : HCParam R) {d c : ℕ} (hdc : d ≤ c) (hc' : c < R.r) :
    lamAt hc c ≤ lamAt hc d := by
  have := lamAt_add_add_le hc (c - d) d (by omega)
  rw [show d + (c - d) = c by omega] at this
  have h0 : (0 : ℚ) ≤ ((c - d : ℕ) : ℚ) := by positivity
  linarith

theorem gap_minus {R : Ranks} (hc : HCParam R) (h : ℝ)
    (hb : ∀ (j j' : ℕ) (hj : j < R.m) (hj' : j' < R.m), j' = j + 1 → h ≤ ((hc.b ⟨j', hj'⟩ - hc.b ⟨j, hj⟩ : ℚ) : ℝ))
    (c d : ℕ) (hcr : c < R.r) (hdr : d < R.r) (hcs : sgA R c = false) (hdc : d ≠ c) :
    h ≤ |((lamAt hc d : ℚ) : ℝ) - ((lamAt hc c : ℚ) : ℝ)| := by
  have hrr : R.r = R.k + R.m - 1 := rfl
  have hk := R.m_add_three_le_k
  unfold sgA at hcs
  simp only [decide_eq_false_iff_not, not_or, not_lt, Nat.not_even_iff_odd] at hcs
  obtain ⟨hc1, ⟨i, hi⟩⟩ := hcs
  have hcm : c - (R.k - 1) < R.m := by omega
  have hlc := lamAt_of_b hc c hc1 hcm
  rcases Nat.lt_or_gt_of_ne hdc with hlt | hgt
  · have hm1 : c - 1 - (R.k - 1) < R.m := by omega
    have hl1 := lamAt_of_b hc (c - 1) (by omega) hm1
    have hmono := lamAt_anti hc (show d ≤ c - 1 by omega) (by omega)
    have hg := hb (c - 1 - (R.k - 1)) (c - (R.k - 1)) hm1 hcm (by omega)
    have hmono' : ((lamAt hc (c - 1) : ℚ) : ℝ) ≤ ((lamAt hc d : ℚ) : ℝ) := by exact_mod_cast hmono
    rw [hl1] at hmono'
    rw [hlc]
    push_cast at hg hmono' ⊢
    exact le_trans (by linarith) (le_abs_self _)
  · have hm1 : c + 1 - (R.k - 1) < R.m := by omega
    have hl1 := lamAt_of_b hc (c + 1) (by omega) hm1
    have hmono := lamAt_anti hc (show c + 1 ≤ d by omega) hdr
    have hg := hb (c - (R.k - 1)) (c + 1 - (R.k - 1)) hcm hm1 (by omega)
    have hmono' : ((lamAt hc d : ℚ) : ℝ) ≤ ((lamAt hc (c + 1) : ℚ) : ℝ) := by exact_mod_cast hmono
    rw [hl1] at hmono'
    rw [hlc]
    push_cast at hg hmono' ⊢
    exact le_trans (by linarith) (neg_le_abs _)

theorem isEnum_dual {n : ℕ} {S : SPar} {lam : Fin n → ℝ} {ε : Fin n → Bool} (h : IsEnum S lam ε) :
    IsEnum (dualPar S) (fun a => -lam (Fin.rev a)) (fun a => ε (Fin.rev a)) := by
  obtain ⟨hanti, Q, hQ, rfl⟩ := h
  refine ⟨fun a b hab => neg_lt_neg (hanti (Fin.rev_lt_rev.mpr hab)), fun a => -Q (Fin.rev a),
    fun a => by simp [hQ], ?_⟩
  unfold dualPar
  rw [Finset.image_image]
  ext ⟨x, s⟩
  simp only [Finset.mem_image, Finset.mem_univ, true_and, Function.comp_apply, Prod.mk.injEq]
  constructor
  · rintro ⟨a, ha⟩
    exact ⟨Fin.rev a, by simpa using ha⟩
  · rintro ⟨a, ha⟩
    exact ⟨_, ha⟩

theorem exists_enumB (D : D7) (h : ℝ) (hN : D.NodeGap h) (τ : D.what₂.Tau) (n : ℕ) (hn : n = D.R.r) :
    ∃ (lam : Fin n → ℝ) (ε : Fin n → Bool), IsEnum (parB (tparRec D) 0 τ) lam ε ∧ Formalism.QuantumDeterminants.IsHCParam lam ∧
      Formalism.QuantumDeterminants.GapAtLeast ε lam h ∧ (Finset.univ.filter fun a => ε a = true).card = D.R.sigY0.1 ∧
      (Finset.univ.filter fun a => ε a = false).card = D.R.sigY0.2 := by
  subst hn
  have hb : ∀ (j j' : ℕ) (hj : j < D.R.m) (hj' : j' < D.R.m), j' = j + 1 →
      h ≤ (((D.hc τ).b ⟨j', hj'⟩ - (D.hc τ).b ⟨j, hj⟩ : ℚ) : ℝ) := by
    intro j j' hj hj' e
    subst e
    have := hN D.u₀ τ j hj'
    rwa [D.hcW_base] at this
  have hk := D.R.m_add_three_le_k
  have hm := D.R.two_le_m
  obtain ⟨c, hc⟩ := D.R.m_even
  have hcnt : (Finset.univ.filter fun a : Fin D.R.r => sgA D.R (Fin.rev a) = true).card =
      (Finset.univ.filter fun a : Fin D.R.r => sgA D.R a = true).card :=
    Finset.card_equiv Fin.revPerm (by intro i; simp)
  have hA : (Finset.univ.filter fun a : Fin D.R.r => sgA D.R (Fin.rev a) = true).card = D.R.k - 1 + D.R.m / 2 :=
    hcnt.trans (card_sgA D.R)
  refine ⟨fun a => -((lamAt (D.hc τ) (Fin.rev a) : ℚ) : ℝ), fun a => sgA D.R (Fin.rev a), ?_, ?_, ?_, ?_, ?_⟩
  · show IsEnum (dualPar (parA (tparHC D _ _) 0 τ)) _ _
    rw [parA_eq]
    exact isEnum_dual (lam := fun a => ((lamAt (D.hc τ) a : ℚ) : ℝ))
      ⟨fun _ _ h => by dsimp only; exact_mod_cast lamAt_strictAnti _ h, fun a => lamAt (D.hc τ) a,
        fun _ => rfl, rfl⟩
  · refine ⟨fun a b hab => neg_lt_neg ?_, fun a => ?_⟩
    · exact_mod_cast lamAt_strictAnti (D.hc τ) (Fin.rev_lt_rev.mpr hab)
    · obtain ⟨z, hz⟩ := lamAt_half (D.hc τ) (Fin.rev a)
      refine ⟨-z - ((D.R.r : ℤ) - 1), ?_⟩
      push_cast
      linarith
  · intro a b hab
    dsimp only at hab ⊢
    have hne : (Fin.rev a : ℕ) ≠ (Fin.rev b : ℕ) := by
      intro e
      apply hab
      rw [Fin.ext e]
    have e1 : -((lamAt (D.hc τ) (Fin.rev a) : ℚ) : ℝ) - -((lamAt (D.hc τ) (Fin.rev b) : ℚ) : ℝ) =
        ((lamAt (D.hc τ) (Fin.rev b) : ℚ) : ℝ) - ((lamAt (D.hc τ) (Fin.rev a) : ℚ) : ℝ) := by ring
    rw [e1]
    cases ha : sgA D.R (Fin.rev a)
    · exact gap_minus (D.hc τ) h hb _ _ (Fin.rev a).2 (Fin.rev b).2 ha (Ne.symm hne)
    · have hbf : sgA D.R (Fin.rev b) = false := by
        rw [ha] at hab
        cases hh : sgA D.R (Fin.rev b)
        · rfl
        · exact absurd hh.symm hab
      rw [abs_sub_comm]
      exact gap_minus (D.hc τ) h hb _ _ (Fin.rev b).2 (Fin.rev a).2 hbf hne
  · rw [hA]; simp only [Ranks.sigY0, Ranks.rS]; omega
  · rw [card_false_eq, hA]; simp only [Ranks.sigY0, Ranks.rS, Ranks.r]; omega

theorem big_rec (D : D7) (n : ℕ) (hn : n = D.R.r) (ε : Fin n → Bool) :
    max (2 * (n : ℝ)) (8 * (n : ℝ) * (ReciprocityTheory.ChartRestriction.DS.S7.q0 ε : ℝ)) <
      4 * (D.R.N D.R.m : ℝ) ^ 3 + 2 * D.R.t + 6 := by
  have hk := D.R.m_add_three_le_k
  have hq : ReciprocityTheory.ChartRestriction.DS.S7.q0 ε ≤ n := by
    unfold ReciprocityTheory.ChartRestriction.DS.S7.q0 ReciprocityTheory.ChartRestriction.DS.pOf
    refine le_trans (min_le_left _ _) ?_
    refine le_trans (Finset.card_filter_le _ _) ?_
    simp
  have hnN : n ≤ D.R.N D.R.m := by
    subst hn
    unfold Ranks.r Ranks.N
    have : D.R.m ≤ D.R.m * (D.R.t + 1) := Nat.le_mul_of_pos_right _ (by omega)
    omega
  have h2N : 2 ≤ D.R.N D.R.m := by unfold Ranks.N; omega
  have hqR : (ReciprocityTheory.ChartRestriction.DS.S7.q0 ε : ℝ) ≤ n := by exact_mod_cast hq
  have hnR : (n : ℝ) ≤ D.R.N D.R.m := by exact_mod_cast hnN
  have h2R : (2 : ℝ) ≤ D.R.N D.R.m := by exact_mod_cast h2N
  have ht : (0 : ℝ) ≤ D.R.t := by positivity
  have hn0 : (0 : ℝ) ≤ n := by positivity
  have hq0 : (0 : ℝ) ≤ (ReciprocityTheory.ChartRestriction.DS.S7.q0 ε : ℝ) := by positivity
  set x : ℝ := (D.R.N D.R.m : ℝ)
  have hx2 : 8 * x ^ 2 ≤ 4 * x ^ 3 := by nlinarith
  have hsq : 8 * (n : ℝ) * (ReciprocityTheory.ChartRestriction.DS.S7.q0 ε : ℝ) ≤ 8 * x ^ 2 := by
    have : (n : ℝ) * (ReciprocityTheory.ChartRestriction.DS.S7.q0 ε : ℝ) ≤ x * x := mul_le_mul hnR (hqR.trans hnR) hq0 (by linarith)
    nlinarith
  refine max_lt ?_ ?_
  · nlinarith
  · linarith

section Rec

variable (D : D7) (τ : D.what₂.Tau)

end Rec

section Rec2

variable (D : D7) (τ : D.what₂.Tau)

end Rec2

theorem isHCParam_dual {n : ℕ} {lam : Fin n → ℝ} (h : Formalism.QuantumDeterminants.IsHCParam lam) :
    Formalism.QuantumDeterminants.IsHCParam (fun a => -lam (Fin.rev a)) := by
  obtain ⟨hanti, hint⟩ := h
  refine ⟨fun a b hab => neg_lt_neg (hanti (Fin.rev_lt_rev.mpr hab)), fun a => ?_⟩
  obtain ⟨z, hz⟩ := hint (Fin.rev a)
  refine ⟨-z - ((n : ℤ) - 1), ?_⟩
  push_cast
  linarith

theorem gap_dual {n : ℕ} {ε : Fin n → Bool} {lam : Fin n → ℝ} {h : ℝ} (hg : Formalism.QuantumDeterminants.GapAtLeast ε lam h) :
    Formalism.QuantumDeterminants.GapAtLeast (fun a => ε (Fin.rev a)) (fun a => -lam (Fin.rev a)) h := by
  intro a b hab
  have := hg (Fin.rev a) (Fin.rev b) hab
  rw [show -lam (Fin.rev a) - -lam (Fin.rev b) = -(lam (Fin.rev a) - lam (Fin.rev b)) by ring, abs_neg]
  exact this

end Formalism.IndefR.DiscreteSeriesPlaces

end
