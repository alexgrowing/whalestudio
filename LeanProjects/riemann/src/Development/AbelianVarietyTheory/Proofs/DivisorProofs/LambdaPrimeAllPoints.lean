import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AtPtsImp
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LamGeoEqFormula

set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpTie

namespace GlobalTheory.LiftWeightForced

open Formalism.IndefR.IndefiniteWeightData

def wd (D : D7) (j : Fin D.R.m) (τ : D.what₂.Tau) : WeightData where
  k := D.R.k
  m := D.R.m
  t := D.R.t
  j := (j : ℕ) + 1
  e := ((D.hc τ).e_int j).choose
  v := fun n => if h : 2 ≤ n ∧ n - 2 < D.R.k - 1 then ((D.hc τ).v_int ⟨n - 2, h.2⟩).choose else 0
  b := fun n => if h : 1 ≤ n ∧ n - 1 < D.R.m then ((D.hc τ).b_int ⟨n - 1, h.2⟩).choose else 0

variable (D : D7) (j : Fin D.R.m) (τ : D.what₂.Tau)

theorem wd_e : ((wd D j τ).e : ℚ) = (D.hc τ).e j := ((D.hc τ).e_int j).choose_spec.symm

theorem wd_v (n : ℕ) (h : 2 ≤ n ∧ n - 2 < D.R.k - 1) : ((wd D j τ).v n : ℚ) = (D.hc τ).v ⟨n - 2, h.2⟩ := by
  show (((if h : 2 ≤ n ∧ n - 2 < D.R.k - 1 then ((D.hc τ).v_int ⟨n - 2, h.2⟩).choose else 0 : ℤ)) : ℚ) = _
  rw [dif_pos h]
  exact ((D.hc τ).v_int _).choose_spec.symm

theorem wd_b (n : ℕ) (h : 1 ≤ n ∧ n - 1 < D.R.m) : ((wd D j τ).b n : ℚ) = (D.hc τ).b ⟨n - 1, h.2⟩ := by
  show (((if h : 1 ≤ n ∧ n - 1 < D.R.m then ((D.hc τ).b_int ⟨n - 1, h.2⟩).choose else 0 : ℤ)) : ℚ) = _
  rw [dif_pos h]
  exact ((D.hc τ).b_int _).choose_spec.symm

end GlobalTheory.LiftWeightForced

namespace GlobalTheory.LiftWeightForced

open Formalism.IndefR.IndefiniteWeightData

variable (D : D7) (j : Fin D.R.m) (τ : D.what₂.Tau)

theorem wd_lam_lo (i : ℕ) (h1 : 1 ≤ i) (h2 : i ≤ D.R.k - 1) :
    ((wd D j τ).lam i : ℚ) = (D.hc τ).v ⟨i - 1, by omega⟩ := by
  have hk : (wd D j τ).k = D.R.k := rfl
  unfold WeightData.lam
  rw [if_pos (by rw [hk]; exact h2), wd_v D j τ (i + 1) ⟨by omega, by omega⟩]
  exact congrArg _ (Fin.ext (by simp))

theorem wd_lam_hi (i : ℕ) (h1 : D.R.k - 1 < i) (h2 : i - (D.R.k - 1) - 1 < D.R.m) :
    ((wd D j τ).lam i : ℚ) = -(D.hc τ).b ⟨i - (D.R.k - 1) - 1, h2⟩ := by
  have hk : (wd D j τ).k = D.R.k := rfl
  unfold WeightData.lam
  rw [if_neg (by rw [hk]; omega)]
  push_cast
  rw [hk, wd_b D j τ _ ⟨by omega, h2⟩]

theorem wd_hyp : (wd D j τ).Hyp := by
  have hR := D.R.m_add_three_le_k
  have hm2 := D.R.two_le_m
  have hjm := j.2
  have ht : (0 : ℚ) ≤ D.R.t := by positivity
  set P := D.hc τ with hP
  have hu : ∀ a b : Fin D.R.k, a.1 = b.1 → P.u a = P.u b := fun a b h => congrArg _ (Fin.ext h)
  have hb : ∀ a b : Fin D.R.m, a.1 = b.1 → P.b a = P.b b := fun a b h => congrArg _ (Fin.ext h)
  refine ⟨show 1 ≤ D.R.k by omega, show 1 ≤ (j : ℕ) + 1 by omega, show (j : ℕ) + 1 ≤ D.R.m by omega, ?_, D.R.t_odd, ?_, ?_, ?_⟩
  · show Odd (D.R.k + D.R.m - 1)
    exact Nat.Even.sub_odd (by omega) (D.R.k_even.add D.R.m_even) odd_one
  · intro i hi1 hi2
    have hi2' : i < D.R.k + D.R.m - 1 := hi2
    suffices ((wd D j τ).lam (i + 1) : ℚ) < (wd D j τ).lam i by exact_mod_cast this
    rcases lt_trichotomy (i + 1) (D.R.k) with h | h | h
    · rw [wd_lam_lo D j τ (i + 1) (by omega) (by omega), wd_lam_lo D j τ i hi1 (by omega)]
      have h1 := P.u_gt_v ⟨i, by omega⟩
      have h2 := P.v_gt_u ⟨i - 1, by omega⟩
      rw [hu ⟨i - 1 + 1, _⟩ ⟨i, by omega⟩ (by simp; omega)] at h2
      have e1 : (⟨i + 1 - 1, by omega⟩ : Fin (D.R.k - 1)) = ⟨i, by omega⟩ := Fin.ext (by simp)
      rw [e1]
      exact h1.trans h2
    · rw [wd_lam_hi D j τ (i + 1) (by omega) (by omega), wd_lam_lo D j τ i hi1 (by omega)]
      have h1 := P.u_last_gt (by omega) (by omega)
      have h2 := P.v_gt_u ⟨i - 1, by omega⟩
      rw [hu ⟨i - 1 + 1, _⟩ ⟨D.R.k - 1, by omega⟩ (by simp; omega)] at h2
      rw [hb ⟨i + 1 - (D.R.k - 1) - 1, _⟩ ⟨0, by omega⟩ (by simp; omega)]
      exact h1.trans h2
    · rw [wd_lam_hi D j τ (i + 1) (by omega) (by omega), wd_lam_hi D j τ i (by omega) (by omega)]
      have h1 := P.gap_be ⟨i - (D.R.k - 1) - 1, by omega⟩
      have h2 := P.gap_eb ⟨i - (D.R.k - 1) - 1, by omega⟩ (by simp; omega)
      rw [hb ⟨i - (D.R.k - 1) - 1 + 1, _⟩ ⟨i + 1 - (D.R.k - 1) - 1, by omega⟩ (by simp; omega)] at h2
      linarith
  · show (((wd D j τ).b ((j : ℕ) + 1)) : ℤ) < (wd D j τ).e
    suffices ((wd D j τ).b ((j : ℕ) + 1) : ℚ) < (wd D j τ).e by exact_mod_cast this
    rw [wd_b D j τ _ ⟨by omega, by omega⟩, wd_e, hb _ j (by simp)]
    have := P.gap_be j
    linarith
  · intro hj'
    have hj'' : (j : ℕ) + 1 < D.R.m := hj'
    show ((wd D j τ).e : ℤ) < (wd D j τ).b ((j : ℕ) + 1 + 1)
    suffices ((wd D j τ).e : ℚ) < (wd D j τ).b ((j : ℕ) + 1 + 1) by exact_mod_cast this
    rw [wd_b D j τ _ ⟨by omega, by omega⟩, wd_e, hb _ ⟨(j : ℕ) + 1, hj''⟩ (by simp)]
    have := P.gap_eb j hj''
    linarith

theorem wd_gap : (wd D j τ).GapHyp := by
  have hjm := j.2
  set P := D.hc τ with hP
  have hb : ∀ a b : Fin D.R.m, a.1 = b.1 → P.b a = P.b b := fun a b h => congrArg _ (Fin.ext h)
  refine ⟨?_, ?_⟩
  · show ((D.R.t : ℚ) + 3) / 2 ≤ ((wd D j τ).e : ℚ) - (wd D j τ).b ((j : ℕ) + 1)
    rw [wd_b D j τ _ ⟨by omega, by omega⟩, wd_e, hb _ j (by simp)]
    exact P.gap_be j
  · intro hj'
    have hj'' : (j : ℕ) + 1 < D.R.m := hj'
    show ((D.R.t : ℚ) + 3) / 2 ≤ ((wd D j τ).b ((j : ℕ) + 1 + 1) : ℚ) - (wd D j τ).e
    rw [wd_b D j τ _ ⟨by omega, by omega⟩, wd_e, hb _ ⟨(j : ℕ) + 1, hj''⟩ (by simp)]
    exact P.gap_eb j hj''

end GlobalTheory.LiftWeightForced

namespace GlobalTheory.LiftWeightForced

open Formalism.IndefR.IndefiniteWeightData

variable (D : D7) (j : Fin D.R.m) (τ : D.what₂.Tau)

theorem exists_isLamPrime :
    ∃ lam : DomWeight (Vc D j).rank, Formalism.IndefR.Bridge.IsLamPrime (D := D) lam ((j : ℕ) + 1) τ := by
  have hjm := j.2
  have hC := GlobalTheory.LowestKType.thetaSide (wd D j τ) (wd_hyp D j τ) (wd_gap D j τ)
  have hint := hC.2.2.2.1
  have hdom := hC.2.2.2.2.1
  have hN : (Vc D j).rank = (wd D j τ).nV := D.sp.V_rank _ (by omega) (by omega)

  have hmono : ∀ d a : ℕ, 1 ≤ a → a + d ≤ (wd D j τ).nV →
      (wd D j τ).lamPrime (a + d) ≤ (wd D j τ).lamPrime a := by
    intro d
    induction d with
    | zero => intro a _ _; simp
    | succ d ih =>
      intro a ha had
      have := hdom (a + d) (by omega) (by omega)
      rw [← add_assoc]
      exact this.trans (ih a ha (by omega))
  let w : Fin (Vc D j).rank → ℤ := fun i => (hint (i.1 + 1) (by omega) (by have := i.2; omega)).choose
  have hw : ∀ i, (w i : ℚ) = (wd D j τ).lamPrime (i.1 + 1) := fun i =>
    (hint (i.1 + 1) (by omega) (by have := i.2; omega)).choose_spec.symm
  have hanti : Antitone w := by
    intro a b hab
    have hab' : a.1 ≤ b.1 := hab
    have := hmono (b.1 - a.1) (a.1 + 1) (by omega) (by have := b.2; omega)
    rw [show a.1 + 1 + (b.1 - a.1) = b.1 + 1 by omega] at this
    have h' : (w b : ℚ) ≤ w a := by rw [hw, hw]; exact this
    exact_mod_cast h'
  refine ⟨⟨w, hanti⟩, ⟨by omega, by omega⟩, wd D j τ, rfl, rfl, rfl, rfl, ?_, ?_, ?_, ?_⟩
  · rw [wd_e]
    exact congrArg _ (Fin.ext (by simp))
  · intro a
    rw [wd_v D j τ _ ⟨by omega, by have := a.2; omega⟩]
    exact congrArg _ (Fin.ext (by simp))
  · intro a
    rw [wd_b D j τ _ ⟨by omega, by have := a.2; omega⟩]
    exact congrArg _ (Fin.ext (by simp))
  · intro i
    exact hw i

theorem isLamPrime_lamLdef :
    Formalism.IndefR.Bridge.IsLamPrime (D := D)
      (Formalism.IndefR.Bridge.lamLdef (D := D) (Vc D j).rank ((j : ℕ) + 1) τ) ((j : ℕ) + 1) τ := by
  have hex := exists_isLamPrime D j τ
  unfold Formalism.IndefR.Bridge.lamLdef
  rw [dif_pos hex]
  exact hex.choose_spec

end GlobalTheory.LiftWeightForced

theorem GlobalTheory.LiftWeightForced.atPts : GlobalTheory.BigOn.AtPts fun Fm x _ i _ => ∀ (j : Fin (Fm.D x i).R.m) τ,
    Formalism.IndefR.Bridge.IsLamPrime (D := Fm.D x i)
      (Formalism.IndefR.Bridge.lamLdef (D := Fm.D x i) (Formalism.IndefR.Links.Vc (Fm.D x i) j).rank ((j : ℕ) + 1) τ) ((j : ℕ) + 1) τ :=
  ⟨1, one_pos, fun _ _ _ => ⟨⟨0, fun _ => 0, fun _ => 0, fun _ => 0⟩, fun Fm _ _ _ =>
    EvPt.of_forall fun x _ i _ _ _ j τ => GlobalTheory.LiftWeightForced.isLamPrime_lamLdef (Fm.D x i) j τ⟩⟩
