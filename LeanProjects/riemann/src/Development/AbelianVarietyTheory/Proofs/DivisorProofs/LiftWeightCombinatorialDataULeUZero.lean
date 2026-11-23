import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AtPtsImp

set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links
open Formalism.CohomologicalDescent.LogSmallConstantBounds (Par)
open Formalism.CohomologicalDescent.ShortWeightBounds (Wts)

namespace GlobalTheory.ExpTie.Lift

variable {D : D7}

abbrev lamL (j : Fin D.R.m) (τ : D.what₂.Tau) : DomWeight (Vc D j).rank :=
  Formalism.IndefR.Bridge.lamLdef (D := D) (Vc D j).rank ((j : ℕ) + 1) τ

def lamT (j : Fin D.R.m) (τ : D.what₂.Tau) (a : ℕ) : ℕ :=
  if h : a < (Vc D j).rank then (lamL j τ).natW ⟨a, h⟩ else 0

def cT (j : Fin D.R.m) (τ : D.what₂.Tau) : ℝ :=
  ((Vc D j).rank : ℝ) / 2 - 1 - ((lamL j τ).detShift : ℝ)

open Classical in

def wts (L : SizeData₂ D) (j : Fin D.R.m) : Wts D.what₂.Tau where
  lam := lamT j
  T2 := Finset.univ.filter fun τ => (D.eTau τ : D.R.GG) ∈ D.host.thickPlaces
  j := fun _ => (j : ℕ) + 1
  q := fun _ => D.R.m - ((j : ℕ) + 1)
  xm := fun τ => ⌈cT j τ⌉
  xp := fun τ => ⌊cT j τ + L.Sc⌋
  c := cT j
  e := fun τ => wj D ((j : ℕ) + 1) τ
  fr := fun _ τ => τ
  cj := fun _ _ => false
  Sp := Formalism.MainNotions.JumpSetsAlt.excSet D

def ValsAt (L : SizeData₂ D) (j : Fin D.R.m) (τ : D.what₂.Tau) : Prop :=
  (∀ (a : ℕ) (ha : a < D.R.k - 1),
      ((wts L j).U (parOf L j) τ a : ℝ) - (wts L j).c τ = (((D.hc τ).v ⟨a, ha⟩ : ℚ) : ℝ)) ∧
    (∀ i : Fin D.R.m, (i : ℕ) ≤ j →
      ((wts L j).U (parOf L j) τ (D.R.k - 1 + i) : ℝ) - (wts L j).c τ = -(((D.hc τ).b i : ℚ) : ℝ)) ∧
    (∀ s : ℕ, s < D.R.t →
      ((wts L j).U (parOf L j) τ (D.R.k + j + s) : ℝ) - (wts L j).c τ =
        -wj D ((j : ℕ) + 1) τ + ((D.R.t : ℝ) - 1) / 2 - s) ∧
    (∀ i : Fin D.R.m, (j : ℕ) < i →
      ((wts L j).U (parOf L j) τ (D.R.k - 1 + i + D.R.t) : ℝ) - (wts L j).c τ = -(((D.hc τ).b i : ℚ) : ℝ))

end GlobalTheory.ExpTie.Lift

namespace GlobalTheory.ExpTie.Lift

open Formalism.IndefR.Bridge

variable {D : D7}

theorem lamT_of_lt (j : Fin D.R.m) (τ : D.what₂.Tau) (a : ℕ) (h : a < (Vc D j).rank) :
    (lamT j τ a : ℤ) = (lamL j τ).w ⟨a, h⟩ - (lamL j τ).detShift := by
  have hn : 0 < (Vc D j).rank := by omega
  have hle : (lamL j τ).detShift ≤ (lamL j τ).w ⟨a, h⟩ := by
    unfold DomWeight.detShift
    rw [dif_pos hn]
    exact (lamL j τ).anti (Fin.mk_le_mk.2 (by omega))
  unfold lamT DomWeight.natW
  rw [dif_pos h]
  omega

theorem anti (L : SizeData₂ D) (j : Fin D.R.m) : ∀ τ a b, a ≤ b → b < (parOf L j).Nr → (wts L j).lam τ b ≤ (wts L j).lam τ a := by
  intro τ a b hab hb
  have ha : a < (Vc D j).rank := lt_of_le_of_lt hab hb
  have h1 := lamT_of_lt j τ a ha
  have h2 := lamT_of_lt j τ b hb
  have h3 := (lamL j τ).anti (show (⟨a, ha⟩ : Fin _) ≤ ⟨b, hb⟩ from Fin.mk_le_mk.2 hab)
  show lamT j τ b ≤ lamT j τ a
  omega

theorem rank_eq (j : Fin D.R.m) : (Vc D j).rank = D.R.k - 1 + D.R.m + D.R.t := by
  have h := D.sp.V_rank ((j : ℕ) + 1) (by omega) (by omega)
  have hk := D.R.m_add_three_le_k
  simp only [Vc, h, Ranks.nV, Ranks.r]
  omega

theorem what₂ (L : SizeData₂ D) (j : Fin D.R.m) : ∀ τ, Formalism.CohomologicalDescent.ShortWeightBounds.kc (parOf L j) + (wts L j).j τ + (parOf L j).t + (wts L j).q τ = (parOf L j).Nr := by
  intro τ
  have := rank_eq j
  have hj := j.2
  simp only [Formalism.CohomologicalDescent.ShortWeightBounds.kc, parOf, wts]
  omega

end GlobalTheory.ExpTie.Lift

namespace GlobalTheory.ExpTie.Lift

open Formalism.IndefR.Bridge

variable {D : D7}

theorem U_last (L : SizeData₂ D) (j : Fin D.R.m) (τ : D.what₂.Tau) :
    (wts L j).U (parOf L j) τ ((Vc D j).rank - 1) = 0 := by
  have hn := rank_eq j
  have ht0 := D.R.t_odd.pos
  have hlt : (Vc D j).rank - 1 < (Vc D j).rank := by omega
  have h1 := lamT_of_lt j τ _ hlt
  have h2 : (lamL j τ).detShift = (lamL j τ).w ⟨(Vc D j).rank - 1, hlt⟩ := by
    unfold DomWeight.detShift; rw [dif_pos (by omega)]
  show Formalism.CohomologicalDescent.UnitNormBounds.UN (Vc D j).rank (lamT j τ) ((Vc D j).rank - 1) = 0
  unfold Formalism.CohomologicalDescent.UnitNormBounds.UN
  omega

theorem liftWeightCombinatorialData_U_le_U_zero (L : SizeData₂ D) (j : Fin D.R.m) (τ : D.what₂.Tau) (a : ℕ) (ha : a < (Vc D j).rank) :
    (wts L j).U (parOf L j) τ a ≤ (wts L j).U (parOf L j) τ 0 := by
  have h := anti L j τ 0 a (Nat.zero_le _) ha
  show Formalism.CohomologicalDescent.UnitNormBounds.UN (Vc D j).rank (lamT j τ) a ≤ Formalism.CohomologicalDescent.UnitNormBounds.UN (Vc D j).rank (lamT j τ) 0
  change lamT j τ a ≤ lamT j τ 0 at h
  unfold Formalism.CohomologicalDescent.UnitNormBounds.UN
  omega

theorem U_nonneg (L : SizeData₂ D) (j : Fin D.R.m) (τ : D.what₂.Tau) (a : ℕ) (ha : a < (Vc D j).rank) :
    0 ≤ (wts L j).U (parOf L j) τ a := by
  show 0 ≤ Formalism.CohomologicalDescent.UnitNormBounds.UN (Vc D j).rank (lamT j τ) a
  unfold Formalism.CohomologicalDescent.UnitNormBounds.UN
  omega

theorem T2_card (L : SizeData₂ D) (j : Fin D.R.m) : (wts L j).T2.card ≤ D.host.T2.card := by
  classical
  calc (wts L j).T2.card ≤ D.host.thickPlaces.card := by
        refine Finset.card_le_card_of_injOn (fun τ => (D.eTau τ : D.R.GG)) ?_ ?_
        · intro τ hτ
          simp only [wts, Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hτ
          exact hτ
        · intro a _ b _ h
          exact D.eTau.injective (Subtype.ext h)
    _ ≤ D.host.T2.card := by
        unfold Host.thickPlaces
        exact Finset.card_image_le

theorem c_le (L : SizeData₂ D) (j : Fin D.R.m) (τ : D.what₂.Tau) (hv : ValsAt L j τ) :
    (wts L j).c τ ≤ wj D D.R.m τ + ((D.R.t : ℝ) - 1) / 2 := by
  have hn := rank_eq j
  have hU := U_last L j τ
  have ht : (1 : ℝ) ≤ D.R.t := by exact_mod_cast D.R.t_odd.pos
  have ht0 := D.R.t_odd.pos
  have hk := D.R.m_add_three_le_k
  have hm2 := D.R.two_le_m
  have hm : 0 < D.R.m := by omega
  by_cases hj : (j : ℕ) + 1 < D.R.m
  · have h := hv.2.2.2 ⟨D.R.m - 1, by omega⟩ (by simp; omega)
    have hrow : D.R.k - 1 + (D.R.m - 1) + D.R.t = (Vc D j).rank - 1 := by omega
    simp only [hrow, hU] at h
    have hg := (D.hc τ).gap_be ⟨D.R.m - 1, by omega⟩
    have hw : wj D D.R.m τ = (((D.hc τ).e ⟨D.R.m - 1, by omega⟩ : ℚ) : ℝ) := by
      unfold wj; rw [dif_pos (by omega)]
    have hg' : (((D.hc τ).b ⟨D.R.m - 1, by omega⟩ : ℚ) : ℝ) + ((D.R.t : ℝ) + 3) / 2 ≤
        (((D.hc τ).e ⟨D.R.m - 1, by omega⟩ : ℚ) : ℝ) := by
      have h2 : ((((D.hc τ).e ⟨D.R.m - 1, by omega⟩ - (D.hc τ).b ⟨D.R.m - 1, by omega⟩ : ℚ)) : ℝ) ≥ ((((D.R.t : ℚ) + 3) / 2 : ℚ) : ℝ) := by
        exact_mod_cast hg
      push_cast at h2
      linarith
    push_cast at h
    rw [hw]; linarith
  · have hjm : (j : ℕ) + 1 = D.R.m := by omega
    have h := hv.2.2.1 (D.R.t - 1) (by omega)
    have hrow : D.R.k + (j : ℕ) + (D.R.t - 1) = (Vc D j).rank - 1 := by omega
    simp only [hrow, hU] at h
    have hts : ((D.R.t - 1 : ℕ) : ℝ) = (D.R.t : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega)]; simp
    rw [hts, hjm] at h
    push_cast at h
    linarith

end GlobalTheory.ExpTie.Lift

end
