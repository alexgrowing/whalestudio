import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.DuStarPos
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SpreadLe
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AssembleLattice
import Formalism.SharpRestriction.InertJacobiLevels.HostFam
open Formalism.BasicNotions NumberField IsDedekindDomain GlobalTheory.Mem

namespace GlobalTheory.Mem

def hcStdU (k Del : ℕ) (uF uL : ℤ) (c : Fin (k - 2) → Bool) (i : ℕ) : ℚ :=
  if i = 0 then (uF : ℚ) + 1 / 2
  else if h : i - 1 < k - 2 then
    ((k - 2 - (i - 1) : ℕ) : ℚ) * (4 * (Del : ℚ)) - 1 / 2 - (if c ⟨i - 1, h⟩ then (Del : ℚ) else 0)
  else (uL : ℚ) + 1 / 2

theorem hcStdU_zero (k Del : ℕ) (uF uL : ℤ) (c : Fin (k - 2) → Bool) :
    hcStdU k Del uF uL c 0 = (uF : ℚ) + 1 / 2 := by simp [hcStdU]

theorem hcStdU_succ (k Del : ℕ) (uF uL : ℤ) (c : Fin (k - 2) → Bool) (l : ℕ) (h : l < k - 2) :
    hcStdU k Del uF uL c (l + 1) =
      ((k - 2 - l : ℕ) : ℚ) * (4 * (Del : ℚ)) - 1 / 2 - (if c ⟨l, h⟩ then (Del : ℚ) else 0) := by
  unfold hcStdU
  rw [if_neg (Nat.succ_ne_zero l), dif_pos (by simpa using h)]
  rfl

theorem hcStdU_last (k Del : ℕ) (uF uL : ℤ) (c : Fin (k - 2) → Bool) (i : ℕ) (h0 : i ≠ 0)
    (h : ¬ i - 1 < k - 2) : hcStdU k Del uF uL c i = (uL : ℚ) + 1 / 2 := by
  unfold hcStdU
  rw [if_neg h0, dif_neg h]

theorem exists_hcParam_std : ∀ (R : Ranks) (Del hh : ℕ) (uF uL b1 : ℤ), 1 ≤ Del → R.t + 3 ≤ 2 * hh → ((R.k - 2 : ℕ) : ℤ) * (4 * Del) ≤ uF → uL ≤ -1 → -b1 ≤ uL → ∀ c : Fin (R.k - 2) → Bool, ∃ P : HCParam R, (∀ i : Fin (R.k - 1), (P).v i = ((R.k - 2 - i.1 : ℕ) : ℚ) * (4 * (Del : ℚ))) ∧ (∀ j : Fin R.m, (P).b j = (b1 : ℚ) + (j.1 : ℚ) * (2 * hh : ℚ) ∧ (P).e j = (P).b j + hh) ∧ (∀ h : 0 < R.k, (P).u ⟨0, h⟩ = (uF : ℚ) + 1 / 2 ∧ (P).u ⟨R.k - 1, by omega⟩ = (uL : ℚ) + 1 / 2) ∧ ∀ (l : ℕ) (h : l < R.k - 2), (P).u ⟨l + 1, by omega⟩ = (P).v ⟨l, by omega⟩ - 1 / 2 - (if c ⟨l, h⟩ then (Del : ℚ) else 0) := by
  intro R Del hh uF uL b1 hD hhh hF hL hb c
  have hk := R.m_add_three_le_k
  have hm := R.two_le_m
  have hDq : (1 : ℚ) ≤ Del := by exact_mod_cast hD
  have hhq : (R.t : ℚ) + 3 ≤ 2 * hh := by exact_mod_cast hhh
  have hFq : ((R.k - 2 : ℕ) : ℚ) * (4 * (Del : ℚ)) ≤ uF := by exact_mod_cast hF
  have hLq : (uL : ℚ) ≤ -1 := by exact_mod_cast hL
  have hbq : -(b1 : ℚ) ≤ uL := by exact_mod_cast hb
  refine ⟨{
    u := fun i => hcStdU R.k Del uF uL c i.1
    v := fun i => ((R.k - 2 - i.1 : ℕ) : ℚ) * (4 * (Del : ℚ))
    b := fun j => (b1 : ℚ) + (j.1 : ℚ) * (2 * hh : ℚ)
    e := fun j => (b1 : ℚ) + (j.1 : ℚ) * (2 * hh : ℚ) + hh
    u_gt_v := ?_
    v_gt_u := ?_
    u_last_gt := ?_
    gap_be := ?_
    gap_eb := ?_
    e_int := ?_
    u_half := ?_
    v_int := ?_
    b_int := ?_ }, fun i => rfl, fun j => ⟨rfl, rfl⟩, fun h => ⟨?_, ?_⟩, fun l h => ?_⟩
  · rintro ⟨i, hi⟩
    rcases i with _ | l
    · simp only [hcStdU_zero, Nat.sub_zero]
      linarith
    · have hl : l < R.k - 2 := by omega
      simp only [hcStdU_succ _ _ _ _ _ l hl]
      have : R.k - 2 - l = (R.k - 2 - (l + 1)) + 1 := by omega
      rw [this]
      push_cast
      split_ifs <;> linarith
  · rintro ⟨i, hi⟩
    by_cases hl : i < R.k - 2
    · simp only [hcStdU_succ _ _ _ _ _ i hl]
      split_ifs <;> linarith
    · simp only
      rw [hcStdU_last _ _ _ _ _ _ (by omega) (by simpa using hl)]
      have : R.k - 2 - i = 0 := by omega
      rw [this]
      push_cast
      linarith
  · intro h h'
    simp only
    rw [hcStdU_last _ _ _ _ _ _ (by omega) (by omega)]
    push_cast
    linarith
  · intro j
    linarith
  · intro j h
    push_cast
    linarith
  · intro j
    exact ⟨b1 + j.1 * (2 * hh) + hh, by push_cast; ring⟩
  · rintro ⟨i, hi⟩
    rcases i with _ | l
    · exact ⟨uF, hcStdU_zero _ _ _ _ _⟩
    · by_cases hl : l < R.k - 2
      · refine ⟨((R.k - 2 - l : ℕ) : ℤ) * (4 * Del) - 1 - (if c ⟨l, hl⟩ then (Del : ℤ) else 0), ?_⟩
        simp only [hcStdU_succ _ _ _ _ _ l hl]
        split_ifs <;> push_cast <;> ring
      · exact ⟨uL, hcStdU_last _ _ _ _ _ _ (by simp) (by simpa using hl)⟩
  · intro i
    exact ⟨((R.k - 2 - i.1 : ℕ) : ℤ) * (4 * Del), by push_cast; ring⟩
  · intro j
    exact ⟨b1 + j.1 * (2 * hh), by push_cast; ring⟩
  · exact hcStdU_zero R.k Del uF uL c
  · exact hcStdU_last R.k Del uF uL c (R.k - 1) (by omega) (by omega)
  · exact hcStdU_succ R.k Del uF uL c l h

end GlobalTheory.Mem
