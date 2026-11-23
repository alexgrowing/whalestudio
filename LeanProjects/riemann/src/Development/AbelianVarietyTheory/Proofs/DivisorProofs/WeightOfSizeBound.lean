import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.TieTest
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.SizeAt
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain
open Formalism.L2 Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim

namespace GlobalTheory.BigTop.Fun

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open GlobalTheory.FunObj.SqNum GlobalTheory.SignedHC

section Arith

variable {D : D7}

theorem rankV_lt_gap {i j : ℕ} (hi : i < D.R.m) (hj : j < D.R.m) : rankV D (i + 1) (j + 1) < gap D 1 := by
  have h1 : (j + 1) * D.R.t ≤ D.R.m * D.R.t := Nat.mul_le_mul_right _ hj
  have h2 : (i + 1) * sLen D ≤ D.R.m * sLen D := Nat.mul_le_mul_right _ hi
  have h3 : rankV D (i + 1) (j + 1) ≤ bigN D := by
    have hr : D.R.r = D.R.k + D.R.m - 1 := rfl
    have hk := D.R.m_add_three_le_k
    unfold rankV bigN
    rw [mul_add, mul_add, mul_one]
    omega
  have h4 := (isLeast_gap D 1).1.2.1
  have h5 : bigN D ≤ bigN D ^ 3 := Nat.le_self_pow (by norm_num) _
  omega

theorem numE_bounds {L : SizeData₂ D} (hs : GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup.SizeRows L) (τ : D.what₂.Tau) {j : ℕ} (hj : j < D.R.m) :
    0 ≤ (num D 1 τ).e (j + 1) ∧ ((num D 1 τ).e (j + 1) : ℝ) ≤ 4 * L.sc.b := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, hbe, -⟩ := hs
  have e1 : (D.hc τ).e ⟨j, hj⟩ = ((num D 1 τ).e (j + 1) : ℚ) :=
    (GridData.ofHCParam_spec (D.hc τ) (sLen D) (gap D 1) (cen D 1 τ)).2.2 ⟨j, hj⟩
  obtain ⟨hb0, he4⟩ := hbe τ ⟨j, hj⟩
  have hg := (D.hc τ).gap_be ⟨j, hj⟩
  have ht : (0 : ℚ) ≤ D.R.t := by positivity
  rw [e1] at hg he4
  refine ⟨?_, by exact_mod_cast he4⟩
  have : (0 : ℚ) ≤ ((num D 1 τ).e (j + 1) : ℚ) := by linarith
  exact_mod_cast this

theorem cen_bounds {L : SizeData₂ D} (hs : GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup.SizeRows L) (τ : D.what₂.Tau) {i : ℕ} (h1 : 1 ≤ i)
    (h2 : i ≤ D.R.m) : 0 ≤ cen D 1 τ i ∧ (cen D 1 τ i : ℝ) ≤ L.sc.b := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hgap, -, -⟩ := hs
  set G0 := GridData.ofHCParam (D.hc τ) (sLen D) (gap D 1) 0 with hG0
  have hk := D.R.m_add_three_le_k
  have ev : (D.hc τ).v ⟨0, by omega⟩ = (G0.v 2 : ℚ) :=
    (GridData.ofHCParam_spec (D.hc τ) (sLen D) (gap D 1) 0).1 ⟨0, by omega⟩
  obtain ⟨v0, v1⟩ := L.cloud_v τ ⟨0, by omega⟩
  rw [ev] at v0 v1
  have hmid : G0.mid i = (G0.v 2 : ℚ) + 1 / 2 + ((D.R.m : ℚ) + 1 - i) * (gap D 1 : ℚ) + (gap D 1 : ℚ) / 2 :=
    G0.mid_eq h1
  have hc : cen D 1 τ i = ⌊G0.mid i⌋ := rfl
  have hS := L.Sc_pos
  have hi1 : (1 : ℝ) ≤ i := by exact_mod_cast h1
  have hi2 : (i : ℝ) ≤ D.R.m := by exact_mod_cast h2
  have hγ : (0 : ℝ) ≤ gap D 1 := by positivity
  have hmR : ((G0.mid i : ℚ) : ℝ) = (G0.v 2 : ℝ) + 1 / 2 + ((D.R.m : ℝ) + 1 - i) * (gap D 1 : ℝ) + (gap D 1 : ℝ) / 2 := by
    rw [hmid]; push_cast; ring
  have v0' : (0 : ℝ) ≤ (G0.v 2 : ℝ) := by exact_mod_cast v0
  have v1' : (G0.v 2 : ℝ) ≤ L.Sc := by exact_mod_cast v1
  have m0 : (0 : ℝ) ≤ ((G0.mid i : ℚ) : ℝ) := by
    rw [hmR]; have : (0 : ℝ) ≤ ((D.R.m : ℝ) + 1 - i) * (gap D 1 : ℝ) := mul_nonneg (by linarith) hγ
    linarith
  have m1 : ((G0.mid i : ℚ) : ℝ) ≤ L.sc.b := by
    rw [hmR]
    have : ((D.R.m : ℝ) + 1 - i) * (gap D 1 : ℝ) + (gap D 1 : ℝ) / 2 ≤ ((D.R.m : ℝ) + 1) * gap D 1 := by nlinarith
    linarith
  have m0q : (0 : ℚ) ≤ G0.mid i := by exact_mod_cast m0
  refine ⟨hc ▸ Int.floor_nonneg.2 m0q, ?_⟩
  have hf : ((⌊G0.mid i⌋ : ℚ) : ℝ) ≤ ((G0.mid i : ℚ) : ℝ) := by exact_mod_cast Int.floor_le (G0.mid i)
  rw [hc]
  push_cast at hf ⊢
  linarith

theorem gap_le_b {L : SizeData₂ D} (hs : GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup.SizeRows L) : (gap D 1 : ℝ) ≤ L.sc.b ∧ 675 ≤ L.sc.b := by
  obtain ⟨-, -, -, hm, -, -, -, -, -, -, -, hgap, -, -⟩ := hs
  have hS := L.Sc_pos
  have h4 := (isLeast_gap D 1).1.2.1
  have h15 : 15 ≤ gap D 1 := by have : 6 ≤ sLen D := by unfold sLen; omega
                                omega
  have hγ : (15 : ℝ) ≤ gap D 1 := by exact_mod_cast h15
  have hm' : (44 : ℝ) ≤ D.R.m := by exact_mod_cast hm
  constructor <;> nlinarith

theorem maxWt_le {L : SizeData₂ D} (hs : GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup.SizeRows L) :
    1 ≤ (maxWt D 1 : ℝ) ∧ (maxWt D 1 : ℝ) ≤ 10 * L.sc.b ∧ 675 ≤ L.sc.b := by
  obtain ⟨hγb, hb⟩ := gap_le_b hs
  have key : ∀ x : Fin D.R.m × Fin D.R.m × D.what₂.Tau,
      max (wtA D 1 x.1 x.2.1 x.2.2).natAbs (wtA' D 1 x.1 x.2.1 x.2.2).natAbs ≤ ⌊10 * L.sc.b⌋₊ := by
    rintro ⟨i, j, τ⟩
    have hr := rankV_lt_gap (D := D) i.2 j.2
    have hij : rankV D i j ≤ rankV D (i + 1) (j + 1) := by unfold rankV; gcongr <;> omega
    have hbs : botSmall D i j ≤ rankV D (i + 1) (j + 1) := by unfold botSmall; omega
    have hbb : botBig D i j ≤ rankV D (i + 1) (j + 1) := by unfold botBig; omega
    have hp : rankV D i j % 2 ≤ 1 := Nat.le_of_lt_succ (Nat.mod_lt _ (by norm_num))
    obtain ⟨e0, e1⟩ := numE_bounds hs τ j.2
    obtain ⟨c0, c1⟩ := cen_bounds hs τ (i := D.R.m - i) (by omega) (by omega)
    dsimp only
    refine max_le (Nat.le_floor ?_) (Nat.le_floor ?_)
    · have hA : |wtA D 1 i j τ| ≤ 2 * (num D 1 τ).e (j + 1) + 1 + gap D 1 := by
        rw [abs_le]
        unfold wtA
        constructor <;> omega
      have hA' : |((wtA D 1 i j τ : ℤ) : ℝ)| ≤ 2 * ((num D 1 τ).e (j + 1) : ℝ) + 1 + (gap D 1 : ℝ) := by
        exact_mod_cast hA
      rw [Nat.cast_natAbs, Int.cast_abs]
      linarith
    · have hA : |wtA' D 1 i j τ| ≤ 2 * cen D 1 τ (D.R.m - i) + 1 + gap D 1 := by
        rw [abs_le]
        unfold wtA'
        constructor <;> omega
      have hA' : |((wtA' D 1 i j τ : ℤ) : ℝ)| ≤ 2 * (cen D 1 τ (D.R.m - i) : ℝ) + 1 + (gap D 1 : ℝ) := by
        exact_mod_cast hA
      rw [Nat.cast_natAbs, Int.cast_abs]
      linarith
  have hsup : maxWt D 1 ≤ max 1 ⌊10 * L.sc.b⌋₊ := max_le_max le_rfl (Finset.sup_le fun x _ => key x)
  have hfl : (⌊10 * L.sc.b⌋₊ : ℝ) ≤ 10 * L.sc.b := Nat.floor_le (by linarith)
  refine ⟨by exact_mod_cast le_max_left 1 _, ?_, hb⟩
  have : (maxWt D 1 : ℝ) ≤ ((max 1 ⌊10 * L.sc.b⌋₊ : ℕ) : ℝ) := by exact_mod_cast hsup
  rw [Nat.cast_max, Nat.cast_one] at this
  exact this.trans (max_le (by linarith) hfl)

end Arith

theorem wt_tie (h : SizeAt) : Wt @Comparison₂ := by
  obtain ⟨e, he, h⟩ := h
  refine ⟨0, fun CF _ => ⟨e, he, fun eps h1 h2 => ?_⟩⟩
  obtain ⟨K, hK⟩ := h eps h1 h2
  refine ⟨K, fun Fm CH hc hL _ => ⟨10, fun C hC => ?_⟩⟩
  obtain ⟨x0, hx0⟩ := hK Fm CH hc hL
  refine ⟨x0, fun x hx hle i p hp d hd => ?_⟩
  have hs := hx0 x hx hle i p hp
  obtain ⟨-, a, ha⟩ := hd
  have hw : d.Bw = (maxWt _ 1 : ℝ) := ha.sq.weight
  obtain ⟨w1, w2, hb⟩ := maxWt_le hs
  have eb : p.Z.b = (Fm.L x i).sc.b := rfl
  show 1 ≤ d.Bw ∧ d.Bw ≤ C * p.Z.b ∧ Real.log d.Bw ≤ C * Real.log p.Z.b
  rw [hw, eb]
  have hb0 : 0 < (Fm.L x i).sc.b := by linarith
  have l10 : Real.log 10 ≤ Real.log (Fm.L x i).sc.b := Real.log_le_log (by norm_num) (by linarith)
  have l0 : 0 ≤ Real.log (Fm.L x i).sc.b := l10.trans' (Real.log_nonneg (by norm_num))
  refine ⟨w1, w2.trans (by nlinarith), ?_⟩
  calc Real.log (maxWt _ 1 : ℝ) ≤ Real.log (10 * (Fm.L x i).sc.b) := Real.log_le_log (by linarith) w2
    _ = Real.log 10 + Real.log (Fm.L x i).sc.b := Real.log_mul (by norm_num) hb0.ne'
    _ ≤ 2 * Real.log (Fm.L x i).sc.b := by linarith
    _ ≤ C * Real.log (Fm.L x i).sc.b := by nlinarith

end GlobalTheory.BigTop.Fun

end
