import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.RowsPtAt
import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.FamilyStatementOfItemsFourSeven
import Formalism.SharpRestriction.CuspSpanNormBounds.AbsoluteAmplitudeSecondOfSource
import Formalism.SharpRestriction.CuspSpanNormBounds.BranchingAndRankConstants
import Formalism.SharpRestriction.CuspSpanNormBounds.SBridge
import Development.AbelianVarietyTheory.Statements.DiscreteSeriesShifts.ThmBpDS
import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.FormalDegreeCompactDualIff
import Formalism.SharpRestriction.CuspSpanNormBounds.StandingHypothesesHoldFamily
import Formalism.SharpRestriction.CuspSpanNormBounds.BesselShellMomentBounds
import Formalism.SharpRestriction.CuspSpanNormBounds.LatticeGluingRadicals
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.BridgeLemma GlobalTheory.Core.Deg

namespace GlobalTheory.Core.Deg

theorem elementary_size_bounds_of_size_hypotheses : ∀ M : ℝ, ∃ thr : ℝ, ∀ (D : D7) (large₂ : SizeData₂ D) (C' Cl Cg cb Cu cT CT : ℝ),
    thr ≤ C' → thr ≤ Cl → StandingHypotheses D large₂ C' Cl Cg cb Cu cT CT → 1000 ≤ Cl ∧ M ≤ Cl ∧ M ≤ (D.R.m : ℝ) ∧
    M ≤ (D.R.k : ℝ) ∧ D.host.rdE ≤ large₂.sc.b ∧ (D.R.k : ℝ) ^ M ≤ large₂.sc.b ∧ (D.R.r : ℝ) ≤ large₂.sc.b ∧
    (D.R.m : ℝ) ^ 2 ≤ D.R.k ∧ M * (D.R.m : ℝ) ^ 5 * D.R.f * large₂.sc.L ≤ D.R.k := by
  intro M
  refine ⟨max 1000 (2 * |M|), ?_⟩
  intro D large₂ C' Cl Cg cb Cu cT CT hC' hCl h
  have hMabs : M ≤ |M| := le_abs_self M
  have hM0 : 0 ≤ |M| := abs_nonneg M
  have hCl1000 : 1000 ≤ Cl := le_trans (le_max_left _ _) hCl
  have hCl2M : 2 * |M| ≤ Cl := le_trans (le_max_right _ _) hCl
  have hC'M : M ≤ C' := by linarith [le_trans (le_max_right _ _) hC']
  obtain ⟨-, hk, hmf, hfk, -, -, hm2L, -, -, -, hrd, -, -, -, -, hbj, -, -, -, -, -, -, -, hClm, -⟩ := h
  have hL : 1 < large₂.sc.L := Formalism.MainNotions.S.one_lt_scL large₂
  have hlogb : Real.log large₂.sc.b = large₂.sc.L := Formalism.MainNotions.S.log_scb large₂
  have hb2 : 2 ≤ large₂.sc.b := Formalism.MainNotions.S.two_le_scb large₂
  have hm2 : 2 ≤ D.R.m := D.R.two_le_m
  have hmk : D.R.m + 3 ≤ D.R.k := D.R.m_add_three_le_k
  have hmkR : (D.R.m : ℝ) + 3 ≤ D.R.k := by exact_mod_cast hmk
  have hm : (2 : ℝ) ≤ D.R.m := by exact_mod_cast hm2
  have hk1 : (1 : ℝ) ≤ D.R.k := by linarith
  have hf16 : 16 ≤ D.R.f := le_trans (by
    calc 16 = 2 ^ 4 := by norm_num
      _ ≤ D.R.m ^ 4 := Nat.pow_le_pow_left hm2 4) hmf
  have hcard : 0 < Fintype.card D.what₂.Tau := by
    rw [← Formalism.MainNotions.BesselShellMomentBounds.card_places D, Formalism.MainNotions.LatticeGluingRadicals.d_card D]; omega
  obtain ⟨τ⟩ := Fintype.card_pos_iff.1 hcard
  have hb1 := hbj τ 1 le_rfl (by omega)

  have hkb2 : (D.R.k : ℝ) ^ Cl ≤ large₂.sc.b ^ (2 : ℝ) := le_trans (le_trans (le_max_left _ _) hb1.1) hb1.2
  have hb0 : 0 ≤ large₂.sc.b := by linarith

  have hkhalf : (D.R.k : ℝ) ^ (Cl / 2) ≤ large₂.sc.b := by
    have e1 : (D.R.k : ℝ) ^ (Cl / 2) = ((D.R.k : ℝ) ^ Cl) ^ ((1 : ℝ) / 2) := by
      rw [← Real.rpow_mul (by linarith)]; ring_nf
    have e2 : large₂.sc.b = (large₂.sc.b ^ (2 : ℝ)) ^ ((1 : ℝ) / 2) := by
      rw [← Real.rpow_mul hb0]; norm_num
    rw [e1, e2]
    exact Real.rpow_le_rpow (by positivity) hkb2 (by norm_num)
  have hkM : (D.R.k : ℝ) ^ M ≤ large₂.sc.b :=
    le_trans (Real.rpow_le_rpow_of_exponent_le hk1 (by linarith)) hkhalf
  have hk2 : (D.R.k : ℝ) ^ (2 : ℝ) ≤ large₂.sc.b :=
    le_trans (Real.rpow_le_rpow_of_exponent_le hk1 (by linarith)) hkhalf
  rw [Real.rpow_two] at hk2
  have hr : (D.R.r : ℝ) ≤ large₂.sc.b := by
    have e : (D.R.r : ℝ) = (D.R.k : ℝ) + D.R.m - 1 := by
      unfold Formalism.BasicNotions.Ranks.r; push_cast [show 1 ≤ D.R.k + D.R.m by omega]; ring
    rw [e]; nlinarith
  have hmL : (D.R.m : ℝ) ^ 2 ≤ D.R.k := by
    have h0 : 0 ≤ (D.R.m : ℝ) ^ 2 := by positivity
    have a1 : (D.R.m : ℝ) ^ 2 ≤ Cl * (D.R.m : ℝ) ^ 2 := le_mul_of_one_le_left h0 (by linarith)
    have a2 : Cl * (D.R.m : ℝ) ^ 2 ≤ Cl * ((D.R.m : ℝ) ^ 2 * large₂.sc.L) := by
      have : (D.R.m : ℝ) ^ 2 ≤ (D.R.m : ℝ) ^ 2 * large₂.sc.L := le_mul_of_one_le_right h0 hL.le
      exact mul_le_mul_of_nonneg_left this (by linarith)
    linarith
  have hrdb : D.host.rdE ≤ large₂.sc.b := by
    rcases le_or_gt D.host.rdE 0 with hneg | hpos
    · linarith
    · have hLCl : large₂.sc.L / Cl ≤ large₂.sc.L := div_le_self (by linarith) (by linarith)
      have hlog : Real.log D.host.rdE ≤ Real.log large₂.sc.b := by rw [hlogb]; linarith
      exact (Real.log_le_log_iff hpos (by linarith)).1 hlog
  have hX0 : 0 ≤ (D.R.m : ℝ) ^ 5 * D.R.f * large₂.sc.L := by positivity
  have hMk : M * (D.R.m : ℝ) ^ 5 * D.R.f * large₂.sc.L ≤ D.R.k := by
    have a : M * ((D.R.m : ℝ) ^ 5 * D.R.f * large₂.sc.L) ≤ C' * ((D.R.m : ℝ) ^ 5 * D.R.f * large₂.sc.L) :=
      mul_le_mul_of_nonneg_right hC'M hX0
    have e1 : M * (D.R.m : ℝ) ^ 5 * D.R.f * large₂.sc.L = M * ((D.R.m : ℝ) ^ 5 * D.R.f * large₂.sc.L) := by ring
    have e2 : C' * (D.R.m : ℝ) ^ 5 * D.R.f * large₂.sc.L = C' * ((D.R.m : ℝ) ^ 5 * D.R.f * large₂.sc.L) := by ring
    linarith
  exact ⟨hCl1000, by linarith, by linarith, by linarith, hrdb, hkM, hr, hmL, hMk⟩

end GlobalTheory.Core.Deg
