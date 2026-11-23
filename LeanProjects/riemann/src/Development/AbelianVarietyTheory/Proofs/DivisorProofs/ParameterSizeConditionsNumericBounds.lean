import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HBdNonneg
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.PolyConstantLeZBasePowFour
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.TestLat GlobalTheory.SumSize GlobalTheory.RowClaim GlobalTheory.ClassCount

namespace GlobalTheory.SizesOfRows

theorem sizes_of_sizeRows : ∀ {D : D7} (large₂ : SizeData₂ D), GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup.SizeRows large₂ → (bigN D : ℝ) ≤ large₂.sc.b ∧ (D.R.f : ℝ) ≤ large₂.sc.b ∧ 1 ≤ bigN D ∧ 1 ≤ D.R.f ∧ 2 ≤ D.R.m ∧ 1 ≤ D.host.rdE ∧ Real.log D.host.rdE ≤ Real.log large₂.sc.b / 100 ∧ 12 ≤ large₂.sc.b := by
  intro D large₂ h
  obtain ⟨_, _, hm4, hm44, _, hb, _, _, _, hrd, hcond, _, _, _⟩ := h
  have hk : D.R.m + 3 ≤ D.R.k := D.R.m_add_three_le_k
  have ht : D.R.k + D.R.m - 1 + 5 ≤ D.R.t := D.R.rank_add_five_le
  have hd : 1 ≤ D.host.d := by have := D.host.qd_big.2; omega
  have hf : 1 ≤ D.R.f := by
    have : 1 ≤ D.R.m ^ 4 := Nat.one_le_pow _ _ (by omega)
    omega
  have hN1 : 1 ≤ D.R.N D.R.m := by simp only [Formalism.BasicNotions.Ranks.N]; omega
  have hbig2 : bigN D ≤ 2 * D.R.N D.R.m := by
    simp only [bigN, sLen, Formalism.BasicNotions.Ranks.N, Formalism.BasicNotions.Ranks.r]
    have h1 : D.R.k + D.R.m - 1 + 6 ≤ D.R.t + 1 := by omega
    have h2 : D.R.m * (D.R.k + D.R.m - 1 + 6) ≤ D.R.m * (D.R.t + 1) := Nat.mul_le_mul_left _ h1
    have e : D.R.m * (D.R.t + (D.R.k + D.R.m - 1 + 6) + 1) = D.R.m * (D.R.t + 1) + D.R.m * (D.R.k + D.R.m - 1 + 6) := by ring
    omega
  have hmR : (44 : ℝ) ≤ D.R.m := by exact_mod_cast hm44
  have hfR : (1 : ℝ) ≤ D.R.f := by exact_mod_cast hf
  have hNR : (1 : ℝ) ≤ (D.R.N D.R.m : ℝ) := by exact_mod_cast hN1
  have hdR : (1 : ℝ) ≤ (D.host.d : ℝ) := by exact_mod_cast hd
  have hbigR : (bigN D : ℝ) ≤ 2 * (D.R.N D.R.m : ℝ) := by exact_mod_cast hbig2
  have hN2 : (D.R.N D.R.m : ℝ) ≤ (D.R.N D.R.m : ℝ) ^ 2 := by nlinarith
  have hP1 : (D.R.m : ℝ) * (D.R.N D.R.m : ℝ) ≤ (D.R.m : ℝ) * D.R.f * (D.R.N D.R.m : ℝ) ^ 2 * D.host.d := by
    have a : (D.R.N D.R.m : ℝ) ≤ D.R.f * (D.R.N D.R.m : ℝ) ^ 2 * D.host.d := by
      have : (D.R.N D.R.m : ℝ) ^ 2 ≤ D.R.f * (D.R.N D.R.m : ℝ) ^ 2 := by nlinarith
      have : D.R.f * (D.R.N D.R.m : ℝ) ^ 2 ≤ D.R.f * (D.R.N D.R.m : ℝ) ^ 2 * D.host.d := by nlinarith
      linarith
    have := mul_le_mul_of_nonneg_left a (by linarith : (0:ℝ) ≤ D.R.m)
    linarith
  have hP2 : (D.R.f : ℝ) ≤ (D.R.m : ℝ) * D.R.f * (D.R.N D.R.m : ℝ) ^ 2 * D.host.d := by
    have : (1 : ℝ) ≤ (D.R.m : ℝ) * (D.R.N D.R.m : ℝ) ^ 2 * D.host.d := by
      have : (1:ℝ) ≤ (D.R.m : ℝ) * (D.R.N D.R.m : ℝ) ^ 2 := by nlinarith
      nlinarith
    nlinarith
  have hmN : 2 * (D.R.N D.R.m : ℝ) ≤ (D.R.m : ℝ) * (D.R.N D.R.m : ℝ) := by nlinarith
  have hrd1 : 1 ≤ D.host.rdE := Formalism.MainNotions.Gaps.EtaleWeightGaps.Num.Pm.one_le_rdE D
  have hlogb : Real.log large₂.sc.b = large₂.sc.L := by
    show Real.log (Real.exp large₂.sc.L) = large₂.sc.L
    exact Real.log_exp _
  refine ⟨by linarith, by linarith, by simp only [bigN]; omega, hf, by omega, hrd1, ?_, ?_⟩
  · rw [hlogb]; linarith
  · have : (12 : ℝ) ≤ (D.R.m : ℝ) * (D.R.N D.R.m : ℝ) := by nlinarith
    linarith

end GlobalTheory.SizesOfRows
