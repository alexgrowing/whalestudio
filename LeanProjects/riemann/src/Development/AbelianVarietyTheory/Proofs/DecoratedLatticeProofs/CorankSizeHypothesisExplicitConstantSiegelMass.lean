import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.RowsPtAt
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.CollSBound
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.LoopEvaluationThresholdZero
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.DegenerateConstant
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.LoopTerm
open scoped Classical
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.PackageTie2 Formalism.L2.SG.TermTieOf GlobalTheory.Core.Deg
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Core.Deg
theorem xiSizes_explicit : Formalism.HermitianLatticesTheory.SiegelMassRatio → ∀ C : ℝ, 408 * (Real.exp 1 * Real.pi) ≤ C → ∀ (D : D7) (large₂ : SizeData₂ D) (u u' : D.what₂.Word) (C' Cl Cg cb Cu cT CT C0 A : ℝ), 1 ≤ Cl → Cnt.Hyp D large₂ u u' C' Cl Cg cb Cu cT CT C0 A → Formalism.HermitianLatticeCounting.LatticeSumBounds.XiHyp C D.R.k (2 * D.R.rS + 2) D.R.f large₂.sc.b D.host.v (Cnt.NT D u) (BridgeLemma.XiB D large₂ u C) := by
  intro hS C hC D large₂ u u' C' Cl Cg cb Cu cT CT C0 A hCl hH
  have he : (1 : ℝ) ≤ Real.exp 1 * Real.pi := by
    have h1 : (1 : ℝ) ≤ Real.exp 1 := Real.one_le_exp (by norm_num)
    have h2 : (3 : ℝ) ≤ Real.pi := Real.pi_gt_three.le
    nlinarith
  have hmax : max 1 (1 / Cl) ≤ 1 := max_le le_rfl (by rw [div_le_one (by linarith)]; exact hCl)
  have hM2 := Formalism.MainNotions.BridgeLemma₂.plane_mass_bound_parameters D large₂ u u' C' Cl Cg cb Cu cT CT C0 A 8
    (le_trans (mul_le_mul_of_nonneg_left hmax (by norm_num)) (by norm_num))
  have hX := Formalism.MainNotions.BridgeLemma.first_bound_of_mass_ratio D large₂ u u' C' Cl Cg cb Cu cT CT C0 A 8 408
    (Formalism.MainNotions.BridgeLemma.lattice_count_first_of_siegel hS D) hM2 (by norm_num) le_rfl hCl
  have hCX : |(408 : ℝ)| * max 1 |Real.exp 1 * Real.pi| ≤ C := by
    rw [abs_of_pos (by norm_num : (0 : ℝ) < 408), abs_of_pos (by positivity), max_eq_right he]; exact hC
  have hXi := Formalism.MainNotions.BridgeLemma.xiHyp_of_stX D large₂ hH hX hCX (by linarith)
  rw [← Formalism.MainNotions.BridgeLemma.d_m_eq D]
  exact hXi
end GlobalTheory.Core.Deg
