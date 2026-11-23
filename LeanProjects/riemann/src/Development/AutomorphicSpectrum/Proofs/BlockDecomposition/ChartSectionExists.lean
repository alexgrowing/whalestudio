import Mathlib
import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinContinuation.EisensteinChartSplitting.TChartSplit
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ContinuousStandardUnitaryChartAndSymmStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsStandardUnitaryChartDoubledSpaceStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.StandardUnitaryChartMemRationalIffStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemDoublingSiegelParabolicIffChartMemSiegelUnnStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.StandardUnitaryChartSiegelLeviDetEqStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsSiegelParabolicConjDoubledCompactStatement
open ResidueKilled.Tr
open scoped NNReal Matrix TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.TChartProof

open Matrix

theorem mat_mul' {D : D7} {n : ℕ} (g h : G D n) : mat (g * h) = mat g * mat h := by
  simp only [mat, map_mul, Units.val_mul]

theorem mat_one' {D : D7} {n : ℕ} : mat (1 : G D n) = 1 := by
  simp only [mat, map_one, Units.val_one]

theorem blkA_mul_of_lowerLeft {R : Type} [CommRing R] {n : ℕ} (X Y : Matrix (Fin (n + n)) (Fin (n + n)) R)
    (hY : ∀ i j : Fin n, Y (Fin.natAdd n i) (Fin.castAdd n j) = 0) : blkA (X * Y) = blkA X * blkA Y := by
  ext i j
  simp only [blkA, Matrix.mul_apply, Fin.sum_univ_add, hY, mul_zero, Finset.sum_const_zero, add_zero,
    toBlocks₁₁, Matrix.of_apply, submatrix_apply, finSumFinEquiv_apply_left]

theorem blkA_one' {R : Type} [CommRing R] {n : ℕ} : blkA (1 : Matrix (Fin (n + n)) (Fin (n + n)) R) = 1 := by
  ext i j
  simp [blkA, toBlocks₁₁, Matrix.one_apply]

theorem exists_gl_blkA {D : D7} {n : ℕ} {g : G D n} (hg : g ∈ P D n) :
    ∃ a : GL (Fin n) (AE D), blkA (mat g) = a.1 := by
  have hg' : g⁻¹ ∈ P D n := inv_mem hg
  have e₁ : blkA (mat g) * blkA (mat g⁻¹) = 1 := by
    rw [← blkA_mul_of_lowerLeft _ _ (chart_lowerLeft_zero hg'), ← mat_mul', mul_inv_cancel, mat_one', blkA_one']
  have e₂ : blkA (mat g⁻¹) * blkA (mat g) = 1 := by
    rw [← blkA_mul_of_lowerLeft _ _ (chart_lowerLeft_zero hg), ← mat_mul', inv_mul_cancel, mat_one', blkA_one']
  exact ⟨⟨_, _, e₁, e₂⟩, rfl⟩

theorem tChart : TChart := by
  intro hDict hDI hStd D χ V a hMaj
  obtain ⟨m0, hm0, hp0⟩ := GlobalTheory.T.exists_siegel_parabolic_conj_doubled_compact D
  obtain ⟨κ, hκ⟩ := GlobalTheory.T.exists_standardUnitaryChart_doubledSpace D V m0 hm0
  obtain ⟨p, hp⟩ := hp0 V a hMaj κ hκ
  obtain ⟨hc, hc'⟩ := GlobalTheory.T.continuous_standardUnitaryChart_and_symm D V m0 hm0 κ hκ
  obtain ⟨Ψ, h1, h2, h3, h4⟩ := hStd hDict hDI D χ V.rank
  have hG := GlobalTheory.T.standardUnitaryChart_mem_rational_iff D V m0 hm0 κ hκ
  have hP := GlobalTheory.T.mem_doublingSiegelParabolic_iff_chart_mem_siegelUnn D V m0 hm0 κ hκ
  let κt : GA D (dblSp V) ≃ₜ* G D V.rank :=
    { κ with continuous_toFun := hc, continuous_invFun := hc' }
  have hκt : ∀ g, κt g = κ g := fun _ => rfl
  refine ⟨κt.trans Ψ, p, fun g => ?_, fun g => ?_, fun k => ?_, fun q => ?_, fun x => ?_⟩
  · exact (hG g).trans (h1 (κ g))
  · exact (hP g).trans (h2 (κ g))
  · exact (hp k).trans (h3 _)
  · obtain ⟨b, hb⟩ := exists_gl_blkA ((hP q).1 q.2)
    have e₁ := GlobalTheory.T.standardUnitaryChart_siegelLeviDet_eq D V m0 hm0 κ hκ q b hb
    have e₂ := h4 (κ q) b hb
    rw [e₁]
    exact e₂
  · have e := (hDict D.host.F D.host.E).2.2.2.2 x
    show Real.log _ = _
    rw [e]

end GlobalTheory.CompanionTheory.TChartProof
