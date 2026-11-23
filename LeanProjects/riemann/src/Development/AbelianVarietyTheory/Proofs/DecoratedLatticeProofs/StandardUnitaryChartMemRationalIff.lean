import Development.AbelianVarietyTheory.Definitions.LatticeFrames.HalfData
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitaryConvergent
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoubledBasisSkewColumnMatrixGramInverseStatement
open scoped Matrix NNReal ComplexConjugate TensorProduct ContDiff
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.Core.Rk.SWLaw GlobalTheory.Core.Rk.SW GlobalTheory.StdUnn
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (RealMat IsFockVec)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.StdUnn.ChartRat

variable {D : D7}

theorem mem_GF_iff {n : ℕ} (g : G D n) : g ∈ GF D n ↔ mat g ∈ ratMx D (n + n) (n + n) := by
  constructor
  · rintro ⟨γ, -, h⟩
    exact ⟨γ.1, congrArg Units.val h⟩
  · rintro ⟨γ, hγ⟩
    replace hγ : rat γ = mat g := hγ
    have h : γᴴ * Jst D n * γ = Jst D n := by
      apply rat_injective
      rw [rat_mul, rat_mul, rat_conjTranspose, hγ]
      exact g.2
    have hdet : γ.det ≠ 0 := by
      intro h0
      have hu : IsUnit (mat g).det := Matrix.isUnits_det_units _
      rw [← hγ, rat, ← RingHom.mapMatrix_apply, ← RingHom.map_det, h0, map_zero] at hu
      have h01 : (0 : AE D) = 1 := isUnit_zero_iff.1 hu
      exact zero_ne_one (incA_injective (D := D) (by rw [map_zero, map_one]; exact h01))
    exact ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero γ hdet, h, Units.ext hγ⟩

end GlobalTheory.StdUnn.ChartRat

namespace GlobalTheory.StdUnn

theorem chart_mem_GF_iff : ∀ (D : D7) (A : HSp D) (μ : D.host.E), IsSkew μ → ∀ κ : GA D (dblSp A) ≃* G D A.rank,
    IsChart A μ κ → ∀ g, g ∈ GQ (dblSp A) ↔ κ g ∈ GF D A.rank := by
  intro D A μ hμ κ hκ g
  obtain ⟨-, hdet, -⟩ := GlobalTheory.T.doubledBasisSkewColumnMatrix_gram_inverse D A μ hμ
  have hTi : rat (Tm A μ)⁻¹ * rat (Tm A μ) = 1 := by
    rw [← rat_mul, Matrix.nonsing_inv_mul _ hdet, rat_one]
  have hTi' : rat (Tm A μ) * rat (Tm A μ)⁻¹ = 1 := by
    rw [← rat_mul, Matrix.mul_nonsing_inv _ hdet, rat_one]
  have e1 : mat (κ g) = rat (Tm A μ)⁻¹ * (mt (dblSp A) g * rat (Tm A μ)) := by
    rw [← hκ g, ← Matrix.mul_assoc, hTi, Matrix.one_mul]
  have e2 : mt (dblSp A) g = rat (Tm A μ) * mat (κ g) * rat (Tm A μ)⁻¹ := by
    rw [hκ g, Matrix.mul_assoc, hTi', Matrix.mul_one]
  rw [GlobalTheory.MixModel.mem_GQ_iff, ChartRat.mem_GF_iff]
  constructor
  · intro h
    rw [e1]
    exact ratMx_mul (rat_mem _) (ratMx_mul h (rat_mem _))
  · intro h
    rw [e2]
    exact ratMx_mul (ratMx_mul (rat_mem _) h) (rat_mem _)

end GlobalTheory.StdUnn
