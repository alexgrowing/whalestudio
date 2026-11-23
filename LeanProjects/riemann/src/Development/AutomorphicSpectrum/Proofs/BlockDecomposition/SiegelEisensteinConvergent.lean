import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.WeilThetaConvergence
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.WeilSiegelFormula
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsSiegelParabolicConjDoubledCompact
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsStandardUnitaryChartDoubledSpace
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.StandardUnitaryChartMemRationalIff
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemDoublingSiegelParabolicIffChartMemSiegelUnn
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsWeilDatumTransportSchwartzBruhatStandard
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TransportedSchrodingerStandardLeviAction
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TransportedSchrodingerSiegelUnipotentAction
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeylFormulaStandardUnitaryGroupWeilDatum
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ShiftedAdditiveCharacterArchimedeanParameters
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsHeckeCharRestrictionEtaInv
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaKernelEqTsumSchrodingerFunction
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CosetSumAlongMulEquivSubgroups
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoubledFlatSectionEqTranslateStandardSection
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SchrodingerThetaEqSchwartzBruhat
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SiegelWeilFockDoubledPairOfWeilAndIchino
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SiegelParabolicUnnMatrixBlockUpperTriangular
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IwasawaDecompositionUnitary
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ContinuousLeviBlock
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsArchEquivEq
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MixSDblDecZero
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.LeftInvOfIsSection
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SiegelWeilSectionIntegrableAndContinuous
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.HalfData
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbsoluteThetaIntegralLeContinuousSeminormStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegrableThetaKernelWeilRangeStatement
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.WeilSiegelFormulaUnitary
open scoped TensorProduct ENNReal Matrix Classical NNReal
open MeasureTheory NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Doubling GlobalTheory.Eis GlobalTheory GlobalTheory.SiegelFormula
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.AdelicU GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.Core.Rk.SWLaw GlobalTheory.Core.Rk.SW GlobalTheory.StdUnn
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)

noncomputable section

namespace GlobalTheory.CompanionTheory.Godement

open GlobalTheory.StdUnn.HeightExists GlobalTheory.StdUnn.PolesModel

theorem cosetConv_of_continuous_law : ∀ (D : D7) (n : ℕ) (χ : (AE D)ˣ →* Circle) (s₁ : ℂ) (φ : G D n → ℂ), Continuous φ →
    (∀ p ∈ P D n, ∀ a : GL (Fin n) (AE D), blkA (mat p) = a.1 → ∀ g,
      φ (p * g) = (χ (Matrix.GeneralLinearGroup.det a) : ℂ) *
        npow (absA D (Matrix.GeneralLinearGroup.det a)) (s₁ + (n : ℂ) / 2) * φ g) →
    (n : ℝ) / 2 < s₁.re → ∀ g : G D n, CosetConv (P D n) (GF D n) φ g := by
  intro D n χ s₁ φ hcont hlaw hs g
  obtain ⟨H, φ₀, -, -, hH, hsec, hne⟩ :=
    GlobalTheory.StdUnn.PolesModel.hypotheses_hold D n 0 (s₁.re : ℂ)
  have hconv0 := GlobalTheory.StdUnn.PolesModel.cosetConv_stdSec hH hsec
    (s := (s₁.re : ℂ)) (by simpa using hs) g
  have hstd : GlobalTheory.StdUnn.stdSec H φ₀ (s₁.re : ℂ) (s₁.re : ℂ) = φ₀ := by
    funext x
    simp [GlobalTheory.StdUnn.stdSec, GlobalTheory.Doubling.npow]
  rw [hstd] at hconv0
  have hK : IsCompact (↑(GlobalTheory.StdUnn.K D n) : Set (G D n)) :=
    GlobalTheory.StdUnn.HeightExists.isCompact_K
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hcont.continuousOn
  have hC0 : 0 ≤ C := le_trans (norm_nonneg _) (hC 1 (GlobalTheory.StdUnn.K D n).one_mem)
  obtain ⟨k₀, -, hk₀⟩ := hK.exists_isMinOn ⟨1, (GlobalTheory.StdUnn.K D n).one_mem⟩
    hsec.2.1.norm.continuousOn
  have hc : 0 < ‖φ₀ k₀‖ := norm_pos_iff.mpr (hne k₀)
  have hχ : ∀ u : Circle, ‖(u : ℂ)‖ = 1 := fun u => by
    first
      | exact Circle.norm_coe u
      | exact mem_sphere_zero_iff_norm.mp u.2
      | simp [Circle.abs_coe]
  have key : ∀ x, ‖φ x‖ ≤ C / ‖φ₀ k₀‖ * ‖φ₀ x‖ := by
    intro x
    obtain ⟨p, hp, k, hk, rfl⟩ := GlobalTheory.StdUnn.Iwasawa.exists_mul D n x
    obtain ⟨a, ha⟩ := GlobalTheory.StdUnn.LeftInvSect.exists_blkA hp
    rw [hlaw p hp a ha k, hsec.1 p hp a ha k]
    have hu : IsUnit (GlobalTheory.Doubling.absA D (Matrix.GeneralLinearGroup.det a)) :=
      (Group.isUnit _).map _
    have hr : (0 : ℝ) < (GlobalTheory.Doubling.absA D (Matrix.GeneralLinearGroup.det a) : ℝ) :=
      NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hu.ne_zero)
    have hRR : ‖GlobalTheory.Doubling.npow (GlobalTheory.Doubling.absA D (Matrix.GeneralLinearGroup.det a))
          ((s₁.re : ℂ) + (n : ℂ) / 2)‖ =
        ‖GlobalTheory.Doubling.npow (GlobalTheory.Doubling.absA D (Matrix.GeneralLinearGroup.det a))
          (s₁ + (n : ℂ) / 2)‖ := by
      simp only [GlobalTheory.Doubling.npow]
      rw [Complex.norm_cpow_eq_rpow_re_of_pos hr, Complex.norm_cpow_eq_rpow_re_of_pos hr]
      congr 1 <;> simp
    have hb : ‖φ k‖ ≤ C / ‖φ₀ k₀‖ * ‖φ₀ k‖ := by
      refine le_trans (hC k hk) ?_
      calc C = C / ‖φ₀ k₀‖ * ‖φ₀ k₀‖ := (div_mul_cancel₀ C hc.ne').symm
        _ ≤ C / ‖φ₀ k₀‖ * ‖φ₀ k‖ :=
          mul_le_mul_of_nonneg_left (isMinOn_iff.mp hk₀ k hk) (div_nonneg hC0 hc.le)
    simp only [norm_mul, hχ, hRR]
    calc 1 * ‖GlobalTheory.Doubling.npow (GlobalTheory.Doubling.absA D (Matrix.GeneralLinearGroup.det a))
            (s₁ + (n : ℂ) / 2)‖ * ‖φ k‖
        ≤ 1 * ‖GlobalTheory.Doubling.npow (GlobalTheory.Doubling.absA D (Matrix.GeneralLinearGroup.det a))
            (s₁ + (n : ℂ) / 2)‖ * (C / ‖φ₀ k₀‖ * ‖φ₀ k‖) :=
          mul_le_mul_of_nonneg_left hb (by positivity)
      _ = C / ‖φ₀ k₀‖ * (1 * ‖GlobalTheory.Doubling.npow (GlobalTheory.Doubling.absA D
            (Matrix.GeneralLinearGroup.det a)) (s₁ + (n : ℂ) / 2)‖ * ‖φ₀ k‖) := by ring
  unfold GlobalTheory.Eis.CosetConv at hconv0 ⊢
  refine Summable.of_nonneg_of_le (fun q => norm_nonneg _) (fun q => ?_)
    (hconv0.mul_left (C / ‖φ₀ k₀‖))
  simp only [GlobalTheory.Eis.term]
  exact key _

end GlobalTheory.CompanionTheory.Godement

end
