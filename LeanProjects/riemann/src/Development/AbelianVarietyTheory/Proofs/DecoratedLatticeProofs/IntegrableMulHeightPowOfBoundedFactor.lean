import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CartFrSgn
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ChainParSucc
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RealMatrixCoeffFockVectorsLeDoublingHeightPowStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaInnerFockProductEqProdRealPlacesStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IntegralRealUnitaryHaarEqProdUpqHaarStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoublingHeightAtRealPlaceContinuousPosLeOneStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaChainStepWeilDatumNonzeroFockVacuumStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.Chain GlobalTheory.ChainFr GlobalTheory.PairLift GlobalTheory.Chain.RealIt
open scoped TensorProduct InnerProductSpace ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem GlobalTheory.realZeta_integrable_mul_heightPow : ∀ {G : Type} [MeasurableSpace G] [TopologicalSpace G] [OpensMeasurableSpace G] (μ : Measure G) (z m : G → ℂ) (H : G → ℝ) (C : ℝ) (b t : ℕ), Integrable z μ → Integrable m μ → Continuous H → (∀ g, 0 < H g ∧ H g ≤ 1) → t ≤ b → (∀ g, ‖z g‖ ≤ C * H g ^ ((b : ℝ) / 2) * ‖m g‖) → Integrable (fun g => z g * ((H g : ℝ) : ℂ) ^ (((0 : ℝ) : ℂ) - (t : ℂ) / 2)) μ := by
  intro G _ _ _ μ z m H C b t hz hm hH hpos htb hbound
  have hmeas : AEStronglyMeasurable (fun g => z g * ((H g : ℝ) : ℂ) ^ (((0:ℝ):ℂ) - (t:ℂ)/2)) μ := by
    refine hz.aestronglyMeasurable.mul ?_
    exact ((Complex.measurable_ofReal.comp hH.measurable).pow_const _).aestronglyMeasurable
  refine Integrable.mono' (hm.norm.const_mul (max C 0)) hmeas ?_
  refine Filter.Eventually.of_forall (fun g => ?_)
  obtain ⟨h0, h1⟩ := hpos g
  have hre : (((0:ℝ):ℂ) - (t:ℂ)/2).re = -(t:ℝ)/2 := by simp; ring
  have hcpow : ‖((H g : ℝ) : ℂ) ^ (((0:ℝ):ℂ) - (t:ℂ)/2)‖ = H g ^ (-(t:ℝ)/2) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos h0, hre]
  rw [norm_mul, hcpow]
  have hw : 0 ≤ H g ^ (-(t:ℝ)/2) := Real.rpow_nonneg h0.le _
  have hprod : H g ^ ((b:ℝ)/2) * H g ^ (-(t:ℝ)/2) = H g ^ (((b:ℝ) - t)/2) := by
    rw [← Real.rpow_add h0]; ring_nf
  have htb' : (t:ℝ) ≤ b := by exact_mod_cast htb
  have hle1 : H g ^ (((b:ℝ) - t)/2) ≤ 1 := Real.rpow_le_one h0.le h1 (by linarith)
  have hnn : 0 ≤ H g ^ (((b:ℝ) - t)/2) := Real.rpow_nonneg h0.le _
  calc ‖z g‖ * H g ^ (-(t:ℝ)/2) ≤ C * H g ^ ((b:ℝ)/2) * ‖m g‖ * H g ^ (-(t:ℝ)/2) :=
        mul_le_mul_of_nonneg_right (hbound g) hw
    _ = C * (H g ^ ((b:ℝ)/2) * H g ^ (-(t:ℝ)/2)) * ‖m g‖ := by ring
    _ = C * H g ^ (((b:ℝ) - t)/2) * ‖m g‖ := by rw [hprod]
    _ ≤ max C 0 * ‖m g‖ := by
        apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
        calc C * H g ^ (((b:ℝ) - t)/2) ≤ max C 0 * H g ^ (((b:ℝ) - t)/2) :=
              mul_le_mul_of_nonneg_right (le_max_left _ _) hnn
          _ ≤ max C 0 * 1 := mul_le_mul_of_nonneg_left hle1 (le_max_right _ _)
          _ = max C 0 := mul_one _
