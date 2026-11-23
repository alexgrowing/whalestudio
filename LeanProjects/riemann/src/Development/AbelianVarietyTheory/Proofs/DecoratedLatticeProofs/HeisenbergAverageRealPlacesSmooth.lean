import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsQuasiFam
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ThetaAbsoluteSum
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.TransvectionAction
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.WeilDatumExistence
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.AdjointIsotropicDecomposition
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ComplexEmbeddingHermitianQuadrupleSum
import Development.AbelianVarietyTheory.Proofs.HeightProofs.SmoothIffRealCoordinatesAndRealLines
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsInverseChart
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsInfFamFamily
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SmulEqZeroOfInf
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct ContDiff Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

noncomputable section

namespace GlobalTheory.HeisAverage

open GlobalTheory.FockCompare GlobalTheory.OrientedHeis

theorem contDiff_integral_kernel {R : Type} [NormedAddCommGroup R] [NormedSpace ℝ R] [FiniteDimensional ℝ R]
    [MeasurableSpace R] [BorelSpace R] (μ : Measure R) [μ.IsAddHaarMeasure]
    (φ : R → ℝ) (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ) (K : R → R → ℂ)
    (hK : ContDiff ℝ ∞ fun p : R × R => K p.1 p.2) (G : R → ℂ) (hG : Continuous G) :
    ContDiff ℝ ∞ fun y => ∫ x, (φ x : ℂ) * K y x * G (y + x) ∂μ := by
  set g : R → R → ℂ := fun p v => (φ (-v) : ℂ) * K p (-v) with hgdef
  have e : ∀ y, ∫ x, (φ x : ℂ) * K y x * G (y + x) ∂μ = convolution G (g y) (ContinuousLinearMap.mul ℝ ℂ) μ y := by
    intro y
    rw [convolution_def]
    simp only [ContinuousLinearMap.mul_apply', g, neg_sub]
    rw [← integral_sub_right_eq_self (fun x => (φ x : ℂ) * K y x * G (y + x)) y]
    congr 1
    funext t
    simp only [add_sub_cancel]
    ring
  have hk : IsCompact (Neg.neg '' tsupport φ) := hφc.isCompact.image continuous_neg
  have hgs : ∀ p, ∀ x, p ∈ (Set.univ : Set R) → x ∉ Neg.neg '' tsupport φ → g p x = 0 := by
    intro p x _ hx
    have : -x ∉ tsupport φ := fun h => hx ⟨-x, h, neg_neg x⟩
    simp [g, image_eq_zero_of_notMem_tsupport this]
  have hg : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (↿g) (Set.univ ×ˢ Set.univ) := by
    apply ContDiff.contDiffOn
    exact (Complex.ofRealCLM.contDiff.comp (hφ.comp contDiff_snd.neg)).mul
      (hK.comp (contDiff_fst.prodMk contDiff_snd.neg))
  have hc := contDiffOn_convolution_right_with_param_comp (μ := μ) (ContinuousLinearMap.mul ℝ ℂ)
    (s := Set.univ) (v := id) contDiffOn_id isOpen_univ hk hgs hG.locallyIntegrable hg
  rw [funext e]
  exact contDiffOn_univ.1 hc

theorem sm_heisO_average : ∀ (D : D7) (θ : InfFam D) (σ : (D.what₂.Tau → ℂ) →+ AE D), GlobalTheory.FockCompare.Chart θ σ → ∀ (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (A T : HSp D) (φ : GlobalTheory.FockCompare.RW T A → ℝ), ContDiff ℝ ∞ φ → HasCompactSupport φ → ∀ (f : WO A T → ℂ), Continuous f → GlobalTheory.FockCompare.Sm (GlobalTheory.FockCompare.iotaW σ T A) (fun w => ∫ x, (φ x : ℂ) * heisO ψ A T (GlobalTheory.FockCompare.iotaW σ T A x) f w) := by
  intro D θ σ h ψ hψ A T φ hφ hφc f hf w
  haveI : (volume : Measure (Fin A.rank → ℂ)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
  haveI : (volume : Measure (Fin T.rank → Fin A.rank → ℂ)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
  haveI : (volume : Measure (RW T A)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
  let Bc : RW T A →L[ℝ] RW T A →L[ℝ] ℝ := LinearMap.toContinuousLinearMap
    ((LinearMap.toContinuousLinearMap : (RW T A →ₗ[ℝ] ℝ) ≃ₗ[ℝ] (RW T A →L[ℝ] ℝ)).toLinearMap ∘ₗ omO A T)
  have hK : ContDiff ℝ ∞ fun p : RW T A × RW T A =>
      Complex.exp (-(Real.pi * Complex.I) * (Complex.ofRealCLM (Bc (piW θ T A w + p.1) p.2))) :=
    Complex.contDiff_exp.comp (contDiff_const.mul (Complex.ofRealCLM.contDiff.comp
      ((Bc.contDiff.comp (contDiff_const.add contDiff_fst)).clm_apply contDiff_snd)))
  have hG : Continuous fun t : RW T A => f (w + iotaW σ T A t) :=
    hf.comp (continuous_const.add (h.continuous_iota T A))
  have key := contDiff_integral_kernel (volume : Measure (RW T A)) φ hφ hφc
    (fun y x => Complex.exp (-(Real.pi * Complex.I) * (Complex.ofRealCLM (Bc (piW θ T A w + y) x)))) hK _ hG
  refine (congrArg (ContDiff ℝ ∞) ?_).mp key
  funext y
  refine congrArg _ ?_
  funext x
  rw [heisO_iota h hψ, (piW θ T A).map_add, h.pi_iota, (iotaW σ T A).map_add, ← add_assoc, mul_assoc]
  rfl

end GlobalTheory.HeisAverage
