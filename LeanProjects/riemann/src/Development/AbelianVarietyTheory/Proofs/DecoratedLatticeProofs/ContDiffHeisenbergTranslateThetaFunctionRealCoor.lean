import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsQuasiFam
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ThetaAbsoluteSum
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.TransvectionAction
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.WeilDatumExistence
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ContinuousResTSymm
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ComplexEmbeddingHermitianQuadrupleSum
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ContinuousIsotropicSandwichMeanTranslation
import Development.AbelianVarietyTheory.Proofs.HeightProofs.SmoothIffRealCoordinatesAndRealLines
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsInverseChart
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsInfFamFamily
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.ThetaTranslate

open GlobalTheory.FockCompare GlobalTheory.OrientedHeis

theorem hasDerivAt_expLine {H : ℝ → ℂ} {h' : ℂ} (hH : HasDerivAt H h' 0) (a k : ℝ) :
    HasDerivAt (fun s : ℝ => Complex.exp (-(Real.pi * Complex.I) * ((a + s * k : ℝ) : ℂ)) * H s)
      (Complex.exp (-(Real.pi * Complex.I) * (a : ℂ)) * (-(Real.pi * Complex.I) * (k : ℂ) * H 0 + h')) 0 := by
  have h1 : HasDerivAt (fun s : ℝ => a + s * k) k 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).mul_const k).const_add a
  have h2 : HasDerivAt (fun s : ℝ => ((a + s * k : ℝ) : ℂ)) (k : ℂ) 0 := h1.ofReal_comp
  have h3 := ((h2.const_mul (-(Real.pi * Complex.I))).cexp).mul hH
  exact h3.congr_deriv (by simp only [zero_mul, add_zero]; ring)

theorem contDiff_heisO_iota_fderiv : ∀ (D : D7) (θ : InfFam D) (σ : (D.what₂.Tau → ℂ) →+ AE D), GlobalTheory.FockCompare.Chart θ σ → ∀ (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D) (F : WO S T → ℂ), IsThetaFunO ψ S T F → ∀ v : WO S T, ContDiff ℝ ∞ (fun z : GlobalTheory.FockCompare.RW T S => heisO ψ S T (GlobalTheory.FockCompare.iotaW σ T S z) F v) ∧ ∀ z u : GlobalTheory.FockCompare.RW T S, fderiv ℝ (fun z : GlobalTheory.FockCompare.RW T S => heisO ψ S T (GlobalTheory.FockCompare.iotaW σ T S z) F v) z u = (Real.pi * Complex.I) * ((GlobalTheory.OrientedHeis.omO S T z u : ℝ) : ℂ) * heisO ψ S T (GlobalTheory.FockCompare.iotaW σ T S z) F v + heisO ψ S T (GlobalTheory.FockCompare.iotaW σ T S z) (fun y => deriv (fun s : ℝ => heisO ψ S T (GlobalTheory.FockCompare.iotaW σ T S (s • u)) F y) 0) v := by
  intro D θ σ h ψ hψ S T F hF v
  have hG : ContDiff ℝ ∞ fun x : RW T S => F (v + iotaW σ T S x) := theta_sm h hF v
  have eg : (fun z : RW T S => heisO ψ S T (iotaW σ T S z) F v) = fun z =>
      Complex.exp (-(Real.pi * Complex.I) * (Complex.ofRealCLM (omO S T (piW θ T S v) z))) *
        F (v + iotaW σ T S z) := by
    funext z; rw [heisO_iota h hψ]; rfl
  have hsm : ContDiff ℝ ∞ (fun z : RW T S => heisO ψ S T (iotaW σ T S z) F v) := by
    rw [eg]
    exact (Complex.contDiff_exp.comp (contDiff_const.mul (Complex.ofRealCLM.contDiff.comp
      (LinearMap.toContinuousLinearMap (omO S T (piW θ T S v))).contDiff))).mul hG
  refine ⟨hsm, fun z u => ?_⟩
  have hHc : ContDiff ℝ ∞ fun x : RW T S => F ((v + iotaW σ T S z) + iotaW σ T S x) := theta_sm h hF _
  have hH : HasDerivAt (fun s : ℝ => F ((v + iotaW σ T S z) + iotaW σ T S (s • u)))
      (deriv (fun s : ℝ => F ((v + iotaW σ T S z) + iotaW σ T S (s • u))) 0) 0 :=
    ((hHc.comp (contDiff_id.smul contDiff_const)).differentiable (by simp) 0).hasDerivAt
  have hline : HasDerivAt (fun s : ℝ => heisO ψ S T (iotaW σ T S (z + s • u)) F v)
      (Complex.exp (-(Real.pi * Complex.I) * ((omO S T (piW θ T S v) z : ℝ) : ℂ)) *
        (-(Real.pi * Complex.I) * ((omO S T (piW θ T S v) u : ℝ) : ℂ) *
          F ((v + iotaW σ T S z) + iotaW σ T S ((0 : ℝ) • u)) +
          deriv (fun s : ℝ => F ((v + iotaW σ T S z) + iotaW σ T S (s • u))) 0)) 0 := by
    have eline : (fun s : ℝ => heisO ψ S T (iotaW σ T S (z + s • u)) F v) = fun s =>
        Complex.exp (-(Real.pi * Complex.I) * ((omO S T (piW θ T S v) z + s * omO S T (piW θ T S v) u : ℝ) : ℂ)) *
          F ((v + iotaW σ T S z) + iotaW σ T S (s • u)) := by
      funext s
      rw [heisO_iota h hψ, (omO S T (piW θ T S v)).map_add, LinearMap.map_smul, smul_eq_mul, (iotaW σ T S).map_add,
        add_assoc]
    rw [eline]
    exact hasDerivAt_expLine hH _ _
  have hf : HasDerivAt (fun s : ℝ => heisO ψ S T (iotaW σ T S (z + s • u)) F v)
      (fderiv ℝ (fun z : RW T S => heisO ψ S T (iotaW σ T S z) F v) z u) 0 := by
    have hd : HasFDerivAt (fun z : RW T S => heisO ψ S T (iotaW σ T S z) F v)
        (fderiv ℝ (fun z : RW T S => heisO ψ S T (iotaW σ T S z) F v) z) (z + (0 : ℝ) • u) := by
      rw [zero_smul, add_zero]; exact (hsm.differentiable (by simp) z).hasFDerivAt
    have hl : HasDerivAt (fun s : ℝ => z + s • u) u 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).smul_const u).const_add z
    exact hd.comp_hasDerivAt (0 : ℝ) hl
  have hF' : HasDerivAt (fun s : ℝ => heisO ψ S T (iotaW σ T S (s • u)) F (v + iotaW σ T S z))
      (Complex.exp (-(Real.pi * Complex.I) * ((0 : ℝ) : ℂ)) *
        (-(Real.pi * Complex.I) * ((omO S T (piW θ T S v) u + omO S T z u : ℝ) : ℂ) *
          F ((v + iotaW σ T S z) + iotaW σ T S ((0 : ℝ) • u)) +
          deriv (fun s : ℝ => F ((v + iotaW σ T S z) + iotaW σ T S (s • u))) 0)) 0 := by
    have eF : (fun s : ℝ => heisO ψ S T (iotaW σ T S (s • u)) F (v + iotaW σ T S z)) = fun s =>
        Complex.exp (-(Real.pi * Complex.I) *
          ((0 + s * (omO S T (piW θ T S v) u + omO S T z u) : ℝ) : ℂ)) *
          F ((v + iotaW σ T S z) + iotaW σ T S (s • u)) := by
      funext s
      rw [heisO_iota h hψ, (piW θ T S).map_add, h.pi_iota, LinearMap.map_smul, smul_eq_mul, (omO S T).map_add,
        LinearMap.add_apply, zero_add]
    rw [eF]
    exact hasDerivAt_expLine hH _ _
  rw [hf.unique hline, heisO_iota h hψ z F v, heisO_iota h hψ z _ v]
  beta_reduce
  rw [hF'.deriv]
  simp only [zero_smul, map_zero, add_zero, Complex.ofReal_zero, mul_zero, Complex.exp_zero, one_mul,
    Complex.ofReal_add]
  ring

end GlobalTheory.ThetaTranslate

end
