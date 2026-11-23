import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsQuasiFam
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.RealSizeNonneg
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.UnifModGrowthOfIsUnifModerate
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ThetaAbsoluteSum
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.TransvectionAction
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.WeilDatumExistence
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisenbergSupSobolevSeminormThetaLawsStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DualDirectionDerivativeMixedCoordinateBoundStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicMatrixRealSizeLeRealSymplecticPairingSumStatement
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.EqZeroOfLintegralEqZero

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf
open scoped ComplexOrder ENNReal NNReal ContDiff

namespace GlobalTheory.Unf

theorem mixS_decay : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ θ : InfFam D, IsInfFam θ → ∀ (S S₀ T : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ) (v : VolM D T.rank ρ) (N : ℕ), ∃ C : ℝ≥0, ∀ f : WO S T → ℂ, IsThetaFunO ψ S T f → ∀ x w, ‖d.mixS T ψ v.μ v.𝓕 f x w‖ₑ * ENNReal.ofReal ((1 + realSize θ x) ^ N) ≤ C * supSob ψ θ N f := by
  intro D ψ hψ θ hθ S S₀ T ρ d v N
  obtain ⟨k, τs, zs, K, hK⟩ := GlobalTheory.T.adelicMatrixRealSize_le_realSymplecticPairing_sum D θ T ρ
  choose Z hZ using fun i => GlobalTheory.T.dualDirection_derivative_mixedCoordinate_bound D ψ hψ θ hθ S S₀ T ρ d v (τs i) (zs i)
  have hsf := GlobalTheory.T.heisenberg_sup_sobolev_seminorm_theta_laws D ψ hψ θ hθ S T
  choose Cd hCd using fun i => (hsf.2.1 (τs i) (Z i)).2
  induction N with
  | zero =>
    refine ⟨1, fun f hf x w => ?_⟩
    rw [pow_zero, ENNReal.ofReal_one, mul_one, ENNReal.coe_one, one_mul]
    have hs : supSob ψ θ 0 f = ⨆ w, ‖f w‖ₑ := GlobalTheory.Size.wordSum_zero _ _ _
    rw [hs]
    unfold HypDec.mixS
    calc _ ≤ ∫⁻ a in v.𝓕, ‖heisO ψ S T (d.extY T a) (heisO ψ S T (d.extX T x) (heisO ψ S T (d.ext0 T w) f)) 0‖ₑ ∂v.μ :=
          enorm_integral_le_lintegral_enorm _
      _ ≤ ∫⁻ _ in v.𝓕, (⨆ w, ‖f w‖ₑ) ∂v.μ := lintegral_mono fun a => by
          rw [d.integrandS_eq, enorm_mul]
          have h1 : ‖ψ (symplOH S T (d.extY T a) (d.extX T x))‖ₑ = 1 := by
            rw [← ofReal_norm_eq_enorm, hψ.1.2.1, ENNReal.ofReal_one]
          rw [h1, one_mul]
          exact le_iSup (fun w => ‖f w‖ₑ) _
      _ = _ := by rw [setLIntegral_const, v.covol.2.2, mul_one]
  | succ N ih =>
    obtain ⟨C, hC⟩ := ih
    refine ⟨C + K.toNNReal * ∑ i, C * Cd i, fun f hf x w => ?_⟩
    set R := realSize θ x with hRdef
    have hR0 : 0 ≤ R := realSize_nonneg θ x
    set M := d.mixS T ψ v.μ v.𝓕 f x w
    set s := supSob ψ θ (N + 1) f
    have hNs : supSob ψ θ N f ≤ s := GlobalTheory.Size.wordSum_mono (Nat.le_succ N) f
    have hpow : ENNReal.ofReal ((1 + R) ^ (N + 1)) =
        ENNReal.ofReal ((1 + R) ^ N) + ENNReal.ofReal R * ENNReal.ofReal ((1 + R) ^ N) := by
      rw [← ENNReal.ofReal_mul hR0, ← ENNReal.ofReal_add (by positivity) (by positivity)]
      congr 1
      ring
    have hA : ‖M‖ₑ * ENNReal.ofReal ((1 + R) ^ N) ≤ C * s := (hC f hf x w).trans (by gcongr)
    have hRle : ENNReal.ofReal R ≤ K.toNNReal * ∑ i, ENNReal.ofReal |2 * (tauE D (τs i) D.host.xi0 *
        ((compAt θ (τs i) x)ᴴ * gramAt D T (τs i) * zs i).trace).re| := by
      refine (ENNReal.ofReal_le_ofReal (hK x)).trans (le_of_eq ?_)
      rw [ENNReal.ofReal_mul' (Finset.sum_nonneg fun i _ => abs_nonneg _),
        ENNReal.ofReal_sum_of_nonneg fun i _ => abs_nonneg _]
      rfl
    have hi : ∀ i, ENNReal.ofReal |2 * (tauE D (τs i) D.host.xi0 *
        ((compAt θ (τs i) x)ᴴ * gramAt D T (τs i) * zs i).trace).re| * (‖M‖ₑ * ENNReal.ofReal ((1 + R) ^ N)) ≤
        C * Cd i * s := fun i => by
      have hDf := GlobalTheory.OrientedHeis.theta_dRho hθ hψ (τs i) (Z i) hf
      rw [← mul_assoc, ← ofReal_norm_eq_enorm, ← ENNReal.ofReal_mul (abs_nonneg _)]
      calc _ ≤ ‖d.mixS T ψ v.μ v.𝓕 (dRho (heisO ψ S T) θ (τs i) (Z i) f) x w‖ₑ * ENNReal.ofReal ((1 + R) ^ N) := by
            gcongr
            rw [← ofReal_norm_eq_enorm]
            exact ENNReal.ofReal_le_ofReal (hZ i f hf x w)
        _ ≤ C * supSob ψ θ N (dRho (heisO ψ S T) θ (τs i) (Z i) f) := hC _ hDf x w
        _ ≤ C * (Cd i * s) := by gcongr; exact hCd i N f hf
        _ = C * Cd i * s := (mul_assoc _ _ _).symm
    calc ‖M‖ₑ * ENNReal.ofReal ((1 + R) ^ (N + 1))
        = ‖M‖ₑ * ENNReal.ofReal ((1 + R) ^ N) + ENNReal.ofReal R * (‖M‖ₑ * ENNReal.ofReal ((1 + R) ^ N)) := by
          rw [hpow, mul_add, mul_left_comm]
      _ ≤ C * s + (K.toNNReal * ∑ i, ENNReal.ofReal |2 * (tauE D (τs i) D.host.xi0 *
            ((compAt θ (τs i) x)ᴴ * gramAt D T (τs i) * zs i).trace).re|) * (‖M‖ₑ * ENNReal.ofReal ((1 + R) ^ N)) :=
          add_le_add hA (by gcongr)
      _ ≤ C * s + K.toNNReal * ∑ i, (C * Cd i * s : ℝ≥0∞) := by
          rw [mul_assoc, Finset.sum_mul]
          exact add_le_add le_rfl (mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ => hi i) zero_le)
      _ = _ := by
          push_cast
          rw [add_mul, mul_assoc, Finset.sum_mul]

end GlobalTheory.Unf

end
