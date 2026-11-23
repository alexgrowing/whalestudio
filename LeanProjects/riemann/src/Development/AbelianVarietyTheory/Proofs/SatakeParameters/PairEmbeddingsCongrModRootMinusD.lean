import Mathlib
import Formalism.SharpRestriction.Divisibility.OrbitPlaces
import Formalism.LocalToGlobal.TorsionIntegrality.GaussianEigenFrames.StatementJ
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.StdBases
import Formalism.LocalToGlobal.KernelLattices.KerStd
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaZJetsThree
import Formalism.LocalToGlobal.InertKernelTheory.StatementIota
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ColR
import Formalism.LocalToGlobal.TorsionIntegrality.GaussianEigenFrames.GramFrameComposition.Inertia
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.Col Classical
open Formalism.L2.Th1.H (cmL CmOK matH IsIsom taylorMv)
open Formalism.L2.Th1.GD (LocNorm InMul frameM thetaLin)
open Formalism.L2.Th1.E (IntCurve curveL Unif)
open Formalism.DworkPowerSeriesWeights (JetsIntegral)
open Formalism.MainNotions.G (HH)

noncomputable section

namespace GlobalTheory.DFrame

theorem congr_at_d : ∀ (D : D7) (p : ℕ) [Fact p.Prime], p = D.host.d → ∀ (ι : ℂ ≃+* ℂ_[p]) (cE s : D.host.E ≃+* D.host.E) (δ : D.host.E), (∀ y, cE y = D.host.conj y) → δ ^ 2 = -(p : D.host.E) → s δ = -δ → (∀ y, s (s y) = y) → (∀ (t : HH D) (y : D.host.E), TaylorLogMetric.embT D (tauPl D (true, t)) y = TaylorLogMetric.embT D (tauPl D (false, t)) (s (cE y))) → (∀ (τ : D.what₂.Tau) (y : D.host.E), s y = y → ι (TaylorLogMetric.embT D τ y) ∈ Formalism.L2.Th1.CM.MaximalUnramifiedExtension p) → (‖ι (Complex.I * ((Real.sqrt D.host.d : ℝ) : ℂ))‖ ≤ 1 ∧ ι (Complex.I * ((Real.sqrt D.host.d : ℝ) : ℂ)) ≠ 0) ∧ ∀ (t : HH D) (y : 𝓞 D.host.E), ‖GlobalTheory.DFrame.rho D ι (false, t) (D.host.conj (y : D.host.E)) - GlobalTheory.DFrame.rho D ι (true, t) (y : D.host.E)‖ ≤ ‖ι (Complex.I * ((Real.sqrt D.host.d : ℝ) : ℂ))‖ := by
  intro D p _ hpd ι cE s δ hcE hδ hsδ hss hpair hK
  set th : ℂ_[p] := ι (Complex.I * ((Real.sqrt D.host.d : ℝ) : ℂ)) with hth
  have hp0 : (0 : ℝ) < ‖(p : ℂ_[p])‖ := Formalism.L2.Th1.GD.norm_p_pos
  have hp1 : ‖(p : ℂ_[p])‖ < 1 := Formalism.L2.Th1.GD.norm_p_lt_one
  have hsq : th ^ 2 = -(p : ℂ_[p]) := by
    rw [hth, ← map_pow, mul_pow, Complex.I_sq, ← Complex.ofReal_pow,
      Real.sq_sqrt (Nat.cast_nonneg _), ← hpd]
    simp
  have hnorm2 : ‖th‖ ^ 2 = ‖(p : ℂ_[p])‖ := by
    rw [← norm_pow, hsq, norm_neg]
  have hnth : ‖th‖ = ‖(p : ℂ_[p])‖ ^ (1 / 2 : ℝ) := by
    rw [← Real.sqrt_eq_rpow, ← hnorm2, Real.sqrt_sq (norm_nonneg _)]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · by_contra h
    push_neg at h
    have : 1 < ‖th‖ ^ 2 := by nlinarith
    linarith
  · intro h
    rw [h, norm_zero] at hnorm2
    simp at hnorm2
    linarith
  · intro t y
    have hp2 : p ≠ 2 := by
      have h := hypOdd_of_hostHyp D.host.hyp
      obtain ⟨-, -, h1, h2, h3⟩ := h
      omega
    have hI := Formalism.L2.Th1.GD.InertiaRam_proof p hp2 D.host.E s δ (rho D ι (false, t)) hδ hsδ hss
      (fun y hy => hK _ y hy)
    let y' : 𝓞 D.host.E := RingOfIntegers.mapRingEquiv D.host.conj.toRingEquiv y
    have hy' : ((y' : 𝓞 D.host.E) : D.host.E) = D.host.conj (y : D.host.E) := rfl
    have h2 := hI.2.1 y'
    rw [hy'] at h2
    have htrue : rho D ι (true, t) (y : D.host.E) = rho D ι (false, t) (s (D.host.conj (y : D.host.E))) := by
      show ι (TaylorLogMetric.embT D (tauPl D (true, t)) (y : D.host.E)) = ι (TaylorLogMetric.embT D (tauPl D (false, t)) _)
      rw [hpair t, hcE]
    rw [htrue, hnth]
    exact h2

end GlobalTheory.DFrame
