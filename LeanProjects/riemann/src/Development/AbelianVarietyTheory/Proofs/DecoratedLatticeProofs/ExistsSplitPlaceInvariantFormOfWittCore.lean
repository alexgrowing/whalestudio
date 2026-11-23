import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsQuasiFam
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ThetaAbsoluteSum
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.TransvectionAction
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.WeilDatumExistence
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.AdjointIsotropicDecomposition
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.T2SpaceHalfAdelicMatrixAddSubgroup
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.InfPartOneSubEInfSmul
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ThetaFunctionZeroOfInvariantFunctionals
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HalfAvgLinear
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IntegralTranslate
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IntegralCompAddEquivEqSmul
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SymplOExtXExtY
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

namespace GlobalTheory.SplitPlaceForm

set_option maxHeartbeats 1000000 in

theorem exists_form_of_core : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S S₀ T : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ) (μ : Measure (Mx D T.rank ρ)) (𝓕 : Set (Mx D T.rank ρ)), IsCovolOne (ratMx D T.rank ρ) μ 𝓕 → ∀ e, IsSplitIdem D e → ∀ ℓ₀ : (WO S₀ T → ℂ) →ₗ[ℂ] ℂ, (∀ u : WO S₀ T, (∀ i j, cA D e * u i j = u i j) → ∀ f, IsThetaFunO ψ S₀ T f → ℓ₀ (heisO ψ S₀ T u f) = ℓ₀ f) → (∃ f, IsThetaFunO ψ S₀ T f ∧ ℓ₀ f ≠ 0) → ∃ ℓ : (WO S T → ℂ) →ₗ[ℂ] ℂ, (∀ u : WO S T, (∀ i j, cA D e * u i j = u i j) → ∀ f, IsThetaFunO ψ S T f → ℓ (heisO ψ S T u f) = ℓ f) ∧ (∃ f, IsThetaFunO ψ S T f ∧ ℓ f ≠ 0) ∧ ∀ (h : GL (Fin T.rank) (AE D)) (a : GL (Fin ρ) (AE D)), ∃ r : ℝ, 0 < r ∧ ∀ (f f' : WO S T → ℂ) (k : ℂ), IsThetaFunO ψ S T f → IsThetaFunO ψ S T f' → (∀ x : Mx D T.rank ρ, (∀ i j, cA D e * x i j = x i j) → ℓ₀ (d.mixS T ψ μ 𝓕 (f') x) = k * ℓ₀ (d.mixS T ψ μ 𝓕 (f) (h.1 ⬝ x ⬝ a.1))) → ℓ f' = r * k * ℓ f := by
  intro D ψ hψ S S₀ T ρ d μ 𝓕 hμ e he ℓ₀ h0 hne
  letI : MeasurableSpace (GlobalTheory.HalfAverage.halfMx (cA D e) T.rank ρ) := GlobalTheory.HalfAverage.measHalf _ _ _
  haveI : BorelSpace (GlobalTheory.HalfAverage.halfMx (cA D e) T.rank ρ) := GlobalTheory.HalfAverage.borelHalf _ _ _
  have hH : ∀ x, x ∈ GlobalTheory.HalfAverage.halfMx (cA D e) T.rank ρ ↔ ∀ i j, cA D e * x i j = x i j := fun x => Iff.rfl
  obtain ⟨ℓ, hℓ⟩ := GlobalTheory.HalfLinForm.halfAvg_linear D ψ hψ S S₀ T ρ d μ 𝓕 hμ e he ℓ₀ _ hH (GlobalTheory.HalfAverage.haarHalf (cA D e) T.rank ρ)
  refine ⟨ℓ, fun u hu f hf => ?_, ?_, fun h a => ?_⟩
  · rw [hℓ _ (GlobalTheory.ThetaClosed.isThetaFunO_heisO_all hψ hf u), hℓ f hf]
    exact GlobalTheory.HalfInvariance.half_avg_heis_inv D ψ hψ S S₀ T ρ d μ 𝓕 hμ e he ℓ₀ h0 _ hH _ u hu f hf
  · obtain ⟨f, hf, hn⟩ := GlobalTheory.HalfNonvan.avg_mixS_ne_zero D ψ hψ S S₀ T ρ d μ 𝓕 hμ e he ℓ₀ hne _ hH (GlobalTheory.HalfAverage.haarHalf (cA D e) T.rank ρ)
    exact ⟨f, hf, by rw [hℓ f hf]; exact hn⟩
  · obtain ⟨r, hr, hm⟩ := GlobalTheory.HalfTwist.integral_twist_fix_eq_smul D T.rank ρ (cA D e) _ hH (GlobalTheory.HalfAverage.haarHalf (cA D e) T.rank ρ) h a
    refine ⟨r, hr, fun f f' k hf hf' hk => ?_⟩
    have e1 := hm fun x => ℓ₀ (d.mixS T ψ μ 𝓕 f x)
    rw [hℓ f hf, hℓ f' hf', mul_comm (r : ℂ) k, mul_assoc, ← e1, ← integral_const_mul]
    exact integral_congr_ae (Filter.Eventually.of_forall fun x => hk x.1 x.2)

end GlobalTheory.SplitPlaceForm
