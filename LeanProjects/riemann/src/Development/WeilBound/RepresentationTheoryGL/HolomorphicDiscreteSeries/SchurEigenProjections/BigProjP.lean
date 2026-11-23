import Development.WeilBound.RepresentationTheoryGL.HolomorphicDiscreteSeries.WeightOccurrence.OccSome
import Development.WeilBound.RepresentationTheoryGL.HolomorphicDiscreteSeries.SchurEigenProjections.EigA
import Development.AutomorphicSpectrum.Definitions.AdelicLattices.IsGenLevel
import Development.AbelianVarietyTheory.Definitions.Foundations.UnitarySixTwoHarishChandraParameter
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousWordTranslate
import Development.WeilBound.CoreStatements.OrbitDecayEstimates.CurveDerivativeDecay.LipschitzEstimate
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.HeBranching
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsNormEmbId

noncomputable section

open MeasureTheory Matrix Finset Formalism.REAL Formalism.MainNotions.S PI.DSInfCharCap GlobalTheory.CompanionTheory.UnitaryFramesMetricPeriods
open scoped InnerProductSpace ComplexConjugate

namespace PositivityTheory.RgHe.A

def SchurEigenProjectionExists : Prop := GlobalTheory.CompanionTheory.PairingAnalysis.ForPairs fun {n} ε lam ε' mu _ e H H' _ _ _ _ _ _ π σ ν =>
  GlobalTheory.CompanionTheory.PairingAnalysis.HeWord ε lam ε' mu → ∀ κ : ℝ, PositivityTheory.RgHe.SchurK ε' σ ν κ → ∀ w ∈ lowKSub ε' mu σ, ‖w‖ = 1 →
    Integrable (fun h : UJ ε' => ⟪w, σ (GlobalTheory.CompanionTheory.PairingAnalysis.um h) w⟫_ℂ) ν ∧
    ∃ (i : H' →L[ℂ] H) (η : H), (∀ x, ‖i x‖ = ‖x‖) ∧
      (∀ h : UJ ε', ∀ x, i (σ (GlobalTheory.CompanionTheory.PairingAnalysis.um h) x) = π (GlobalTheory.CompanionTheory.PairingAnalysis.emb e (GlobalTheory.CompanionTheory.PairingAnalysis.um h)) (i x)) ∧
      η ∈ PI.PhMeasCore.smoothVecs (Jm ε) π ∧ ⟪η, i w⟫_ℂ ≠ 0 ∧
      ∀ a : H, ∫ h : UJ ε', conj ⟪w, σ (GlobalTheory.CompanionTheory.PairingAnalysis.um h) w⟫_ℂ * ⟪η, π (GlobalTheory.CompanionTheory.PairingAnalysis.emb e (GlobalTheory.CompanionTheory.PairingAnalysis.um h)) a⟫_ℂ ∂ν =
        κ * (⟪η, i w⟫_ℂ * ⟪i w, a⟫_ℂ)

def MomentP : Prop := GlobalTheory.CompanionTheory.PairingAnalysis.ForPairs fun {n} ε lam ε' _ B e H H' _ _ _ _ _ _ π σ ν =>
  ∀ (P : H →L[ℂ] H') (w : H') (κ : ℝ), GlobalTheory.CompanionTheory.PairingAnalysis.Intertw ε' e π σ P → ‖w‖ = 1 →
    ‖ContinuousLinearMap.adjoint P w‖ = 1 → 0 < κ →
    Integrable (fun h : UJ ε' => ⟪w, σ (GlobalTheory.CompanionTheory.PairingAnalysis.um h) w⟫_ℂ) ν →
    (∀ x : UJ ε', ∫ h : UJ ε', conj ⟪w, σ (GlobalTheory.CompanionTheory.PairingAnalysis.um h) w⟫_ℂ * conj ⟪w, σ (GlobalTheory.CompanionTheory.PairingAnalysis.um (h⁻¹ * x)) w⟫_ℂ ∂ν =
      κ * conj ⟪w, σ (GlobalTheory.CompanionTheory.PairingAnalysis.um x) w⟫_ℂ) →
    (∃ η ∈ PI.PhMeasCore.smoothVecs (Jm ε) π, ⟪η, ContinuousLinearMap.adjoint P w⟫_ℂ ≠ 0 ∧
      ∀ a : H, ∫ h : UJ ε', conj ⟪w, σ (GlobalTheory.CompanionTheory.PairingAnalysis.um h) w⟫_ℂ * ⟪η, π (GlobalTheory.CompanionTheory.PairingAnalysis.emb e (GlobalTheory.CompanionTheory.PairingAnalysis.um h)) a⟫_ℂ ∂ν =
        κ * (⟪η, ContinuousLinearMap.adjoint P w⟫_ℂ * ⟪ContinuousLinearMap.adjoint P w, a⟫_ℂ)) →
    ∀ v ∈ lowKSub ε lam π, ‖v‖ = 1 →
      ∫⁻ g : UJ ε, ENNReal.ofReal (GlobalTheory.CompanionTheory.PairingAnalysis.colSq (GlobalTheory.CompanionTheory.PairingAnalysis.um g⁻¹) (GlobalTheory.CompanionTheory.PairingAnalysis.zi e) *
          ‖⟪ContinuousLinearMap.adjoint P w, π (GlobalTheory.CompanionTheory.PairingAnalysis.um g) v⟫_ℂ‖ ^ 2) ∂(muG ε) ≤
        ENNReal.ofReal ((8 * ((n : ℝ) + 1) * B) ^ (8 * (n + 1))) *
          ∫⁻ g : UJ ε, ENNReal.ofReal (‖⟪ContinuousLinearMap.adjoint P w, π (GlobalTheory.CompanionTheory.PairingAnalysis.um g) v⟫_ℂ‖ ^ 2) ∂(muG ε)

def BigProjP : Prop := GlobalTheory.CompanionTheory.PairingAnalysis.ForPairs fun {n} ε lam ε' mu B e H H' _ _ _ _ _ _ π σ ν =>
  ∀ κ : ℝ, PositivityTheory.RgHe.SchurK ε' σ ν κ → ∀ w ∈ lowKSub ε' mu σ, ‖w‖ = 1 →
    Integrable (fun h : UJ ε' => ⟪w, σ (GlobalTheory.CompanionTheory.PairingAnalysis.um h) w⟫_ℂ) ν → ∀ (i : H' →L[ℂ] H) (η : H), (∀ x, ‖i x‖ = ‖x‖) →
    (∀ h : UJ ε', ∀ x, i (σ (GlobalTheory.CompanionTheory.PairingAnalysis.um h) x) = π (GlobalTheory.CompanionTheory.PairingAnalysis.emb e (GlobalTheory.CompanionTheory.PairingAnalysis.um h)) (i x)) →
    η ∈ PI.PhMeasCore.smoothVecs (Jm ε) π → ⟪η, i w⟫_ℂ ≠ 0 →
    (∀ a : H, ∫ h : UJ ε', conj ⟪w, σ (GlobalTheory.CompanionTheory.PairingAnalysis.um h) w⟫_ℂ * ⟪η, π (GlobalTheory.CompanionTheory.PairingAnalysis.emb e (GlobalTheory.CompanionTheory.PairingAnalysis.um h)) a⟫_ℂ ∂ν =
      κ * (⟪η, i w⟫_ℂ * ⟪i w, a⟫_ℂ)) →
    ∀ v ∈ lowKSub ε lam π, ‖v‖ = 1 → ∃ g₀ : UJ ε, hs (GlobalTheory.CompanionTheory.PairingAnalysis.um g₀) ≤ (8 * ((n : ℝ) + 1) * B) ^ (20 * (n + 1)) ∧
      Real.exp (-(100 * ((n : ℝ) + 1) ^ 3 * Real.log (8 * (n + 1) * B))) ≤
        ‖ContinuousLinearMap.adjoint i (π (GlobalTheory.CompanionTheory.PairingAnalysis.um g₀) v)‖

end PositivityTheory.RgHe.A
