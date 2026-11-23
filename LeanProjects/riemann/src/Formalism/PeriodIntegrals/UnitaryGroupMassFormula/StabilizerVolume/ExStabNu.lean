import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.ExStabSt

noncomputable section

namespace PI.VolStabS

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory PI.VolFromSW
open scoped TensorProduct ENNReal

def ThetaPos : Prop := InCtx fun F E _ _ _ _ _ σ M J a X0 _hT =>
  ∀ μ, IsHaarH F E σ M J μ → ∀ 𝓕, IsFDH F E σ M J μ 𝓕 →
    ∃ φ : (Fin a → Fin M → AF F ⊗[F] E) → ℝ, (∀ X, 0 ≤ φ X) ∧ IsAdmS F E (fun X => (φ X : ℂ)) ∧
      meanC μ 𝓕 (thetaS F E σ M J (fun X => (φ X : ℂ)) {X | gramE σ J X = gramE σ J X0}) ≠ 0

theorem nuNeZero_of (hS : SWeqOm) (hP : ThetaPos) : NuNeZero := by
  intro F E _ _ _ _ _ σ hCM M J hJ ha hc a ha1 ha2 X0 hT hdet ψ hψ νX hν h0
  obtain ⟨μ, hμ⟩ := ha.1
  obtain ⟨𝓕, h𝓕⟩ := (ha.2 μ hμ).1
  obtain ⟨φ, -, hadm, hne⟩ := hP F E σ hCM M J hJ ha hc a ha1 ha2 X0 hT hdet μ hμ 𝓕 h𝓕
  have e := hS F E σ hCM M J hJ ha hc a ha1 ha2 X0 hT hdet ψ hψ μ hμ 𝓕 h𝓕 νX hν _ hadm
  rw [e, h0, integral_zero_measure] at hne
  exact hne rfl

end PI.VolStabS
