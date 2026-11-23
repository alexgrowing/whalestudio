import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeilStabilizerVolume.VolStabFromSWW

noncomputable section

namespace PI.VolStabW

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory PI.VolFromSW
open scoped TensorProduct ENNReal

def ThetaFin : Prop := InCtx fun F E _ _ _ _ _ σ M J a X0 _hT =>
  ∀ μ, IsHaarH F E σ M J μ → ∀ 𝓕, IsFDH F E σ M J μ 𝓕 →
    ∀ φ : (Fin a → Fin M → AF F ⊗[F] E) → ℝ, (∀ X, 0 ≤ φ X) → IsAdm F E (fun X => (φ X : ℂ)) →
      ∫⁻ h in 𝓕, ∑' X : {X : Fin a → Fin M → E | gramE σ J X = gramE σ J X0},
        ENNReal.ofReal (φ (h⁻¹ • ratTup (AF F) (X : Fin a → Fin M → E))) ∂μ < ⊤

def LamEx : Prop := InCtx fun F E _ _ _ _ _ σ M J a X0 _hT =>
  ∀ μ, IsHaarH F E σ M J μ → ∃ (lam : Measure (Fin a → Fin M → AF F ⊗[F] E))
    (μ'' : Measure (stabT (AF F) σ J X0)), μ''.IsHaarMeasure ∧ IsCompatT F E σ M J X0 μ μ'' lam ∧
      ∀ K : Set (Fin a → Fin M → AF F ⊗[F] E), IsCompact K → lam K < ⊤

def FinVolStab : Prop := InCtx fun F E _ _ _ _ _ σ M J _a X0 _hT =>
  ∀ μ'' : Measure (stabT (AF F) σ J X0), μ''.IsHaarMeasure →
    ∀ 𝓕'' : Set (stabT (AF F) σ J X0),
      IsFundamentalDomain (ratIn F E σ M J (stabT (AF F) σ J X0)) 𝓕'' μ'' → μ'' 𝓕'' < ⊤

def InvStab : Prop := InCtx fun F E _ _ _ _ _ σ _M J _a X0 _hT =>
  ∀ μ'' : Measure (stabT (AF F) σ J X0), μ''.IsHaarMeasure → μ''.IsInvInvariant

def AdmCpt : Prop := InCtx fun F E _ _ _ _ _ _σ M _J a _X0 _hT =>
  ∀ φ : (Fin a → Fin M → AF F ⊗[F] E) → ℝ, (∀ X, 0 ≤ φ X) → IsAdm F E (fun X => (φ X : ℂ)) →
    ∃ K : Set (Fin a → Fin M → AF F ⊗[F] E), IsCompact K ∧ ∃ C : ℝ, ∀ X, φ X ≤ C ∧ (X ∉ K → φ X = 0)

end PI.VolStabW
