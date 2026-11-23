import Formalism.LocalToGlobal.IndefiniteReal.SEEofApply

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory Formalism.L2.Theta Formalism.IndefR.Mult Formalism.L2.SG.RowDict
open scoped TensorProduct

namespace Formalism.IndefR.AutomorphicEvaluation

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {S : D.what₂.Tau → SPar}

def ConjLevel (t : GA D (D.sp.Y 0)) (J : Set (GA D (D.sp.Y 0))) (χ : GA D (D.sp.Y 0) → ℂ)
    (J' : Set (GA D (D.sp.Y 0))) (χ' : GA D (D.sp.Y 0) → ℂ) : Prop :=
  ∀ k, (k ∈ J ↔ t⁻¹ * k * t ∈ J') ∧ (k ∈ J → χ' (t⁻¹ * k * t) = χ k)

def EvalTieT (M : DSModel (D.sp.Y 0) S) (μ : Measure (GA D (D.sp.Y 0))) (𝓕 : Set (GA D (D.sp.Y 0)))
    (E : Submodule ℂ (MMap M)) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (G : GoodOp X)
    (ι : GA D (D.sp.Y 0) ≃* X.B.I.GA) (t : GA D (D.sp.Y 0)) (c : ℝ) : Prop :=
  ∃ v₀ : M.Vec, (∀ τ, ‖(v₀ τ : M.H τ)‖ = 1) ∧ ∃ j : E ≃ₗ[ℂ] EEC X G, ∀ T : E,
    ((j T : EEC X G) : L2X X) =ᵐ[muX X] (fun x => ev M v₀ (T : MMap M) (ι.symm x * t)) ∧
      ‖((j T : EEC X G) : L2X X)‖ ^ 2 = c * (ipM M μ 𝓕 (T : MMap M) (T : MMap M)).re

open Classical in

def sEEofTT (M : DSModel (D.sp.Y 0) S) (μ : Measure (GA D (D.sp.Y 0))) (𝓕 : Set (GA D (D.sp.Y 0)))
    (E : Submodule ℂ (MMap M)) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (G : GoodOp X)
    (ι : GA D (D.sp.Y 0) ≃* X.B.I.GA) (t : GA D (D.sp.Y 0)) (c : ℝ) :
    E →ₗ⋆[ℂ] Formalism.L2.SG.PoincareInHH.PoincareSetting.HHX X :=
  if h : EvalTieT M μ 𝓕 E X G ι t c then (conjHH X G).toLinearMap.comp h.choose_spec.2.choose.toLinearMap else 0

end Formalism.IndefR.AutomorphicEvaluation

end
