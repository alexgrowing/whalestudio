import Formalism.LocalToGlobal.IndefiniteReal.AutomorphicEvaluation

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory Formalism.L2.Theta Formalism.IndefR.Mult Formalism.L2.SG.RowDict
open scoped TensorProduct

namespace Formalism.IndefR.AutomorphicEvaluation

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {S : D.what₂.Tau → SPar}

def vOf {M : DSModel (D.sp.Y 0) S} {μ : Measure (GA D (D.sp.Y 0))} {𝓕 : Set (GA D (D.sp.Y 0))}
    {E : Submodule ℂ (MMap M)} {X : Formalism.L2.SG.HidaSetting.HidaSetting D} {G : GoodOp X}
    {ι : GA D (D.sp.Y 0) ≃* X.B.I.GA} {c : ℝ} (h : EvalTie M μ 𝓕 E X G ι c) : M.Vec := h.choose

def jOf {M : DSModel (D.sp.Y 0) S} {μ : Measure (GA D (D.sp.Y 0))} {𝓕 : Set (GA D (D.sp.Y 0))}
    {E : Submodule ℂ (MMap M)} {X : Formalism.L2.SG.HidaSetting.HidaSetting D} {G : GoodOp X}
    {ι : GA D (D.sp.Y 0) ≃* X.B.I.GA} {c : ℝ} (h : EvalTie M μ 𝓕 E X G ι c) : E ≃ₗ[ℂ] EEC X G :=
  h.choose_spec.2.choose

theorem jOf_spec {M : DSModel (D.sp.Y 0) S} {μ : Measure (GA D (D.sp.Y 0))} {𝓕 : Set (GA D (D.sp.Y 0))}
    {E : Submodule ℂ (MMap M)} {X : Formalism.L2.SG.HidaSetting.HidaSetting D} {G : GoodOp X}
    {ι : GA D (D.sp.Y 0) ≃* X.B.I.GA} {c : ℝ} (h : EvalTie M μ 𝓕 E X G ι c) (T : E) :
    (((jOf h T : EEC X G) : L2X X) =ᵐ[muX X] fun x => ev M (vOf h) (T : MMap M) (ι.symm x)) ∧
      ‖((jOf h T : EEC X G) : L2X X)‖ ^ 2 = c * (ipM M μ 𝓕 (T : MMap M) (T : MMap M)).re :=
  h.choose_spec.2.choose_spec T

def sEEof {M : DSModel (D.sp.Y 0) S} {μ : Measure (GA D (D.sp.Y 0))} {𝓕 : Set (GA D (D.sp.Y 0))}
    {E : Submodule ℂ (MMap M)} {X : Formalism.L2.SG.HidaSetting.HidaSetting D} {G : GoodOp X}
    {ι : GA D (D.sp.Y 0) ≃* X.B.I.GA} {c : ℝ} (h : EvalTie M μ 𝓕 E X G ι c) :
    E →ₗ⋆[ℂ] Formalism.L2.SG.PoincareInHH.PoincareSetting.HHX X :=
  (conjHH X G).toLinearMap.comp (jOf h).toLinearMap

end Formalism.IndefR.AutomorphicEvaluation

end
