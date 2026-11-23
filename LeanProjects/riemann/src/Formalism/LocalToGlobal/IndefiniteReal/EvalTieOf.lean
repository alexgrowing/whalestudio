import Formalism.LocalToGlobal.IndefiniteReal.SEEofApply

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory Formalism.L2.Theta Formalism.IndefR.Mult Formalism.L2.SG.RowDict
open scoped TensorProduct

namespace Formalism.IndefR.AutomorphicEvaluation

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {S : D.what₂.Tau → SPar}

section Halves

variable (M : DSModel (D.sp.Y 0) S) (μ : Measure (GA D (D.sp.Y 0))) (𝓕 : Set (GA D (D.sp.Y 0)))
  (E : Submodule ℂ (MMap M)) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (G : GoodOp X) (ι : GA D (D.sp.Y 0) ≃* X.B.I.GA)
  (c : ℝ) (v₀ : M.Vec)

def EvalInto : Prop :=
  ∀ T ∈ E, ∃ F : EEC X G, ((F : L2X X) =ᵐ[muX X] fun x => ev M v₀ T (ι.symm x)) ∧
    ‖(F : L2X X)‖ ^ 2 = c * (ipM M μ 𝓕 T T).re

def EvalOnto : Prop :=
  ∀ F : EEC X G, ∃ T ∈ E, (F : L2X X) =ᵐ[muX X] fun x => ev M v₀ T (ι.symm x)

def EvalInj : Prop :=
  ∀ T ∈ E, ((fun x => ev M v₀ T (ι.symm x)) =ᵐ[muX X] 0) → T = 0

end Halves

open Classical in

def sEEofT (M : DSModel (D.sp.Y 0) S) (μ : Measure (GA D (D.sp.Y 0))) (𝓕 : Set (GA D (D.sp.Y 0)))
    (E : Submodule ℂ (MMap M)) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (G : GoodOp X) (ι : GA D (D.sp.Y 0) ≃* X.B.I.GA)
    (c : ℝ) : E →ₗ⋆[ℂ] Formalism.L2.SG.PoincareInHH.PoincareSetting.HHX X :=
  if h : EvalTie M μ 𝓕 E X G ι c then sEEof h else 0

end Formalism.IndefR.AutomorphicEvaluation

end
