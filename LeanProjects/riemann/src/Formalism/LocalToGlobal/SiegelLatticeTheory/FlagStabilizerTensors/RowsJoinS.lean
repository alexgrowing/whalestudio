import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.AutomorphicEvaluation
import Formalism.LocalToGlobal.IndefiniteReal.RationalEmbedding
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs

noncomputable section

set_option linter.dupNamespace false

open Formalism.BasicNotions Formalism.BasicNotions.TH MeasureTheory Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation
open Formalism.L2.SG.RowDict Formalism.L2.SG.PoincareInHH.PoincareSetting
open scoped InnerProductSpace

namespace Formalism.L2.SG.RowsJoinS

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {S : D.what₂.Tau → SPar}

def RowsJoinS (M : DSModel (D.sp.Y 0) S) (μ : Measure (GA D (D.sp.Y 0))) (𝓕 : Set (GA D (D.sp.Y 0)))
    (E : Submodule ℂ (MMap M)) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (G : GoodOp X)
    (ιG : GA D (D.sp.Y 0) ≃* X.B.I.GA) (c : ℝ) (ιH : D.s.HH ≃ₗᵢ[ℂ] HHX X) : Prop :=
  ∃ v₀ : M.Vec, (∀ τ, ‖(v₀ τ : M.H τ)‖ = 1) ∧ ∃ (j : E ≃ₗ[ℂ] EEC X G) (k : D.what₂.EE ≃ₗ[ℂ] E),
    (∀ T : E, ((j T : EEC X G) : L2X X) =ᵐ[muX X] (fun x => ev M v₀ (T : MMap M) (ιG.symm x)) ∧
      ‖((j T : EEC X G) : L2X X)‖ ^ 2 = c * (ipM M μ 𝓕 (T : MMap M) (T : MMap M)).re) ∧
    ∀ F : D.what₂.EE, ιH (D.sEE F) = conjHH X G (j (k F))

variable {M : DSModel (D.sp.Y 0) S} {μ : Measure (GA D (D.sp.Y 0))} {𝓕 : Set (GA D (D.sp.Y 0))}
  {E : Submodule ℂ (MMap M)} {X : Formalism.L2.SG.HidaSetting.HidaSetting D} {G : GoodOp X}
  {ιG : GA D (D.sp.Y 0) ≃* X.B.I.GA} {c : ℝ} {ιH : D.s.HH ≃ₗᵢ[ℂ] HHX X}

end Formalism.L2.SG.RowsJoinS
