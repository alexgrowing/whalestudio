import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsArith
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.GeometryOfNumbersTheory Filter Asymptotics

noncomputable section

def FrameChange.Statement : Prop :=
  ∀ (D : ℕ) (Ω : Type) [Field Ω] [CharZero Ω] (κ : Type) [Fintype κ] (d : HSMDatum D Ω κ),
    ∃ (B : Matrix (Ix κ) (Ix κ) ℚ) (d' : HSMDatum D Ω κ) (e : Fin (D + 1) → Ix κ),
      IsInvMat B ∧ d'.x = matAct B d.x ∧ (∀ z, d'.m.ρ (matActC B z) = d.m.ρ z) ∧ IsProjFrame d'.x e ∧
      (fun n => resChi d' n - resChi d n - latLogIndex d.x d'.x n) =o[atTop] pw D

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
