import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsConeSheetCover
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterFib
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Geo (MRing PBlk IsArithVar IsGoodProj segre)

def conePullback {n e : ℕ} (Ψ : (((k : Unit) → PBlk n k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ))
    (c : MvPolynomial (Fin (e + 1)) ℂ) : MvPolynomial (Fin n) ℂ :=
  aeval (fun j => rename (fun p : Σ k : Unit, PBlk n k => p.2) (ReciprocityTheory.ChartRestriction.G.Geo.psiPoly Ψ j)) c

def ConeHypersurfaceDim.Statement : Prop :=
  ∀ (n e : ℕ) (P : Ideal (MRing (PBlk n)))
    (Ψ : (((k : Unit) → PBlk n k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)) (c : MvPolynomial (Fin (e + 1)) ℂ),
    IsArithVar P (e + 1) → IsGoodProj P Ψ → c ≠ 0 →
      ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ (complexFibreIdeal P ⊔ Ideal.span {conePullback Ψ c})) ≤
        ((e : ℕ) : WithBot ℕ∞)

end GroundTheory.Heights₂.Heights
