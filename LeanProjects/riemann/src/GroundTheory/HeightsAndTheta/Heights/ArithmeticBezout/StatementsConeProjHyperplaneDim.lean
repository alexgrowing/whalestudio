import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsConeProjHyperplaneNull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterFib
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Geo (MRing PBlk IsArithVar IsGoodProj segre)

def coneFirstForm {n e : ℕ} (Ψ : (((k : Unit) → PBlk n k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)) :
    MvPolynomial (Fin n) ℂ :=
  rename (fun p : Σ k : Unit, PBlk n k => p.2) (ReciprocityTheory.ChartRestriction.G.Geo.psiPoly Ψ 0)

theorem eval_coneFirstForm {n e : ℕ} (Ψ : (((k : Unit) → PBlk n k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ))
    (z : Fin n → ℂ) : eval z (coneFirstForm Ψ) = Ψ (segre fun p : Σ k, PBlk n k => z p.2) 0 := by
  rw [coneFirstForm, eval_rename]
  exact ReciprocityTheory.ChartRestriction.G.Geo.eval_psiPoly Ψ 0 _

def ConeProjHyperplaneDim.Statement : Prop :=
  ∀ (n e : ℕ) (P : Ideal (MRing (PBlk n)))
    (Ψ : (((k : Unit) → PBlk n k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)),
    IsArithVar P (e + 1) → IsGoodProj P Ψ →
      ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ (complexFibreIdeal P ⊔ Ideal.span {coneFirstForm Ψ})) ≤
        ((e : ℕ) : WithBot ℕ∞)

end GroundTheory.Heights₂.Heights
