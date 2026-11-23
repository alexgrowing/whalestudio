import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.KappaSt
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MeasureTheory MvPolynomial ReciprocityTheory.ChartRestriction.G.AI

noncomputable section

def momentPoly {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (w : Ω → ℝ)
    (Q : MvPolynomial (Fin 3) (Ω → ℝ)) : MvPolynomial (Fin 3) ℝ :=
  ∑ m ∈ Q.support, monomial m (∫ p, w p * coeff m Q p ∂μ)

def dotPoly {Ω : Type*} (n : Ω → S2) : MvPolynomial (Fin 3) (Ω → ℝ) :=
  ∑ i, X i * C (fun p => (n p : E3) i)

def fibreMomentPoly (k : ℕ) : MvPolynomial (Fin 3) ℝ :=
  momentPoly (sphereMeasure.prod sphereMeasure)
    (fun p : S2 × S2 => (1 / 2 : ℝ) * Real.log ((1 - inner ℝ (p.1 : E3) (p.2 : E3)) / 2))
    (aeval ![dotPoly Prod.fst, dotPoly Prod.snd] (dgPoly k))

def pushMomentPoly (k : ℕ) : MvPolynomial (Fin 3) ℝ :=
  (-(2 * (k : ℝ) - 1)) • momentPoly sphereMeasure (fun _ => 1) (dotPoly id ^ (2 * k - 2))

def FibreLocal.Statement : Prop :=
  (∀ (k : ℕ) (a : E3),
    ∫ n₁ : S2, ∫ n₂ : S2, (1 / 2 : ℝ) * Real.log ((1 - inner ℝ (n₁ : E3) (n₂ : E3)) / 2) *
        eval ![inner ℝ a (n₁ : E3), inner ℝ a (n₂ : E3)] (dgPoly k) ∂sphereMeasure ∂sphereMeasure =
      -kappa k * inner ℝ a a ^ (k - 1)) ∧
  (∀ (k : ℕ) (B : Type) [CommRing B] [Algebra ℝ B] (a : Fin 3 → B),
    aeval a (fibreMomentPoly k) = algebraMap ℝ B (-kappa k) * (∑ i, a i ^ 2) ^ (k - 1)) ∧
  (∀ k : ℕ, 1 ≤ k → ∀ a : E3,
    -(2 * (k : ℝ) - 1) * ∫ n : S2, inner ℝ a (n : E3) ^ (2 * k - 2) ∂sphereMeasure =
      -(inner ℝ a a ^ (k - 1))) ∧
  (∀ k : ℕ, 1 ≤ k → ∀ (B : Type) [CommRing B] [Algebra ℝ B] (a : Fin 3 → B),
    aeval a (pushMomentPoly k) = -(∑ i, a i ^ 2) ^ (k - 1)) ∧
  ∀ k : ℕ, kappa k = (1 / 2) * ∑ j ∈ Finset.range k, (1 : ℝ) / (2 * j + 1)

end

end GroundTheory.Heights₂.Heights.Inter
