import Mathlib
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.Statements
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.SectionInjectivityHypothesesProjectiveLine
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Close

open MvPolynomial

noncomputable section

variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}

theorem chartForm_eval_agree (P : ArithVariety n) (A A' : HermLine n) (hdeg : A'.deg = A.deg)
    (hmet : ∀ z ∈ P.points ℂ, A'.metric z = A.metric z)
    (h : ∀ s : IntegralSection P A'.deg,
      (∀ z ∈ P.points ℂ, ∀ (c c' : (k : ι) → Fin (n k + 1)) (d d' : ι → ℕ)
          (e e' : MvPolynomial (Coord n) ℤ),
        IsChartForm P A'.deg s.num s.den c d e → IsChartForm P A'.deg s.num s.den c' d' e' →
        (∀ k, z k (c k) ≠ 0) → (∀ k, z k (c' k) ≠ 0) →
          ‖evalCone z e‖ / (‖evalCone z (chartMonomial c d)‖ * A'.metric z) =
            ‖evalCone z e'‖ / (‖evalCone z (chartMonomial c' d')‖ * A'.metric z)) ∧
        ∃ C : ℝ, s.SupNormLE A' C)
    (s : IntegralSection P A.deg) :
    (∀ z ∈ P.points ℂ, ∀ (c c' : (k : ι) → Fin (n k + 1)) (d d' : ι → ℕ)
        (e e' : MvPolynomial (Coord n) ℤ),
      IsChartForm P A.deg s.num s.den c d e → IsChartForm P A.deg s.num s.den c' d' e' →
      (∀ k, z k (c k) ≠ 0) → (∀ k, z k (c' k) ≠ 0) →
        ‖evalCone z e‖ / (‖evalCone z (chartMonomial c d)‖ * A.metric z) =
          ‖evalCone z e'‖ / (‖evalCone z (chartMonomial c' d')‖ * A.metric z)) ∧
      ∃ C : ℝ, s.SupNormLE A C := by
  obtain ⟨deg, metric, h1, h2, h3⟩ := A'
  dsimp only at hdeg hmet h
  subst hdeg
  obtain ⟨hind, C, hC⟩ := h s
  refine ⟨fun z hz c c' d d' e e' he he' hc hc' ↦ ?_, C, fun z hz c d e he hc ↦ ?_⟩
  · rw [← hmet z hz]
    exact hind z hz c c' d d' e e' he he' hc hc'
  · rw [← hmet z hz]
    exact hC z hz c d e he hc

theorem BoundedMonomials.equiv :
    GroundTheory.Heights₂.Heights.BoundedMonomials.Statement ↔ GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Close.BoundedMonomials.Statement := by
  constructor
  · intro hA ι _ _ n P M k e
    exact hA ι n P (powDivStd M k) e
  · intro hB ι _ _ n P A s
    have hdeg : (powDivStd (twistPow A 1 1 0) 1).deg = A.deg := by
      funext b
      simp [powDivStd, twistPow]
    have hmet : ∀ z ∈ P.points ℂ, (powDivStd (twistPow A 1 1 0) 1).metric z = A.metric z := by
      intro z hz
      have hS := ((HermLine.standard n).metric_pos z hz.1).ne'
      simp only [powDivStd, twistPow, Nat.cast_one, one_mul, mul_zero, neg_zero, Real.exp_zero,
        pow_one]
      field_simp
    exact chartForm_eval_agree P A _ hdeg hmet (hB ι n P (twistPow A 1 1 0) 1) s

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Close
