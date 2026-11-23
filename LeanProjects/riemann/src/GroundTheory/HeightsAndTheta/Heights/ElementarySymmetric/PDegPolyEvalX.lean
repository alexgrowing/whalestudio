import Mathlib
import GroundTheory.HeightsAndTheta.Heights.MultinomialWeights.Statements
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.TheoremB

open MvPolynomial Finset

theorem polarPoly_eval {σ R : Type*} [CommRing R] [Fintype σ]
    (Φ : MvPolynomial σ R →ₗ[R] R) (n : ℕ) (u : σ → R) :
    eval u (polarPoly Φ n) = Φ ((-∑ v : σ, C (u v) * X v) ^ n) := by
  set P : MvPolynomial σ (MvPolynomial σ R) := (-outerDot σ R) ^ n with hP
  let ψ : MvPolynomial σ (MvPolynomial σ R) →+* MvPolynomial σ R :=
    eval₂Hom (RingHom.id _) (fun v => C (u v))
  have hψ : ψ P = (-∑ v : σ, C (u v) * X v) ^ n := by
    simp [P, ψ, outerDot, map_pow, map_neg, map_sum]
  have hψ' : ψ P = ∑ m ∈ P.support, C (∏ i, u i ^ m i) * coeff m P := by
    change eval₂ (RingHom.id _) (fun v => C (u v)) P = _
    rw [eval₂_eq']
    refine sum_congr rfl fun m _ => ?_
    simp [map_prod, map_pow, mul_comm]
  rw [← hψ, hψ', map_sum]
  unfold polarPoly
  rw [map_sum]
  refine sum_congr rfl fun m _ => ?_
  rw [eval_monomial, Finsupp.prod_fintype _ _ (fun i => pow_zero _), C_mul', map_smul,
    smul_eq_mul, mul_comm]

theorem DegPolyEval.proof : DegPolyEval.Statement := by
  intro d u
  exact polarPoly_eval (intFl d) d.D u

end GroundTheory.Heights₂.Heights.TheoremB
