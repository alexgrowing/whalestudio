import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsTypeIsRealConst
open Set Matrix Filter Topology
open GlobalTheory.HermFrame GlobalTheory.CxForm
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory.GoodMetric (coordVec chernPoly curvPoly)
open scoped ContDiff ComplexOrder

namespace GlobalTheory.CxForm

theorem chernAt_changeFrame : ∀ {n : ℕ} {r : Type} [Fintype r] [DecidableEq r] (H K A : V n → Matrix r r ℂ) (v : V n), MContDiffAt 2 K v → IsUnit (K v).det → (∀ i j, AnalyticAt ℂ (fun w => A w i j) v) → IsUnit (A v).det → (H =ᶠ[𝓝 v] fun w => chg (A w) (K w)) → ∀ j, chernAt H v j = chernAt K v j := by
  intro n r _ _ H K A v hK hKu hg hAu hH j
  have hconj : ∀ (M P Q : Matrix r r (MvPolynomial (Fin n × Fin n) ℂ)), Q * P = 1 →
      (Q * M * P).charpolyRev = M.charpolyRev := by
    intro M P Q hQP
    have hQP' : Q.map Polynomial.C * P.map Polynomial.C = 1 := by
      rw [← Matrix.map_mul, hQP, Matrix.map_one _ (map_zero _) (map_one _)]
    have e : (1 : Matrix r r (Polynomial (MvPolynomial (Fin n × Fin n) ℂ))) -
        (Polynomial.X : Polynomial (MvPolynomial (Fin n × Fin n) ℂ)) • (Q * M * P).map Polynomial.C =
        Q.map Polynomial.C * (1 - (Polynomial.X : Polynomial (MvPolynomial (Fin n × Fin n) ℂ)) •
          M.map Polynomial.C) * P.map Polynomial.C := by
      rw [Matrix.map_mul, Matrix.map_mul, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hQP',
        Matrix.mul_smul, Matrix.smul_mul]
    rw [Matrix.charpolyRev, Matrix.charpolyRev, e, Matrix.det_mul, Matrix.det_mul, mul_right_comm,
      ← Matrix.det_mul, hQP', Matrix.det_one, one_mul]
  have hsum : ∀ G : V n → Matrix r r ℂ, curvPoly G v =
      ∑ a, ∑ b, (MvPolynomial.X (a, b) : MvPolynomial (Fin n × Fin n) ℂ) •
        (curv G v (coordVec a) (coordVec b)).map MvPolynomial.C := by
    intro G
    ext i j
    simp [curvPoly, Matrix.sum_apply, mul_comm]
  have hA : MContDiffAt 2 A v := fun a b => (hg a b).contDiffAt.restrict_scalars ℝ
  have hA0 : ∀ᶠ x in 𝓝 v, ∀ η, mdbar A x η = 0 := by
    have hev : ∀ᶠ x in 𝓝 v, ∀ a b, AnalyticAt ℂ (fun w => A w a b) x :=
      eventually_all.2 fun a => eventually_all.2 fun b => (hg a b).eventually_analyticAt
    filter_upwards [hev] with x hx η
    ext a b
    rw [mdbar_apply, GlobalTheory.dbar_eq_zero (hx a b).differentiableAt]
    rfl
  have hGe : H =ᶠ[𝓝 v] fun u => (A u)ᵀ * K u * (A u)ᴴᵀ := hH
  have hcurv : ∀ ξ η, curv H v ξ η = (A v)⁻¹ * curv K v ξ η * A v :=
    fun ξ η => by rw [curv_congr hGe, curv_changeFrame hK hKu hA hAu hA0]
  have key : curvPoly H v = ((A v)⁻¹).map MvPolynomial.C * curvPoly K v * (A v).map MvPolynomial.C := by
    rw [hsum, hsum]
    simp only [Finset.mul_sum, Finset.sum_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.map_mul, hcurv]
  have key2 : chernPoly H v j = chernPoly K v j := by
    rw [chernPoly, chernPoly, key, show ∀ (Q M P : Matrix r r (MvPolynomial (Fin n × Fin n) ℂ)),
      -(Q * M * P) = Q * (-M) * P from fun Q M P => by rw [Matrix.mul_neg, Matrix.neg_mul], hconj]
    rw [← Matrix.map_mul, Matrix.nonsing_inv_mul _ hAu, Matrix.map_one _ (map_zero _) (map_one _)]
  rw [chernAt, chernAt, key2]

end GlobalTheory.CxForm
