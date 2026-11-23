import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsMetricFrOfIsMetricOn
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ChernDegreeComplex
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MdbarZeroOfHolo

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc
open scoped Matrix ContDiff ComplexOrder

namespace GlobalTheory.ChernCalc.FrameInv

section Algebra

variable {r R : Type} [Fintype r] [DecidableEq r] [CommRing R] {P Q : Matrix r r R}

theorem conj_pow (h : Q * P = 1) (A : Matrix r r R) (k : ℕ) : (P * A * Q) ^ k = P * A ^ k * Q := by
  induction k with
  | zero => rw [pow_zero, pow_zero, mul_one, mul_eq_one_comm.1 h]
  | succ k ih =>
    rw [pow_succ, ih, pow_succ]
    simp only [mul_assoc]
    rw [← mul_assoc Q P, h, one_mul]

theorem trace_conj' (h : Q * P = 1) (A : Matrix r r R) : (P * A * Q).trace = A.trace := by
  rw [Matrix.trace_mul_cycle, h, one_mul]

theorem charpolyRev_conj (h : Q * P = 1) (A : Matrix r r R) : (P * A * Q).charpolyRev = A.charpolyRev := by
  have h' : Q.map Polynomial.C * P.map Polynomial.C = 1 := by
    rw [← Matrix.map_mul, h, Matrix.map_one _ (map_zero _) (map_one _)]
  have e : (1 - (Polynomial.X : Polynomial R) • (P * A * Q).map Polynomial.C : Matrix r r (Polynomial R)) =
      P.map Polynomial.C * (1 - (Polynomial.X : Polynomial R) • A.map Polynomial.C) * Q.map Polynomial.C := by
    rw [Matrix.map_mul, Matrix.map_mul, mul_sub, sub_mul, mul_one, mul_eq_one_comm.1 h', Matrix.mul_smul,
      Matrix.smul_mul]
  rw [Matrix.charpolyRev, Matrix.charpolyRev, e, Matrix.det_mul, Matrix.det_mul, mul_right_comm, ← Matrix.det_mul,
    mul_eq_one_comm.1 h', Matrix.det_one, one_mul]

theorem conj_mul_three (h : Q * P = 1) (A B C : Matrix r r R) :
    (P * A * Q) * (P * B * Q) * (P * C * Q) = P * (A * B * C) * Q := by
  simp only [mul_assoc]
  rw [← mul_assoc Q P, h, one_mul, ← mul_assoc Q P, h, one_mul]

end Algebra

variable {n : ℕ} {r : Type} [Fintype r] [DecidableEq r]

theorem curvPoly_eq_sum (G : V n → Matrix r r ℂ) (v : V n) : curvPoly G v =
    ∑ a, ∑ b, (X (a, b) : MvPolynomial (Fin n × Fin n) ℂ) • (curv G v (coordVec a) (coordVec b)).map C := by
  ext1 i j
  simp [curvPoly, Matrix.sum_apply, mul_comm]

theorem curvPoly_conj {G G₂ : V n → Matrix r r ℂ} {v : V n} {P Q : Matrix r r ℂ}
    (h : ∀ ξ η, curv G₂ v ξ η = P * curv G v ξ η * Q) : curvPoly G₂ v = P.map C * curvPoly G v * Q.map C := by
  simp only [curvPoly_eq_sum, h, Matrix.map_mul, Finset.mul_sum, Finset.sum_mul, Matrix.mul_smul, Matrix.smul_mul]

theorem curvEv_conj {G G₂ : V n → Matrix r r ℂ} {v : V n} {P Q : Matrix r r ℂ}
    (h : ∀ ξ η, curv G₂ v ξ η = P * curv G v ξ η * Q) :
    curvEv G₂ v = P.map (algebraMap ℂ (Ev n)) * curvEv G v * Q.map (algebraMap ℂ (Ev n)) := by
  have e (M : Matrix r r ℂ) : (M.map C).map (aeval (R := ℂ) (sym (n := n))) = M.map (algebraMap ℂ (Ev n)) := by
    ext1 i j
    simp only [Matrix.map_apply, aeval_C]
  rw [curvEv, curvPoly_conj h, Matrix.map_mul, Matrix.map_mul, e, e, curvEv]

theorem pow_chern_trans_frame : ∀ (n : ℕ) (r : Type) [Fintype r] [DecidableEq r] (G G' G₂ G₂' T K K' : V n → Matrix r r ℂ) (v : V n), MContDiffAt ∞ G v → IsUnit (G v).det → MContDiffAt ∞ G' v → IsUnit (G' v).det → (∀ a b, ∀ᶠ x in 𝓝 v, DifferentiableAt ℂ (fun u => T u a b) x) → IsUnit (T v).det → (∀ a b, ∀ᶠ x in 𝓝 v, DifferentiableAt ℂ (fun u => K u a b) x) → IsUnit (K v).det → (∀ a b, ∀ᶠ x in 𝓝 v, DifferentiableAt ℂ (fun u => K' u a b) x) → IsUnit (K' v).det → (∀ᶠ x in 𝓝 v, G₂ x = T x * G x * (K x)ᴴ ∧ G₂' x = T x * G' x * (K' x)ᴴ) → ∀ k, powAt G₂ v k = powAt G v k ∧ chernAt G₂ v k = chernAt G v k ∧ transAt G₂ G₂' v k = transAt G G' v k := by
  intro n r _ _ G G' G₂ G₂' T K K' v hG uG hG' uG' hT uT hK uK hK' uK' h k
  obtain ⟨c₁, f₁⟩ := GlobalTheory.ChernCalc.FrameChange.conn_curv_frame n r G G₂ T K v hG uG hT uT hK uK (h.mono fun _ hx => hx.1)
  obtain ⟨c₂, f₂⟩ := GlobalTheory.ChernCalc.FrameChange.conn_curv_frame n r G' G₂' T K' v hG' uG' hT uT hK' uK' (h.mono fun _ hx => hx.2)
  have u : (T v)ᵀ * (T v)ᵀ⁻¹ = 1 := Matrix.mul_nonsing_inv _ (by rwa [Matrix.det_transpose])
  have uE : (T v)ᵀ.map (algebraMap ℂ (Ev n)) * (T v)ᵀ⁻¹.map (algebraMap ℂ (Ev n)) = 1 := by
    rw [← Matrix.map_mul, u, Matrix.map_one _ (map_zero _) (map_one _)]
  have uC : (T v)ᵀ.map (C : ℂ →+* MvPolynomial (Fin n × Fin n) ℂ) * (T v)ᵀ⁻¹.map C = 1 := by
    rw [← Matrix.map_mul, u, Matrix.map_one _ (map_zero _) (map_one _)]
  refine ⟨?_, ?_, ?_⟩
  · rw [powAt, curvEv_conj f₁, conj_pow uE, trace_conj' uE, powAt]
  · rw [chernAt, chernPoly, curvPoly_conj f₁, ← neg_mul, ← mul_neg, charpolyRev_conj uC, chernAt, chernPoly]
  · have c (ξ : V n) : conn G₂ v ξ - conn G₂' v ξ = (T v)ᵀ⁻¹ * (conn G v ξ - conn G' v ξ) * (T v)ᵀ := by
      rw [c₁, c₂, ← mul_sub, add_sub_add_right_eq_sub, ← sub_mul, mul_assoc]
    unfold transAt
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun i _ => ?_
    rw [c, curvEv_conj f₁, curvEv_conj f₂, conj_pow uE, conj_pow uE, Matrix.map_mul, Matrix.map_mul,
      conj_mul_three uE, trace_conj' uE]

end GlobalTheory.ChernCalc.FrameInv
