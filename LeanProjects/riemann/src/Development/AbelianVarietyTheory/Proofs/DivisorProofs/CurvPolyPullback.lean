import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsMetricFrOfIsMetricOn
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ChernDegreeComplex

noncomputable section

open Matrix MvPolynomial ComplexConjugate
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory.HermFrame GlobalTheory.GoodMetric

namespace GlobalTheory.CurvatureSesquilinearExpansion

theorem eq_sum_coordVec {n : ℕ} (v : V n) : v = ∑ a, v.ofLp a • coordVec a := by
  ext j
  simp [Pi.single_apply]

theorem sesq_expand {n : ℕ} (F : V n → V n → ℂ)
    (h1 : ∀ x y z, F (x + y) z = F x z + F y z) (h2 : ∀ (c : ℂ) x z, F (c • x) z = c * F x z)
    (h3 : ∀ x y z, F x (y + z) = F x y + F x z)
    (h4 : ∀ (c : ℂ) x z, F x (c • z) = conj c * F x z) (ξ η : V n) :
    F ξ η = ∑ a, ∑ b, ξ.ofLp a * conj (η.ofLp b) * F (coordVec a) (coordVec b) := by
  have s1 (z : V n) (f : Fin n → V n) : F (∑ a, f a) z = ∑ a, F (f a) z :=
    map_sum (AddMonoidHom.mk' (fun x => F x z) fun x y => h1 x y z) f Finset.univ
  have s2 (x : V n) (f : Fin n → V n) : F x (∑ a, f a) = ∑ a, F x (f a) :=
    map_sum (AddMonoidHom.mk' (fun z => F x z) fun y z => h3 x y z) f Finset.univ
  conv_lhs => rw [eq_sum_coordVec ξ, eq_sum_coordVec η, s1]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [s2]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [h2, h4, mul_assoc]

theorem curv_expand {n : ℕ} {r : Type} [Fintype r] [DecidableEq r] {G : V n → Matrix r r ℂ} {z : V n}
    (h : MContDiffAt 2 G z) (hu : IsUnit (G z).det) (ξ η : V n) (i j : r) :
    curv G z ξ η i j =
      ∑ a, ∑ b, ξ.ofLp a * conj (η.ofLp b) * curv G z (coordVec a) (coordVec b) i j := by
  have m1 (x y w : V n) : mddbar G z (x + y) w = mddbar G z x w + mddbar G z y w := by
    ext a b; simp
  have m2 (c : ℂ) (x w : V n) : mddbar G z (c • x) w = c • mddbar G z x w := by
    ext a b; simp
  have m3 (x y w : V n) : mddbar G z x (y + w) = mddbar G z x y + mddbar G z x w := by
    ext a b; simp
  have m4 (c : ℂ) (x w : V n) : mddbar G z x (c • w) = conj c • mddbar G z x w := by
    ext a b; simp
  refine sesq_expand (fun ξ η => curv G z ξ η i j) ?_ ?_ ?_ ?_ ξ η
  · intro x y w
    simp only [curv_eq h hu, mdel_add_vec, m1, transpose_add, Matrix.mul_add, Matrix.sub_apply,
      Matrix.add_apply]
    ring
  · intro c x w
    simp only [curv_eq h hu, mdel_smul_vec, m2, transpose_smul, Matrix.mul_smul, Matrix.sub_apply,
      Matrix.smul_apply, smul_eq_mul]
    ring
  · intro x y w
    simp only [curv_eq h hu, mdbar_add_vec, m3, transpose_add, Matrix.mul_add, Matrix.add_mul,
      Matrix.sub_apply, Matrix.add_apply]
    ring
  · intro c x w
    simp only [curv_eq h hu, mdbar_smul_vec, m4, transpose_smul, Matrix.mul_smul, Matrix.smul_mul,
      Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
    ring

theorem curvPoly_pullback : (let d1 : {n n' : ℕ} → (ReciprocityTheory.L2DbarEstimates.V n' →L[ℂ] ReciprocityTheory.L2DbarEstimates.V n) → MvPolynomial (Fin n × Fin n) ℂ →ₐ[ℂ] MvPolynomial (Fin n' × Fin n') ℂ := @(fun {n n' : ℕ} (L : ReciprocityTheory.L2DbarEstimates.V n' →L[ℂ] ReciprocityTheory.L2DbarEstimates.V n) ↦ MvPolynomial.aeval fun (x : Fin n × Fin n) ↦ ∑ c : Fin n', ∑ d : Fin n', (MvPolynomial.C : (fun (x : Fin n) ↦ ℂ) (Prod.fst x) → MvPolynomial (Fin n' × Fin n') ((fun (x : Fin n) ↦ ℂ) (Prod.fst x))) (WithLp.ofLp ((L : ReciprocityTheory.L2DbarEstimates.V n' → ReciprocityTheory.L2DbarEstimates.V n) (GlobalTheory.GoodMetric.coordVec c)) (Prod.fst x) * (starRingEnd ℂ : ℂ → ℂ) (WithLp.ofLp ((L : ReciprocityTheory.L2DbarEstimates.V n' → ReciprocityTheory.L2DbarEstimates.V n) (GlobalTheory.GoodMetric.coordVec d)) (Prod.snd x))) * MvPolynomial.X (c, d)); ∀ {n n' : ℕ} {r : Type} [inst : Fintype r] [inst_1 : DecidableEq r] {G : ReciprocityTheory.L2DbarEstimates.V n → Matrix r r ℂ} {φ : ReciprocityTheory.L2DbarEstimates.V n' → ReciprocityTheory.L2DbarEstimates.V n} {w : ReciprocityTheory.L2DbarEstimates.V n'}, ContDiffAt ℂ (2 : WithTop ℕ∞) φ w → GlobalTheory.HermFrame.MContDiffAt ((⊤ : ℕ∞) : WithTop ℕ∞) G (φ w) → IsUnit (Matrix.det (G (φ w))) → GlobalTheory.GoodMetric.curvPoly (fun (x : ReciprocityTheory.L2DbarEstimates.V n') ↦ G (φ x)) w = (AlgHom.mapMatrix (d1 (fderiv ℂ φ w)) : Matrix r r (MvPolynomial (Fin n × Fin n) ℂ) → Matrix r r (MvPolynomial (Fin n' × Fin n') ℂ)) (GlobalTheory.GoodMetric.curvPoly G (φ w))) := by
  intro d1 n n' r _ _ G φ w hφ hG hu
  have h2 : MContDiffAt 2 G (φ w) := hG.of_le (by norm_cast)
  refine Matrix.ext fun i j => ?_
  simp only [d1, curvPoly, AlgHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, map_sum, map_mul,
    aeval_X, aeval_C, algebraMap_eq, curv_comp_holo h2 hu hφ, Finset.mul_sum]
  symm
  rw [Finset.sum_congr rfl fun a _ => Finset.sum_comm, Finset.sum_comm]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Finset.sum_congr rfl fun a _ => Finset.sum_comm, Finset.sum_comm]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [curv_expand h2 hu (fderiv ℂ φ w (coordVec c))]
  simp only [map_sum, map_mul, Finset.sum_mul]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  ring

end GlobalTheory.CurvatureSesquilinearExpansion
