import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullAevalSym
import Development.AbelianVarietyTheory.Definitions.Divisors.IsMetricFrOfIsMetricOn
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ChernDegreeComplex
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CurvPolyPullback
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc
open scoped Matrix ContDiff ComplexOrder

set_option autoImplicit false

namespace GlobalTheory.ChernCalc.HoloPull

noncomputable def subst {n n' : ℕ} (L : V n' →L[ℂ] V n) :
    MvPolynomial (Fin n × Fin n) ℂ →ₐ[ℂ] MvPolynomial (Fin n' × Fin n') ℂ :=
  aeval fun x : Fin n × Fin n => ∑ c, ∑ d, C (L (coordVec c) x.1 * (starRingEnd ℂ) (L (coordVec d) x.2)) *
    (X (c, d) : MvPolynomial (Fin n' × Fin n') ℂ)

theorem sesq_expand {n : ℕ} {r : Type} {F : V n → V n → Matrix r r ℂ} (h : IsSesq F) (ξ η : V n) (i j : r) :
    F ξ η i j = ∑ a, ∑ b, ξ a * (starRingEnd ℂ) (η b) * F (coordVec a) (coordVec b) i j := by
  have e (v : V n) : v = ∑ a, v a • coordVec a := by
    ext b; simp [Pi.single_apply]
  have h1 (s : Finset (Fin n)) (c : Fin n → ℂ) (y : V n) :
      F (∑ a ∈ s, c a • coordVec a) y = ∑ a ∈ s, c a • F (coordVec a) y := by
    induction s using Finset.induction_on with
    | empty => simpa using h.smul_left 0 0 y
    | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, h.add_left, h.smul_left, ih]
  have h2 (s : Finset (Fin n)) (c : Fin n → ℂ) (x : V n) :
      F x (∑ a ∈ s, c a • coordVec a) = ∑ a ∈ s, (starRingEnd ℂ) (c a) • F x (coordVec a) := by
    induction s using Finset.induction_on with
    | empty => simpa using h.smul_right 0 x 0
    | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, h.add_right, h.smul_right, ih]
  conv_lhs => rw [e ξ, e η, h1]
  simp only [h2, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum, mul_assoc]

variable {n n' : ℕ} {r : Type} [Fintype r] [DecidableEq r] {G : V n → Matrix r r ℂ} {φ : V n' → V n} {w : V n'}

theorem curvPoly_comp (hφ : ContDiffAt ℂ 2 φ w) (hG : MContDiffAt ∞ G (φ w)) (hu : IsUnit (G (φ w)).det) :
    curvPoly (fun x => G (φ x)) w = (subst (fderiv ℂ φ w)).mapMatrix (curvPoly G (φ w)) := by
  first
  | exact @_root_.GlobalTheory.CurvatureSesquilinearExpansion.curvPoly_pullback
  | exact _root_.GlobalTheory.CurvatureSesquilinearExpansion.curvPoly_pullback
  | (apply _root_.GlobalTheory.CurvatureSesquilinearExpansion.curvPoly_pullback <;> assumption)
  | (intros; apply _root_.GlobalTheory.CurvatureSesquilinearExpansion.curvPoly_pullback <;> assumption)
  | (intros; apply @_root_.GlobalTheory.CurvatureSesquilinearExpansion.curvPoly_pullback <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.CurvatureSesquilinearExpansion.curvPoly_pullback ..)

theorem curvEv_eq (G : V n → Matrix r r ℂ) (v : V n) :
    curvEv G v = (aeval sym : MvPolynomial (Fin n × Fin n) ℂ →ₐ[ℂ] Ev n).mapMatrix (curvPoly G v) := rfl

theorem charpolyRev_map {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) (M : Matrix r r R) :
    Matrix.charpolyRev (M.map f) = (Matrix.charpolyRev M).map f := by
  rw [Matrix.charpolyRev, Matrix.charpolyRev, ← Polynomial.coe_mapRingHom, RingHom.map_det]
  congr 1
  ext1 i j
  by_cases h : i = j <;> simp [h, Matrix.one_apply]

end GlobalTheory.ChernCalc.HoloPull

namespace GlobalTheory.ChernCalc

open HoloPull in

theorem curv_pow_chern_comp_holo : ∀ (n n' : ℕ) (r : Type) [Fintype r] [DecidableEq r] (G : V n → Matrix r r ℂ) (φ : V n' → V n) (w : V n'), ContDiffAt ℂ 2 φ w → MContDiffAt ∞ G (φ w) → IsUnit (G (φ w)).det → (∀ k l i j, ∀ G' : V n → Matrix r r ℂ, MContDiffAt ∞ G' (φ w) → IsUnit (G' (φ w)).det → ((curvEv (fun x => G (φ x)) w ^ k * curvEv (fun x => G' (φ x)) w ^ l) i j : Alt n') = pull (fderiv ℂ φ w) ((curvEv G (φ w) ^ k * curvEv G' (φ w) ^ l) i j : Alt n)) ∧ ∀ k, (powAt (fun x => G (φ x)) w k : Alt n') = pull (fderiv ℂ φ w) (powAt G (φ w) k) ∧ (chernAt (fun x => G (φ x)) w k : Alt n') = pull (fderiv ℂ φ w) (chernAt G (φ w) k) := by
  intro n n' r _ _ G φ w hφ hG hu
  have key : ∀ k l i j, ∀ G' : V n → Matrix r r ℂ, MContDiffAt ∞ G' (φ w) → IsUnit (G' (φ w)).det →
      ((curvEv (fun x => G (φ x)) w ^ k * curvEv (fun x => G' (φ x)) w ^ l) i j : Alt n') =
        pull (fderiv ℂ φ w) ((curvEv G (φ w) ^ k * curvEv G' (φ w) ^ l) i j : Alt n) := by
    intro k l i j G' hG' hu'
    simp only [curvEv_eq, curvPoly_comp hφ hG hu, curvPoly_comp hφ hG' hu', ← map_pow, ← map_mul]
    simp only [AlgHom.mapMatrix_apply, Matrix.map_apply]
    exact (pull_aeval_sym _ _ _ _).symm
  refine ⟨key, fun k => ⟨?_, ?_⟩⟩
  · have := fun i => key k 0 i i G hG hu
    simp only [pow_zero, mul_one] at this
    simp only [powAt, Matrix.trace, Matrix.diag_apply, AddSubmonoidClass.coe_finsetSum, map_sum, this]
  · have e : chernPoly (fun x => G (φ x)) w k = subst (fderiv ℂ φ w) (chernPoly G (φ w) k) := by
      rw [chernPoly, chernPoly, curvPoly_comp hφ hG hu, ← map_neg]
      exact (congrArg (fun p => Polynomial.coeff p k)
        (charpolyRev_map (subst (fderiv ℂ φ w)).toRingHom _)).trans (Polynomial.coeff_map _ _)
    rw [chernAt, chernAt, e, Subalgebra.coe_smul, Subalgebra.coe_smul, map_smul, pull_aeval_sym]
    rfl

end GlobalTheory.ChernCalc
