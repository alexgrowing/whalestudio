import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HeightComparison.HeightOrbitDegreeRatio
import GroundTheory.HeightsAndTheta.Heights.HeightComparison.POrbitDegree
import GroundTheory.HeightsAndTheta.Heights.HeightComparison.POrbitCurve
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial ReciprocityTheory.ChartRestriction.G

noncomputable section

variable {ι : Type} {n : ι → ℕ}

def chartHomogQ (c : (k : ι) → Fin (n k + 1)) (f : MvPolynomial (Coord n) ℚ)
    [Fintype ι] : MvPolynomial (Coord n) ℚ :=
  ∑ m ∈ f.support, C (coeff m f) * ∏ p : Coord n, (X p ^ m p * X ⟨p.1, c p.1⟩ ^ (f.totalDegree - m p))

theorem le_totalDegree_of_mem_support {f : MvPolynomial (Coord n) ℚ} {m : Coord n →₀ ℕ}
    (hm : m ∈ f.support) (p : Coord n) : m p ≤ f.totalDegree :=
  (monomial_le_degreeOf p hm).trans (degreeOf_le_totalDegree f p)

variable [Fintype ι]

theorem aeval_chartHomogQ {S : Type*} [CommRing S] [Algebra ℚ S] (c : (k : ι) → Fin (n k + 1))
    (f : MvPolynomial (Coord n) ℚ) (y : Coord n → S) :
    aeval y (chartHomogQ c f) = ∑ m ∈ f.support, algebraMap ℚ S (coeff m f) *
      ∏ p : Coord n, (y p ^ m p * y ⟨p.1, c p.1⟩ ^ (f.totalDegree - m p)) := by
  simp [chartHomogQ, map_sum, map_prod]

theorem aeval_chartHomogQ_field {K : Type*} [Field K] [Algebra ℚ K] (c : (k : ι) → Fin (n k + 1))
    (f : MvPolynomial (Coord n) ℚ) (y : Coord n → K) (hy : ∀ k, y ⟨k, c k⟩ ≠ 0) :
    aeval y (chartHomogQ c f) = (∏ p : Coord n, y ⟨p.1, c p.1⟩ ^ f.totalDegree) *
      aeval (fun p ↦ y p / y ⟨p.1, c p.1⟩) f := by
  rw [aeval_chartHomogQ, aeval_def, eval₂_eq', Finset.mul_sum]
  refine Finset.sum_congr rfl fun m hm ↦ ?_
  have h : ∀ p : Coord n, y p ^ m p * y ⟨p.1, c p.1⟩ ^ (f.totalDegree - m p) =
      y ⟨p.1, c p.1⟩ ^ f.totalDegree * (y p / y ⟨p.1, c p.1⟩) ^ m p := by
    intro p
    obtain ⟨e, he⟩ := Nat.exists_eq_add_of_le (le_totalDegree_of_mem_support hm p)
    have hyp := hy p.1
    rw [he, Nat.add_sub_cancel_left, pow_add, div_pow]
    field_simp
  simp_rw [h, Finset.prod_mul_distrib]
  ring

theorem coneMapQ_chartHomogQ (x : Cone n (AlgebraicClosure ℚ)) (c : (k : ι) → Fin (n k + 1))
    (f : MvPolynomial (Coord n) ℚ) :
    OrbitCurve.coneMapQ x (chartHomogQ c f) =
      C (aeval (flatCone x) (chartHomogQ c f)) * ∏ p : Coord n, X p.1 ^ f.totalDegree := by
  rw [OrbitCurve.coneMapQ, aeval_chartHomogQ, aeval_chartHomogQ, map_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun m hm ↦ ?_
  have h : ∀ p : Coord n,
      (C (flatCone x p) * X p.1 : MvPolynomial ι (AlgebraicClosure ℚ)) ^ m p *
        (C (flatCone x ⟨p.1, c p.1⟩) * X p.1) ^ (f.totalDegree - m p) =
      C (flatCone x p ^ m p * flatCone x ⟨p.1, c p.1⟩ ^ (f.totalDegree - m p)) *
        X p.1 ^ f.totalDegree := by
    intro p
    obtain ⟨e, he⟩ := Nat.exists_eq_add_of_le (le_totalDegree_of_mem_support hm p)
    rw [he, Nat.add_sub_cancel_left]
    simp only [mul_pow, map_mul, map_pow, pow_add]
    ring
  simp only [h, Finset.prod_mul_distrib, map_mul, map_prod, MvPolynomial.algebraMap_apply]
  ring

theorem aeval_ratio_eq_zero (x : Cone n (AlgebraicClosure ℚ)) (c : (k : ι) → Fin (n k + 1))
    (hc : ∀ k, x k (c k) ≠ 0) {z : Coord n → ℂ} (hz : z ∈ Geo.mcPts (ι := blockIdx n) (orbitIdeal x))
    (hz0 : ∀ k, z ⟨k, c k⟩ ≠ 0) (f : MvPolynomial (Coord n) ℚ)
    (hf : aeval (fun p : Coord n ↦ x p.1 p.2 / x p.1 (c p.1)) f = 0) :
    aeval (fun p ↦ z p / z ⟨p.1, c p.1⟩) f = 0 := by
  have hx : aeval (flatCone x) (chartHomogQ c f) = 0 := by
    rw [aeval_chartHomogQ_field c f (flatCone x) hc]
    exact mul_eq_zero_of_right _ hf
  have hker : chartHomogQ c f ∈ RingHom.ker (OrbitCurve.coneMapQ x) := by
    rw [RingHom.mem_ker, coneMapQ_chartHomogQ, hx, map_zero, zero_mul]
  classical
  rw [OrbitCurve.ker_coneMapQ] at hker
  have hle : ReciprocityTheory.AnForm.R.extQ (orbitIdeal x) ≤
      RingHom.ker (aeval z : MvPolynomial (Coord n) ℚ →ₐ[ℚ] ℂ) := by
    refine Ideal.map_le_iff_le_comap.mpr fun g hg ↦ ?_
    rw [Ideal.mem_comap, RingHom.mem_ker, ← algebraMap_int_eq, aeval_map_algebraMap, aeval_def,
      algebraMap_int_eq, ← eval_map]
    exact hz.2 g hg
  have h := hle hker
  rw [RingHom.mem_ker, aeval_chartHomogQ_field c f z hz0] at h
  exact (mul_eq_zero.mp h).resolve_left
    (Finset.prod_ne_zero_iff.mpr fun p _ ↦ pow_ne_zero _ (hz0 p.1))

variable [DecidableEq ι]

theorem chart_ne_zero_of_mem_mcPts (x : Cone n (AlgebraicClosure ℚ)) (c : (k : ι) → Fin (n k + 1))
    (hc : ∀ k, x k (c k) ≠ 0) {z : Coord n → ℂ}
    (hz : z ∈ Geo.mcPts (ι := blockIdx n) (orbitIdeal x)) (k : ι) : z ⟨k, c k⟩ ≠ 0 := by
  intro h0
  obtain ⟨i, hi⟩ := hz.1 k
  obtain ⟨g, hg0, hg⟩ := exists_int_relation (flatCone x ⟨k, i⟩ / flatCone x ⟨k, c k⟩)
  have h := hz.2 _ (homogForm_mem_orbitIdeal x g ⟨k, i⟩ ⟨k, c k⟩ rfl (hc k) hg)
  rw [eval_homogForm, h0, homog_sum_zero] at h
  exact mul_ne_zero (Int.cast_ne_zero.mpr (Polynomial.leadingCoeff_ne_zero.mpr hg0))
    (pow_ne_zero _ hi) h

end

end GroundTheory.Heights₂.Heights
