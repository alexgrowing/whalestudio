import Mathlib
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.CapelliComplements.FirstLemmaA

namespace ReciprocityTheory.ChartRestriction.G.AR.Up.IntPf

noncomputable section

section Cone

open MvPolynomial

variable {R E : Type*} [CommRing R] [CommRing E] [Algebra R E] {ι : Type*}

def cone (a : ι → E) : MvPolynomial ι R →ₐ[R] Polynomial E :=
  aeval fun i => Polynomial.C (a i) * Polynomial.X

theorem cone_homog (a : ι → E) {f : MvPolynomial ι R} {d : ℕ} (hf : f.IsHomogeneous d) :
    cone a f = Polynomial.monomial d (aeval a f) := by
  classical
  conv_lhs => rw [f.as_sum]
  conv_rhs => rw [f.as_sum]
  rw [map_sum, map_sum, map_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hd : ∑ i ∈ m.support, m i = d := by
    have := hf (mem_support_iff.mp hm)
    simpa [Finsupp.weight_apply, Finsupp.sum] using this
  have hp : (m.prod fun i k => (Polynomial.C (a i) * Polynomial.X) ^ k) =
      Polynomial.C (m.prod fun i k => a i ^ k) * Polynomial.X ^ d := by
    simp only [Finsupp.prod, mul_pow, Finset.prod_mul_distrib, map_prod, map_pow,
      Finset.prod_pow_eq_pow_sum, hd]
  rw [cone, aeval_monomial, aeval_monomial, hp, Polynomial.algebraMap_apply, ← mul_assoc,
    ← Polynomial.C_mul, Polynomial.C_mul_X_pow_eq_monomial]

theorem coeff_cone (a : ι → E) (f : MvPolynomial ι R) (n : ℕ) :
    (cone a f).coeff n = aeval a (homogeneousComponent n f) := by
  classical
  conv_lhs => rw [← sum_homogeneousComponent f]
  rw [map_sum, Polynomial.finsetSum_coeff]
  simp_rw [cone_homog a (homogeneousComponent_isHomogeneous _ f), Polynomial.coeff_monomial]
  rw [Finset.sum_ite_eq']
  split_ifs with h
  · rfl
  · rw [homogeneousComponent_eq_zero _ _ (by simp at h; omega), map_zero]

theorem aeval_mul_homog (q : ι → E) (t : E) {G : MvPolynomial ι R} {m : ℕ} (hG : G.IsHomogeneous m) :
    aeval (fun i => q i * t) G = t ^ m * aeval q G := by
  have h := congrArg ((Polynomial.aeval t : Polynomial E →ₐ[E] E).restrictScalars R)
    (cone_homog (R := R) q hG)
  rw [cone, MvPolynomial.comp_aeval_apply] at h
  simp only [AlgHom.restrictScalars_apply, map_mul, Polynomial.aeval_C, Polynomial.aeval_X,
    Polynomial.aeval_monomial, Algebra.algebraMap_self, RingHom.id_apply] at h
  rw [h, mul_comm]

theorem eval_mul_homog {K : Type*} [CommRing K] (q : ι → K) (t : K) {G : MvPolynomial ι K} {m : ℕ}
    (hG : G.IsHomogeneous m) : eval (fun i => q i * t) G = t ^ m * eval q G := by
  simpa using aeval_mul_homog (R := K) q t hG

end Cone

open MvPolynomial in
theorem exists_cons_one_ne {K : Type*} [Field K] [Infinite K] {n m : ℕ}
    {G : MvPolynomial (Fin (n + 1)) K} (hG : G.IsHomogeneous m) (h0 : G ≠ 0) :
    ∃ c : Fin n → K, eval (Fin.cons 1 c) G ≠ 0 := by
  by_contra! h
  apply h0
  have hX : (X 0 * G : MvPolynomial (Fin (n + 1)) K) = 0 := by
    apply MvPolynomial.funext
    intro p
    rw [map_mul, eval_X, map_zero]
    by_cases hp : p 0 = 0
    · rw [hp, zero_mul]
    · have hq : p = fun i => (Fin.cons 1 (fun k => p k.succ / p 0) : Fin (n + 1) → K) i * p 0 := by
        funext i
        refine Fin.cases ?_ (fun k => ?_) i
        · simp
        · simp [div_mul_cancel₀ _ hp]
      have : eval p G = 0 := by
        rw [hq]
        rw [eval_mul_homog _ _ hG, h, mul_zero]
      rw [this, mul_zero]
  exact (mul_eq_zero.mp hX).resolve_left (X_ne_zero _)

section Int

open MvPolynomial

variable {R E : Type*} [CommRing R] [CommRing E] [Algebra R E] {ι : Type*}

end Int

section Homog

open Polynomial

theorem prod_pow_natDegree_coeff' {B : Type*} [CommRing B] {ι : Type*} (s : Finset ι)
    (v : ι → B[X]) (d : ι → ℕ) (hv : ∀ i, (v i).natDegree ≤ 1) :
    (∏ i ∈ s, v i ^ d i).natDegree ≤ ∑ i ∈ s, d i ∧
      (∏ i ∈ s, v i ^ d i).coeff (∑ i ∈ s, d i) = ∏ i ∈ s, (v i).coeff 1 ^ d i := by
  first | exact Bl.FirstLemmaA.goal1 .. | (apply Bl.FirstLemmaA.goal1 <;> assumption) | (intros; apply Bl.FirstLemmaA.goal1 <;> assumption) | (apply @Bl.FirstLemmaA.goal1 <;> assumption) | (intros; apply @Bl.FirstLemmaA.goal1 <;> assumption) | (apply @Bl.FirstLemmaA.goal1 <;> first | assumption | infer_instance)

end Homog

end

end ReciprocityTheory.ChartRestriction.G.AR.Up.IntPf
