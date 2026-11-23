import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRatioOfWeight
open Filter Topology MvPolynomial GlobalTheory.HSAmp

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HSAmp.HomInj

theorem aeval_mul_hom {σ R A : Type} [CommRing R] [CommRing A] [Algebra R A] {P : MvPolynomial σ R} {q : ℕ} (hP : P.IsHomogeneous q)
    (c : A) (z : σ → A) : aeval (fun i => c * z i) P = c ^ q * aeval z P := by
  conv_lhs => rw [P.as_sum]
  conv_rhs => rw [P.as_sum]
  rw [map_sum, map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hd := hP (mem_support_iff.mp hm)
  simp only [aeval_monomial, mul_pow]
  rw [Finsupp.prod_mul, ← hd]
  have : (m.prod fun _ k => c ^ k) = c ^ (Finsupp.weight 1 m) := by
    simp [Finsupp.prod, Finset.prod_pow_eq_pow_sum, Finsupp.weight_apply, Finsupp.sum]
  rw [this]; ring

def dehom (D : ℕ) : MvPolynomial (Fin (D + 1)) ℤ →ₐ[ℤ] MvPolynomial (Fin D) ℤ :=
  aeval (Fin.cons 1 X)

theorem aeval_dehom {A : Type} [CommRing A] [Algebra ℤ A] {D : ℕ} (w : Fin D → A) (P : MvPolynomial (Fin (D + 1)) ℤ) :
    aeval w (dehom D P) = aeval (Fin.cons 1 w : Fin (D + 1) → A) P := by
  rw [dehom, ← AlgHom.comp_apply, comp_aeval]
  congr 2
  funext i
  refine Fin.cases ?_ (fun j => ?_) i <;> simp

theorem dehom_eq_zero {D q : ℕ} {P : MvPolynomial (Fin (D + 1)) ℤ} (hP : P.IsHomogeneous q)
    (h : dehom D P = 0) : P = 0 := by
  let R := MvPolynomial (Fin (D + 1)) ℤ
  let F := FractionRing R
  have hinj : Function.Injective (algebraMap R F) := IsFractionRing.injective R F
  set c : F := algebraMap R F (X 0) with hc
  have hc0 : c ≠ 0 := by
    rw [hc, Ne, ← map_zero (algebraMap R F)]
    exact fun e => X_ne_zero (R := ℤ) (0 : Fin (D + 1)) (hinj e)
  let z : Fin (D + 1) → F := fun i => algebraMap R F (X i) / c
  have hz : (fun i => algebraMap R F (X i)) = fun i => c * z i := by
    funext i; exact (mul_div_cancel₀ _ hc0).symm
  have hz0 : z = Fin.cons 1 (fun j => z j.succ) := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · show algebraMap R F (X 0) / c = 1
      exact div_self hc0
    · simp
  have key : algebraMap R F P = c ^ q * aeval z P := by
    have e1 : algebraMap R F P = aeval (fun i => algebraMap R F (X i)) P := by
      rw [← Function.comp_def (algebraMap R F) X, aeval_algebraMap_apply, aeval_X_left_apply]
    rw [e1, hz]
    exact aeval_mul_hom hP c z
  have hzP : aeval z P = 0 := by
    have e2 := aeval_dehom (fun j => z j.succ) P
    rw [h, map_zero] at e2
    rw [hz0]; exact e2.symm
  apply hinj
  rw [key, hzP, mul_zero, map_zero]

end GlobalTheory.HSAmp.HomInj

namespace GlobalTheory.HSAmp

open GlobalTheory.HSAmp.HomInj in

theorem homogComb_eq_zero : ∀ (K : Type) [Field K] [CharZero K] (D : ℕ) (x : Fin (D + 1) → K), (∀ j, x j ≠ 0) →
    AlgebraicIndependent ℤ (fun j : Fin D => x j.succ / x 0) → FiniteDimensional (ratF x) K →
    ∀ (ι : Type) [Fintype ι] (g : ι → K), LinearIndependent (ratF x) g → ∀ (q : ℕ)
    (T : ι → MvPolynomial (Fin (D + 1)) ℤ), (∀ i, (T i).IsHomogeneous q) → ∑ i, aeval x (T i) * g i = 0 → T = 0 := by
  intro K _ _ D x hx hind _ ι _ g hg q T hT hsum
  let y : Fin (D + 1) → K := fun j => x j / x 0
  have hy : ∀ j, y j ∈ ratF x := by
    intro j
    refine Fin.cases ?_ (fun j => ?_) j
    · simp only [y, div_self (hx 0)]; exact (ratF x).one_mem
    · exact Subfield.subset_closure ⟨j, rfl⟩
  let y' : Fin (D + 1) → ratF x := fun j => ⟨y j, hy j⟩
  have hxy : x = fun j => x 0 * y j := by
    funext j; exact (mul_div_cancel₀ _ (hx 0)).symm
  have hval : ∀ i, aeval y (T i) = ((aeval y' (T i) : ratF x) : K) := by
    intro i
    show _ = algebraMap (ratF x) K _
    rw [← aeval_algebraMap_apply]
    rfl
  have h1 : ∀ i, aeval x (T i) = x 0 ^ q * aeval y (T i) := by
    intro i
    rw [← aeval_mul_hom (hT i) (x 0) y]
    exact congrArg (fun v => aeval v (T i)) hxy
  have hsum' : ∑ i, aeval y' (T i) • g i = 0 := by
    have hq : x 0 ^ q ≠ 0 := pow_ne_zero _ (hx 0)
    have : x 0 ^ q * ∑ i, aeval y' (T i) • g i = 0 := by
      rw [Finset.mul_sum, ← hsum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [h1, hval, Subfield.smul_def, smul_eq_mul]; ring
    exact (mul_eq_zero.mp this).resolve_left hq
  have h0 : ∀ i, aeval y (T i) = 0 := by
    intro i
    rw [hval, Fintype.linearIndependent_iff.1 hg _ hsum' i]; rfl
  have hy0 : y = Fin.cons 1 (fun j : Fin D => x j.succ / x 0) := by
    funext j
    refine Fin.cases ?_ (fun j => ?_) j
    · simp [y, div_self (hx 0)]
    · simp [y]
  funext i
  apply dehom_eq_zero (hT i)
  apply (algebraicIndependent_iff_injective_aeval.1 hind)
  rw [aeval_dehom, ← hy0, h0, map_zero]

end GlobalTheory.HSAmp
