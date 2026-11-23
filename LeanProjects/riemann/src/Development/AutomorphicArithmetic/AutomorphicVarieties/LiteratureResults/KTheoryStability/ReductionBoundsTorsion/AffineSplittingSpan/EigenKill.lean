import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.AffineSplittingSpan.Transfer

noncomputable section

open Polynomial

namespace PositivityTheory.KB.SplitAffineSpectral.EigenLocalizationShapes

def gpoly (Λ : ℂ) : ℝ[X] := X ^ 2 - C (2 * Λ.re) * X + C (Complex.normSq Λ)

theorem gpoly_eval_one (Λ : ℂ) : (gpoly Λ).eval 1 = Complex.normSq (1 - Λ) := by
  simp only [gpoly, eval_add, eval_sub, eval_pow, eval_X, eval_mul, eval_C, Complex.normSq_apply,
    Complex.sub_re, Complex.one_re, Complex.sub_im, Complex.one_im]
  ring

theorem mapOp_apply {A : Type} (φ : A → A) (m : ℕ) (F : (Fin m → A) → ℝ) (y : Fin m → A) :
    mapOp φ m F y = F fun i => φ (y i) := rfl

theorem kill_one {A : Type} (φ : A → A) (m : ℕ) (E : (Fin m → A) → ℂ) (Λ z : ℂ)
    (hE : ∀ y, E (fun i => φ (y i)) = Λ * E y) :
    aeval (mapOp φ m) (gpoly Λ) (fun y => (z * E y).re) = 0 := by
  simp only [gpoly, map_add, map_sub, map_mul, aeval_X, aeval_C, map_pow]
  funext y
  simp only [LinearMap.add_apply, LinearMap.sub_apply, Module.End.mul_apply, pow_two,
    Module.algebraMap_end_apply, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, mapOp_apply,
    hE, Pi.zero_apply]
  simp only [Complex.mul_re, Complex.mul_im, Complex.normSq_apply]
  ring

theorem kill_sum {A : Type} (φ : A → A) (m : ℕ) {ι : Type} [Fintype ι] [DecidableEq ι]
    (E : ι → (Fin m → A) → ℂ) (Λ z : ι → ℂ) (hE : ∀ j y, E j (fun i => φ (y i)) = Λ j * E j y)
    (F : (Fin m → A) → ℝ) (hF : ∀ y, (F y : ℂ) = ∑ j, z j * E j y) :
    aeval (mapOp φ m) (∏ j, gpoly (Λ j)) F = 0 := by
  have hF' : F = ∑ j, fun y => (z j * E j y).re := by
    funext y
    rw [Finset.sum_apply, ← Complex.re_sum, ← hF y, Complex.ofReal_re]
  rw [hF', map_sum]
  refine Finset.sum_eq_zero fun j _ => ?_
  rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ j), map_mul, Module.End.mul_apply,
    kill_one φ m (E j) (Λ j) (z j) (hE j), map_zero]

theorem cup_kill {A : Type} [Group A] (φ : A →* A) {ι : Type} [Fintype ι] [DecidableEq ι]
    (β : ι → Additive A → ℂ) (lam : ι → ℂ)
    (hβ : ∀ j x, β j (Additive.ofMul (φ x)) = lam j * β j (Additive.ofMul x))
    (hspan : ∀ α : Additive A →+ ℝ, ∃ c : ι → ℂ, ∀ x, (α x : ℂ) = ∑ j, c j * β j x) (q : ℕ)
    (α : Fin (q + 1) → (Additive A →+ ℝ)) :
    aeval (mapOp φ (q + 2)) (∏ J : Fin (q + 1) → ι, gpoly (∏ i, lam (J i))) (cupH α) = 0 := by
  choose c hc using hspan
  let d : Fin (q + 1) → (Fin (q + 2) → A) → Additive A :=
    fun i y => Additive.ofMul ((y i.castSucc)⁻¹ * y i.succ)
  let E : (Fin (q + 1) → ι) → (Fin (q + 2) → A) → ℂ := fun J y => ∏ i, β (J i) (d i y)
  let Λ : (Fin (q + 1) → ι) → ℂ := fun J => ∏ i, lam (J i)
  let z : (Fin (q + 1) → ι) → ℂ := fun J => ∏ i, c (α i) (J i)
  have hE : ∀ J y, E J (fun i => φ (y i)) = Λ J * E J y := by
    intro J y
    simp only [E, Λ]
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    have : d i (fun k => φ (y k)) = Additive.ofMul (φ ((y i.castSucc)⁻¹ * y i.succ)) := by
      simp only [d, map_mul, map_inv]
    rw [this, hβ]
  have hF : ∀ y, (cupH α y : ℂ) = ∑ J, z J * E J y := by
    intro y
    have h1 : (cupH α y : ℂ) = ∏ i, ∑ j, c (α i) j * β j (d i y) := by
      rw [cupH, Complex.ofReal_prod]
      exact Finset.prod_congr rfl fun i _ => hc (α i) _
    rw [h1, Finset.prod_univ_sum, Fintype.piFinset_univ]
    refine Finset.sum_congr rfl fun J _ => ?_
    simp only [z, E]
    rw [Finset.prod_mul_distrib]
  exact kill_sum (⇑φ) (q + 2) E Λ z hE (cupH α) hF

end PositivityTheory.KB.SplitAffineSpectral.EigenLocalizationShapes
