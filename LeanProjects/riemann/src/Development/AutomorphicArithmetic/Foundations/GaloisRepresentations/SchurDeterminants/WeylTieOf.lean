import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SchurDeterminants.SchurYOffClr

noncomputable section

open Finset MvPolynomial

namespace UpperTheory.Gal.Schur

private theorem vdm_ne {K : Type} [Field K] {n : ℕ} (g : Fin n → K)
    (hg : Function.Injective g) : vdm g ≠ 0 := by
  unfold vdm
  refine Finset.prod_ne_zero_iff.2 fun i _ => Finset.prod_ne_zero_iff.2 fun j hj => ?_
  refine sub_ne_zero.2 fun h => ?_
  have := hg h
  subst this
  simp at hj

private theorem num_eq {K : Type} [Field K] {n : ℕ} (l : Fin n → ℤ) (m : ℕ) (lam : Fin n → ℕ)
    (g : Fin n → K) (hl : ∀ i, l i + m = lam i) (h0 : ∀ i, g i ≠ 0) :
    (∏ k, g k) ^ m * altnZ (fun i => l i + n - 1 - (i : ℕ)) g = altn (shift lam) g := by
  unfold altnZ altn shift
  rw [← Finset.prod_pow, ← Matrix.det_mul_row (fun k => g k ^ m)]
  congr 1
  ext i j
  simp only [Matrix.of_apply]
  rw [← zpow_natCast (g j) m, ← zpow_natCast (g j) (lam i + (n - 1 - (i : ℕ))), ← zpow_add₀ (h0 j)]
  congr 1
  have h1 := hl i
  have h2 := i.isLt
  push_cast
  omega

theorem weylTie_of : Comparison₂ → WeylTie := by
  intro hT K _ _ n l m lam g hl hg h0
  have hv := vdm_ne g hg
  have hp : (∏ k, g k) ^ m ≠ 0 := pow_ne_zero _ (prod_ne_zero_iff.mpr fun k _ => h0 k)
  rw [div_eq_div_iff hv hp, hT K n lam g, ← num_eq l m lam g hl h0]
  ring

end UpperTheory.Gal.Schur
