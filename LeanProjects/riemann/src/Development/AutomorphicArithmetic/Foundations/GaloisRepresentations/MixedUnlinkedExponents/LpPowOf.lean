import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.MixedUnlinkedExponents.ValsExtOf

noncomputable section

open Polynomial

namespace UpperTheory.Gal.GamX

private lemma lp_zero : lp 0 = 1 := by simp [lp]

private lemma lp_cons (a : ℂˣ) (A : Multiset ℂˣ) :
    lp (a ::ₘ A) = (1 - C ((a : ℂˣ) : ℂ) * X) * lp A := by
  simp [lp]

private lemma lp_nsmul (f : ℕ) (B : Multiset ℂˣ) : lp (f • B) = lp B ^ f := by
  simp [lp, Multiset.map_nsmul, Multiset.prod_nsmul]

private lemma prod_factor {f : ℕ} (hf : 0 < f) (a : ℂ) :
    ∏ u ∈ nthRootsFinset f (1 : ℂ), (1 - C a * (C u * X)) = 1 - C (a ^ f) * X ^ f := by
  classical
  set S := nthRootsFinset f (1 : ℂ) with hS
  have hζ := Complex.isPrimitiveRoot_exp f hf.ne'
  have mem : ∀ u, u ∈ S ↔ u ^ f = 1 := fun u => mem_nthRootsFinset hf 1
  have ne0 : ∀ u ∈ S, u ≠ 0 := by
    intro u hu h0
    rw [mem, h0, zero_pow hf.ne'] at hu
    exact zero_ne_one hu
  have h1 : ∀ w : ℂ[X], ∏ u ∈ S, (w - C u) = w ^ f - 1 := by
    intro w
    have e := congrArg (aeval w) (X_pow_sub_one_eq_prod hf hζ)
    simp only [map_sub, map_one, aeval_X_pow, map_prod, aeval_X, aeval_C,
      Polynomial.algebraMap_eq] at e
    exact e.symm
  have h3 : ∀ w : ℂ[X], ∏ u ∈ S, (w - C u⁻¹) = ∏ u ∈ S, (w - C u) := by
    intro w
    refine Finset.prod_nbij' (fun u => u⁻¹) (fun u => u⁻¹) ?_ ?_ ?_ ?_ ?_
    · intro u hu
      rw [mem] at hu ⊢
      rw [inv_pow, hu, inv_one]
    · intro u hu
      rw [mem] at hu ⊢
      rw [inv_pow, hu, inv_one]
    · intro u _
      exact inv_inv u
    · intro u _
      exact inv_inv u
    · intro u _
      rfl
  have h2 : ∀ w : ℂ[X], ∏ u ∈ S, (1 - C u * w) = (∏ u ∈ S, (-C u)) * (w ^ f - 1) := by
    intro w
    rw [← h1, ← h3, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl ?_
    intro u hu
    have hc : C u * C u⁻¹ = (1 : ℂ[X]) := by
      rw [← C_mul, mul_inv_cancel₀ (ne0 u hu), C_1]
    linear_combination -hc
  have hc : (∏ u ∈ S, (-C u : ℂ[X])) = -1 := by
    have e := h2 0
    simp only [mul_zero, sub_zero, Finset.prod_const_one, zero_pow hf.ne', zero_sub] at e
    linear_combination e
  have key := h2 (C a * X)
  rw [hc] at key
  calc ∏ u ∈ S, (1 - C a * (C u * X)) = ∏ u ∈ S, (1 - C u * (C a * X)) := by
        refine Finset.prod_congr rfl ?_
        intro u _
        ring
    _ = 1 - C (a ^ f) * X ^ f := by
        rw [key, mul_pow, C_pow]
        ring

private lemma prod_lp {f : ℕ} (hf : 0 < f) (A : Multiset ℂˣ) :
    ∏ u ∈ nthRootsFinset f (1 : ℂ), (lp A).comp (C u * X) =
      (lp (A.map (· ^ f))).comp (X ^ f) := by
  induction A using Multiset.induction_on with
  | empty =>
    simp [lp_zero]
  | cons b A ih =>
    rw [Multiset.map_cons, lp_cons, lp_cons, mul_comp, ← ih]
    simp only [mul_comp, sub_comp, one_comp, C_comp, X_comp]
    rw [Finset.prod_mul_distrib, prod_factor hf, Units.val_pow_eq_pow_val]

theorem lpPowOf : LpPowOf := by
  intro hinj f hf A B h
  apply hinj
  classical
  have hζ := Complex.isPrimitiveRoot_exp f hf.ne'
  apply expand_injective hf
  rw [expand_eq_comp_X_pow, expand_eq_comp_X_pow, ← prod_lp hf, lp_nsmul, pow_comp]
  have e : ∀ u ∈ nthRootsFinset f (1 : ℂ), (lp A).comp (C u * X) = (lp B).comp (X ^ f) := by
    intro u hu
    rw [h, comp_assoc, pow_comp, X_comp, mul_pow, ← C_pow, (mem_nthRootsFinset hf 1).1 hu,
      C_1, one_mul]
  rw [Finset.prod_congr rfl e, Finset.prod_const, hζ.card_nthRootsFinset]

end UpperTheory.Gal.GamX
