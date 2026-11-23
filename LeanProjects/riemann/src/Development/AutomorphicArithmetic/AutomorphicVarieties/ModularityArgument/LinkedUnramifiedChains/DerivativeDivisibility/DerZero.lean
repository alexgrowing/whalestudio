import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.CmpPrime
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.DerivativeDivisibility.CmpPrime
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.DerivativeDivisibility.CondField

open Polynomial UpperTheory.V.Alg

private theorem derivation_pow_eq_nsmul_pow_pred_mul {O B K : Type} [CommRing O] [CommRing B] [Field K] [Algebra O B]
    [Algebra O K] (x : B →ₐ[O] K) (δ : B →ₗ[O] K)
    (hL : ∀ f g : B, δ (f * g) = x f * δ g + x g * δ f) (t : B) (n : ℕ) :
    δ (t ^ n) = (n : K) * x t ^ (n - 1) * δ t := by
  induction n with
  | zero =>
    have h1 := hL 1 1
    simp only [mul_one, map_one, one_mul] at h1
    rw [pow_zero, Nat.cast_zero, zero_mul, zero_mul]
    linear_combination (-1 : K) * h1
  | succ k ih =>
    rw [pow_succ, hL, ih, map_pow]
    cases k with
    | zero => simp
    | succ m =>
      simp only [Nat.add_sub_cancel]
      push_cast
      ring

private theorem derivation_eval2_eq_eval2_derivative_mul {O Λ B K : Type} [CommRing O] [CommRing Λ] [CommRing B] [Field K]
    [Algebra O Λ] [Algebra O B] [Algebra O K] (lam : Λ →ₐ[O] B) (x : B →ₐ[O] K) (δ : B →ₗ[O] K)
    (hL : ∀ f g : B, δ (f * g) = x f * δ g + x g * δ f) (hlam : ∀ c : Λ, δ (lam c) = 0)
    (t : B) (q : Λ[X]) :
    δ (eval₂ (lam : Λ →+* B) t q) = x (eval₂ (lam : Λ →+* B) t (derivative q)) * δ t := by
  induction q using Polynomial.induction_on' with
  | add p r hp hr =>
    rw [eval₂_add, map_add, hp, hr, derivative_add, eval₂_add, map_add, add_mul]
  | monomial n c =>
    rw [derivative_monomial, eval₂_monomial, eval₂_monomial]
    change δ (lam c * t ^ n) = x (lam (c * n) * t ^ (n - 1)) * δ t
    rw [hL, hlam, mul_zero, add_zero, derivation_pow_eq_nsmul_pow_pred_mul x δ hL]
    simp only [map_mul, map_natCast, map_pow]
    ring

private theorem eval_derivative_ne_zero_of_rootMultiplicity_eq_one {K : Type} [Field K] (F : K[X]) (a : K) (h : rootMultiplicity a F = 1) :
    eval a (derivative F) ≠ 0 := by
  have hF0 : F ≠ 0 := by
    rintro rfl
    simp at h
  obtain ⟨q, hq, hnd⟩ := exists_eq_pow_rootMultiplicity_mul_and_not_dvd F hF0 a
  rw [h, pow_one] at hq
  rw [hq, derivative_mul, derivative_sub, derivative_X, derivative_C, sub_zero, one_mul, eval_add,
    eval_mul, eval_sub, eval_X, eval_C, sub_self, zero_mul, add_zero]
  rw [dvd_iff_isRoot] at hnd
  exact hnd

theorem UpperTheory.V.J.derZero :
    UpperTheory.V.J.DerZero := by
  unfold UpperTheory.V.J.DerZero
  intro O Λ B K _ _ _ _ _ _ _ _ _ _ lam J t s g hC x i hker hmult δ hδ hJ hlam
  have hL : ∀ f g : B, δ (f * g) = x f * δ g + x g * δ f := fun f g => hδ f g
  have hx : ∀ q : Λ[X], x (eval₂ (lam : Λ →+* B) t q) =
      eval (x t) (map ((x.comp lam : Λ →ₐ[O] K) : Λ →+* K) q) := by
    intro q
    rw [eval_map]
    exact Polynomial.hom_eval₂ q (lam : Λ →+* B) (x : B →+* K) t
  have hD : ∀ q : Λ[X], δ (eval₂ (lam : Λ →+* B) t q) =
      x (eval₂ (lam : Λ →+* B) t (derivative q)) * δ t :=
    fun q => derivation_eval2_eq_eval2_derivative_mul lam x δ hL hlam t q
  have hprod : (∏ j, g j) = g i * ∏ j ∈ Finset.univ.erase i, g j :=
    (Finset.mul_prod_erase _ _ (Finset.mem_univ i)).symm
  have hF' : x (eval₂ (lam : Λ →+* B) t (derivative (∏ j, g j))) ≠ 0 := by
    have h := eval_derivative_ne_zero_of_rootMultiplicity_eq_one _ _ hmult
    rwa [derivative_map, ← hx] at h
  have hδt : δ t = 0 := by
    have h1 := hD (∏ j, g j)
    rw [hJ _ hC.kill] at h1
    exact (mul_eq_zero.mp h1.symm).resolve_left hF'
  have hδP : ∀ q : Λ[X], δ (eval₂ (lam : Λ →+* B) t q) = 0 := by
    intro q
    rw [hD, hδt, mul_zero]
  have hgi : x (eval₂ (lam : Λ →+* B) t (g i)) = 0 := by
    have hm : eval₂ (lam : Λ →+* B) t (g i) ∈ UpperTheory.V.J.cmp lam J t g i := by
      rw [UpperTheory.V.J.cmp, Submodule.mem_colon_singleton, smul_eq_mul, ← eval₂_mul, ← hprod]
      exact hC.kill
    exact RingHom.mem_ker.mp (hker hm)
  rw [hprod, derivative_mul, eval₂_add, eval₂_mul, eval₂_mul, map_add, map_mul, map_mul, hgi,
    zero_mul, add_zero] at hF'
  have hgd := left_ne_zero_of_mul hF'
  have hEn := right_ne_zero_of_mul hF'
  have hcmp : ∀ b ∈ UpperTheory.V.J.cmp lam J t g i, δ b = 0 := by
    intro b hb
    have hxb : x b = 0 := RingHom.mem_ker.mp (hker hb)
    have hbe : b * eval₂ (lam : Λ →+* B) t (∏ j ∈ Finset.univ.erase i, g j) ∈ J := by
      rw [UpperTheory.V.J.cmp, Submodule.mem_colon_singleton] at hb
      exact hb
    have h1 := hL b (eval₂ (lam : Λ →+* B) t (∏ j ∈ Finset.univ.erase i, g j))
    rw [hJ _ hbe, hxb, zero_mul, zero_add] at h1
    exact (mul_eq_zero.mp h1.symm).resolve_left hEn
  ext a
  obtain ⟨P, hP⟩ := UpperTheory.V.J.cond O Λ B lam J t s g hC i a
  have h1 := hcmp _ hP
  rw [map_sub, hδP, sub_zero, hL, hδP, mul_zero, add_zero] at h1
  exact (mul_eq_zero.mp h1).resolve_left hgd
