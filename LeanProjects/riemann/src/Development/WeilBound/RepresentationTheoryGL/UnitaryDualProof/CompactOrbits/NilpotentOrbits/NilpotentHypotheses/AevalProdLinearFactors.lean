import Mathlib

noncomputable section

open Polynomial

namespace PositivityTheory.RgUd.T.Nil.Asm

section

variable {M : Type*} [AddCommGroup M] [Module ℂ M]

theorem pow_mem (K : Submodule ℂ M) (R : Module.End ℂ M) (hK : ∀ m ∈ K, R m ∈ K) :
    ∀ (j : ℕ), ∀ m ∈ K, (R ^ j) m ∈ K := by
  intro j
  induction j with
  | zero => intro m hm; simpa using hm
  | succ j ih => intro m hm; rw [pow_succ', Module.End.mul_apply]; exact hK _ (ih m hm)

theorem aeval_mem (K : Submodule ℂ M) (R : Module.End ℂ M) (hK : ∀ m ∈ K, R m ∈ K) (p : ℂ[X]) :
    ∀ m ∈ K, (aeval R p) m ∈ K := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => intro m hm; rw [map_add, LinearMap.add_apply]; exact K.add_mem (hp m hm) (hq m hm)
  | monomial j a =>
    intro m hm
    rw [aeval_monomial, Module.End.mul_apply, Algebra.algebraMap_eq_smul_one, LinearMap.smul_apply,
      Module.End.one_apply]
    exact K.smul_mem _ (pow_mem K R hK j m hm)

theorem isCoprime_list_prod_left {R : Type*} [CommRing R] {ι : Type*} (f : ι → R) (z : R) :
    ∀ l : List ι, (∀ x ∈ l, IsCoprime (f x) z) → IsCoprime (l.map f).prod z := by
  intro l
  induction l with
  | nil => intro _; simpa using isCoprime_one_left
  | cons x t ih =>
    intro h
    rw [List.map_cons, List.prod_cons]
    exact (h x (List.mem_cons_self)).mul_left (ih fun y hy => h y (List.mem_cons_of_mem _ hy))

theorem isCoprime_list_prod_right {R : Type*} [CommRing R] {ι : Type*} (f : ι → R) (z : R) :
    ∀ l : List ι, (∀ x ∈ l, IsCoprime z (f x)) → IsCoprime z (l.map f).prod := by
  intro l h
  exact (isCoprime_list_prod_left f z l fun x hx => (h x hx).symm).symm

theorem lin_comb (α β γ u0 v0 : ℂ) :
    C u0 * (X - C α) + C v0 * (C β - C γ * X) = C (u0 * (-α) + v0 * β) + C (u0 - v0 * γ) * X := by
  simp only [C_add, C_mul, C_neg, C_sub]
  ring

theorem isCoprime_lin (α β γ : ℂ) (h : β - γ * α ≠ 0) : IsCoprime (X - C α) (C β - C γ * X) := by
  refine ⟨C (γ / (β - γ * α)), C (1 / (β - γ * α)), ?_⟩
  rw [lin_comb]
  have e1 : γ / (β - γ * α) - 1 / (β - γ * α) * γ = 0 := by ring
  rw [e1, map_zero, zero_mul, add_zero]
  have e2 : (γ / (β - γ * α)) * (-α) + (1 / (β - γ * α)) * β = 1 := by
    field_simp
    ring
  rw [e2, map_one]

theorem aeval_prod_lin (R : Module.End ℂ M) (α : ℝ → ℂ) (a : List ℝ) :
    aeval R ((a.map fun x => X - C (α x)).prod) = ((a.map fun x => R - α x • LinearMap.id).prod : Module.End ℂ M) := by
  rw [map_list_prod, List.map_map]
  congr 1
  refine List.map_congr_left fun x _ => ?_
  simp [Algebra.algebraMap_eq_smul_one, Module.End.one_eq_id]

theorem aeval_prod_linear_factors (R : Module.End ℂ M) (β : ℂ) (γ : ℝ → ℂ) (a : List ℝ) :
    aeval R ((a.map fun x => C β - C (γ x) * X).prod) =
      ((a.map fun x => β • LinearMap.id - γ x • R).prod : Module.End ℂ M) := by
  rw [map_list_prod, List.map_map]
  congr 1
  refine List.map_congr_left fun x _ => ?_
  show aeval R (C β - C (γ x) * X) = β • LinearMap.id - γ x • R
  rw [map_sub, map_mul, aeval_C, aeval_C, aeval_X, Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one,
    smul_mul_assoc, one_mul]
  rfl

theorem pow_mul_prod (R R' : Module.End ℂ M) (hRR : R * R' = 1) (hR'R : R' * R = 1) (β : ℂ) (γ : ℝ → ℂ) :
    ∀ l : List ℝ, R ^ l.length * ((l.map fun x => β • R' - γ x • (1 : Module.End ℂ M)).prod) =
      (l.map fun x => β • (1 : Module.End ℂ M) - γ x • R).prod := by
  have hc : Commute R R' := hRR.trans hR'R.symm
  intro l
  induction l with
  | nil => simp
  | cons x t ih =>
    rw [List.map_cons, List.prod_cons, List.map_cons, List.prod_cons, List.length_cons, pow_succ', mul_assoc]
    have hcm : Commute (R ^ t.length) (β • R' - γ x • (1 : Module.End ℂ M)) :=
      ((hc.pow_left _).smul_right β).sub_right ((Commute.one_right _).smul_right _)
    rw [← mul_assoc (R ^ t.length), hcm.eq, mul_assoc, ih, ← mul_assoc]
    congr 1
    rw [mul_sub, mul_smul_comm, hRR, mul_smul_comm, mul_one]

end

theorem bez' {M : Type*} [AddCommGroup M] [Module ℂ M] (K : Submodule ℂ M) (R R' : M →ₗ[ℂ] M)
    (hRR : R ∘ₗ R' = LinearMap.id) (hR'R : R' ∘ₗ R = LinearMap.id) (hK : ∀ m ∈ K, R m ∈ K) (c : ℝ) (hc : 1 < c)
    (d : ℕ) (a : List ℝ) (ha : ∀ x ∈ a, 2 * x < d) (ζ : M)
    (h1 : ((a.map fun x => R - ((c ^ x : ℝ) : ℂ) • LinearMap.id).prod : Module.End ℂ M) ζ ∈ K)
    (h2 : ((a.map fun x => ((c ^ (d : ℝ) : ℝ) : ℂ) • R' - ((c ^ x : ℝ) : ℂ) • LinearMap.id).prod : Module.End ℂ M) ζ ∈ K) :
    ζ ∈ K := by
  set β : ℂ := ((c ^ (d : ℝ) : ℝ) : ℂ)
  set γ : ℝ → ℂ := fun x => ((c ^ x : ℝ) : ℂ)
  have hRR' : (R : Module.End ℂ M) * R' = 1 := hRR
  have hR'R' : (R' : Module.End ℂ M) * R = 1 := hR'R

  have hQ : ((a.map fun x => β • (1 : Module.End ℂ M) - γ x • R).prod : Module.End ℂ M) ζ ∈ K := by
    rw [← pow_mul_prod R R' hRR' hR'R' β γ a, Module.End.mul_apply]
    exact pow_mem K R hK _ _ h2

  have hc0 : 0 < c := by linarith
  have hcop : IsCoprime ((a.map fun x => X - C (γ x)).prod) ((a.map fun x => C β - C (γ x) * X).prod) := by
    refine isCoprime_list_prod_left _ _ a fun x hx => isCoprime_list_prod_right _ _ a fun y hy => ?_
    refine isCoprime_lin (γ x) β (γ y) ?_
    have hlt : c ^ y * c ^ x < c ^ (d : ℝ) := by
      rw [← Real.rpow_add hc0]
      exact Real.rpow_lt_rpow_of_exponent_lt hc (by linarith [ha x hx, ha y hy])
    intro h0
    have : (c ^ (d : ℝ) : ℝ) = c ^ y * c ^ x := by
      have h0' : β = γ y * γ x := sub_eq_zero.1 h0
      simp only [β, γ] at h0'
      exact_mod_cast h0'
    linarith
  obtain ⟨u, v, huv⟩ := hcop
  have key := congrArg (fun p => (aeval (R : Module.End ℂ M) p) ζ) huv
  simp only [map_add, map_mul, map_one, LinearMap.add_apply, Module.End.mul_apply, Module.End.one_apply] at key
  rw [← key]
  refine K.add_mem (aeval_mem K R hK u _ ?_) (aeval_mem K R hK v _ ?_)
  · rw [aeval_prod_lin R γ a]; exact h1
  · rw [aeval_prod_linear_factors R β γ a]
    convert hQ using 3
    refine List.map_congr_left fun x _ => ?_
    rfl

end PositivityTheory.RgUd.T.Nil.Asm
