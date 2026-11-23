import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.NefFibOfIsNef
open MvPolynomial

namespace GlobalTheory.CompanionTheory.Polarisation

noncomputable def cnt {ι : Type} {m : ℕ} (f : Fin m → ι) : ι →₀ ℕ :=
  ∑ j, Finsupp.single (f j) 1

open Classical in
theorem cnt_apply {ι : Type} {m : ℕ} (f : Fin m → ι) (i : ι) :
    cnt f i = Fintype.card {j // f j = i} := by
  simp [cnt, Finsupp.finset_sum_apply, Finsupp.single_apply, Fintype.card_subtype]

theorem degree_cnt {ι : Type} {m : ℕ} (f : Fin m → ι) : (cnt f).degree = m := by
  classical
  simp [cnt, map_sum]

theorem exists_perm_of_cnt_eq {ι : Type} {m : ℕ} {f g : Fin m → ι} (h : cnt f = cnt g) :
    ∃ σ : Equiv.Perm (Fin m), g = f ∘ σ := by
  classical
  have hc : ∀ i, Nonempty ({j // g j = i} ≃ {j // f j = i}) := fun i => by
    refine Fintype.card_eq.1 ?_
    rw [← cnt_apply, ← cnt_apply, h]
  let e : ∀ i, {j // g j = i} ≃ {j // f j = i} := fun i => (hc i).some
  refine ⟨Equiv.ofFiberEquiv e, ?_⟩
  funext j
  exact (Equiv.ofFiberEquiv_map e j).symm

theorem prod_X_eq {ι : Type} {m : ℕ} (f : Fin m → ι) (a : Fin m → ℝ) :
    ∏ j, (C (a j) * X (f j) : MvPolynomial ι ℝ) = monomial (cnt f) (∏ j, a j) := by
  classical
  have key : ∀ s : Finset (Fin m), ∏ j ∈ s, (C (a j) * X (f j) : MvPolynomial ι ℝ)
      = monomial (∑ j ∈ s, Finsupp.single (f j) 1) (∏ j ∈ s, a j) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | insert x s hx ih =>
      rw [Finset.prod_insert hx, Finset.prod_insert hx, Finset.sum_insert hx, ih, X,
        C_mul_monomial, monomial_mul]
      simp
  exact key Finset.univ

theorem lin_pow {ι : Type} [Fintype ι] (n : ι → ℝ) (m : ℕ) :
    GlobalTheory.ArInt.lin n ^ m = ∑ f : Fin m → ι, monomial (cnt f) (∏ j, n (f j)) := by
  classical
  have h := Finset.prod_univ_sum (fun _ : Fin m => (Finset.univ : Finset ι))
    (fun _ i => (C (n i) * X i : MvPolynomial ι ℝ))
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin, Fintype.piFinset_univ] at h
  rw [GlobalTheory.ArInt.lin, h]
  exact Finset.sum_congr rfl fun f _ => prod_X_eq f (fun j => n (f j))

open Classical in

noncomputable def coef {ι : Type} {m : ℕ} (F : (Fin m → ι) → ℝ) (k : ι →₀ ℕ) : ℝ :=
  if h : ∃ f : Fin m → ι, cnt f = k then F h.choose else 0

theorem coef_cnt {ι : Type} {m : ℕ} (F : (Fin m → ι) → ℝ)
    (hF : ∀ (f : Fin m → ι) (σ : Equiv.Perm (Fin m)), F (f ∘ σ) = F f) (f : Fin m → ι) :
    coef F (cnt f) = F f := by
  have h : ∃ g : Fin m → ι, cnt g = cnt f := ⟨f, rfl⟩
  obtain ⟨σ, hσ⟩ := exists_perm_of_cnt_eq h.choose_spec.symm
  rw [coef, dif_pos h, hσ, hF]

theorem coef_of_degree_ne {ι : Type} {m : ℕ} (F : (Fin m → ι) → ℝ) {k : ι →₀ ℕ}
    (hk : k.degree ≠ m) : coef F k = 0 := by
  refine dif_neg ?_
  rintro ⟨f, rfl⟩
  exact hk (degree_cnt f)

noncomputable def form {ι : Type} {m : ℕ} (F : (Fin m → ι) → ℝ) : MvPolynomial ι ℝ →ₗ[ℝ] ℝ :=
  (basisMonomials ι ℝ).constr ℝ (coef F)

theorem form_monomial {ι : Type} {m : ℕ} (F : (Fin m → ι) → ℝ) (k : ι →₀ ℕ) (a : ℝ) :
    form F (monomial k a) = a * coef F k := by
  have h1 : (monomial k a : MvPolynomial ι ℝ) = a • basisMonomials ι ℝ k := by
    simp [coe_basisMonomials, smul_monomial]
  rw [h1, map_smul, form, Module.Basis.constr_basis, smul_eq_mul]

theorem exists_form (ι : Type) [Fintype ι] (D : ℕ) (F : (Fin (D + 1) → ι) → ℝ)
    (hF : ∀ (f : Fin (D + 1) → ι) (σ : Equiv.Perm (Fin (D + 1))), F (f ∘ σ) = F f) :
    ∃ Φ : MvPolynomial ι ℝ →ₗ[ℝ] ℝ,
      (∀ n : ι → ℝ, Φ (GlobalTheory.ArInt.lin n ^ (D + 1)) = ∑ f : Fin (D + 1) → ι, (∏ j, n (f j)) * F f) ∧
      ∀ (P : MvPolynomial ι ℝ) (d : ℕ), d ≠ D + 1 → P.IsHomogeneous d → Φ P = 0 := by
  refine ⟨form F, fun n => ?_, fun P d hd hP => ?_⟩
  · rw [lin_pow, map_sum]
    exact Finset.sum_congr rfl fun f _ => by rw [form_monomial, coef_cnt F hF]
  · rw [P.as_sum, map_sum]
    refine Finset.sum_eq_zero fun k hk => ?_
    have hdeg : k.degree = d := by
      have := hP (mem_support_iff.1 hk)
      rw [Finsupp.degree_eq_weight_one]; exact this
    rw [form_monomial, coef_of_degree_ne F (by rw [hdeg]; exact hd), mul_zero]

end GlobalTheory.CompanionTheory.Polarisation
