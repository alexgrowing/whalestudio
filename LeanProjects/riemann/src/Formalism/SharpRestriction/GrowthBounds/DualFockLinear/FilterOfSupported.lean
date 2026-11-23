import Formalism.SharpRestriction.GrowthBounds.DualFockLinear.CloudBStepOfRho

noncomputable section

namespace Formalism.MainNotions.TestSideCounting

open Formalism.MainNotions.G Formalism.GradedWeylDivisibility MvPolynomial

section Slice

variable {K : Type} [Field K] {S τ : Type} [DecidableEq S] (A : Finset S)

def slice (γ : MvPolynomial (S × τ) K →ₗ[K] K) : MvPolynomial (S × τ) K →ₗ[K] MvPolynomial (S × τ) K :=
  (MvPolynomial.basisMonomials (S × τ) K).constr K
    (fun e => γ (monomial (e.filter fun v : S × τ => v.1 ∉ A) 1) • monomial (e.filter fun v : S × τ => v.1 ∈ A) 1)

theorem slice_monomial (γ : MvPolynomial (S × τ) K →ₗ[K] K) (e : S × τ →₀ ℕ) (a : K) :
    slice A γ (monomial e a) =
      (a * γ (monomial (e.filter fun v : S × τ => v.1 ∉ A) 1)) • monomial (e.filter fun v : S × τ => v.1 ∈ A) 1 := by
  have h : (monomial e a : MvPolynomial (S × τ) K) = a • MvPolynomial.basisMonomials (S × τ) K e := by
    simp only [MvPolynomial.coe_basisMonomials, smul_monomial, smul_eq_mul, mul_one]
  rw [h, map_smul]
  simp only [slice, Module.Basis.constr_basis, smul_smul]

theorem filter_of_supported {P : MvPolynomial (S × τ) K} {q : S × τ → Prop} [DecidablePred q]
    (hP : P ∈ supported K {v | q v}) {e : S × τ →₀ ℕ} (he : e ∈ P.support) :
    e.filter q = e ∧ e.filter (fun v => ¬ q v) = 0 := by
  rw [mem_supported] at hP
  have key : ∀ v, e v ≠ 0 → q v := fun v hv =>
    hP (Finset.mem_coe.2 ((mem_vars v).2 ⟨e, he, Finsupp.mem_support_iff.2 hv⟩))
  refine ⟨(Finsupp.filter_eq_self_iff _ _).2 key, (Finsupp.filter_eq_zero_iff _ _).2 fun v hv => ?_⟩
  by_contra h
  exact hv (key v h)

theorem slice_mul_left (γ : MvPolynomial (S × τ) K →ₗ[K] K) (P R : MvPolynomial (S × τ) K)
    (hP : P ∈ supported K {v : S × τ | v.1 ∈ A}) : slice A γ (P * R) = P * slice A γ R := by
  induction R using MvPolynomial.induction_on' with
  | monomial f b =>
    conv_lhs => rw [P.as_sum]
    conv_rhs => rw [P.as_sum]
    rw [Finset.sum_mul, Finset.sum_mul, map_sum]
    refine Finset.sum_congr rfl fun e he => ?_
    have h := filter_of_supported (q := fun v : S × τ => v.1 ∈ A) hP he
    beta_reduce at h
    rw [monomial_mul, slice_monomial, slice_monomial, Finsupp.filter_add, Finsupp.filter_add, h.1, h.2,
      zero_add, mul_smul_comm, monomial_mul, smul_monomial, smul_monomial, smul_eq_mul, smul_eq_mul]
    congr 1
    ring
  | add p q hp hq => rw [mul_add, map_add, hp, hq, map_add, mul_add]

theorem slice_spec (γ : MvPolynomial (S × τ) K →ₗ[K] K) (Q : MvPolynomial (S × τ) K)
    (hQ : Q ∈ supported K {v : S × τ | v.1 ∉ A}) : slice A γ Q = γ Q • 1 := by
  conv_lhs => rw [Q.as_sum]
  conv_rhs => rw [Q.as_sum]
  rw [map_sum, map_sum, Finset.sum_smul]
  refine Finset.sum_congr rfl fun e he => ?_
  have h := filter_of_supported (q := fun v : S × τ => v.1 ∉ A) hQ he
  beta_reduce at h
  have h2 : e.filter (fun v : S × τ => v.1 ∈ A) = 0 := by
    rw [Finsupp.filter_eq_zero_iff]
    intro v hv
    exact (Finsupp.filter_eq_zero_iff _ _).1 h.2 v (not_not.2 hv)
  have h3 : (monomial e (coeff e Q) : MvPolynomial (S × τ) K) = coeff e Q • monomial e 1 := by
    rw [smul_monomial, smul_eq_mul, mul_one]
  rw [slice_monomial, h.1, h2, ← C_apply, C_1, h3, map_smul, smul_eq_mul]

theorem slice_mul (γ : MvPolynomial (S × τ) K →ₗ[K] K) (P Q : MvPolynomial (S × τ) K)
    (hP : P ∈ supported K {v : S × τ | v.1 ∈ A}) (hQ : Q ∈ supported K {v : S × τ | v.1 ∉ A}) :
    slice A γ (P * Q) = γ Q • P := by
  rw [slice_mul_left A γ P Q hP, slice_spec A γ Q hQ, mul_smul_comm, mul_one]

end Slice

section Tensor

variable {R K : Type} [CommRing R] [Field K] [Algebra R K] {S : Type} [Fintype S] [DecidableEq S] {k n : ℕ}

theorem blockEmb_supported (s : S) (F : MvPolynomial (Fin k × Fin n) K) (q : S → Prop) (hs : q s) :
    blockEmb K s F ∈ supported K {v : S × (Fin k × Fin n) | q v.1} := by
  rw [mem_supported]
  intro v hv
  have hv' := vars_rename (fun w : Fin k × Fin n => (s, w)) F (Finset.mem_coe.1 hv)
  obtain ⟨w, -, rfl⟩ := Finset.mem_image.1 hv'
  exact hs

theorem prod_split (A : Finset S) (F : S → MvPolynomial (Fin k × Fin n) K) :
    ∏ s, blockEmb K s (F s) =
      (∏ s, blockEmb K s (if s ∈ A then F s else 1)) * ∏ s, blockEmb K s (if s ∈ A then 1 else F s) := by
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun s _ => ?_
  split_ifs <;> simp

theorem slice_tensor (A : Finset S) (M MT Msp : S → Submodule R (MvPolynomial (Fin k × Fin n) K))
    (h1 : ∀ s ∈ A, M s ≤ MT s ∧ (1 : MvPolynomial (Fin k × Fin n) K) ∈ Msp s)
    (h2 : ∀ s, s ∉ A → (1 : MvPolynomial (Fin k × Fin n) K) ∈ MT s ∧ M s ≤ Msp s)
    (γ : MvPolynomial (S × (Fin k × Fin n)) K →ₗ[K] K) (c : K)
    (hγ : ∀ Q ∈ tensorLat R K Msp, ∃ a : R, γ Q = c * algebraMap R K a) :
    ∀ u ∈ tensorLat R K M, ∃ y ∈ tensorLat R K MT, slice A γ u = c • y := by
  intro u hu
  unfold tensorLat at hu
  induction hu using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨F, hF, rfl⟩ := hx
    have hXs : (∏ s, blockEmb K s (if s ∈ A then F s else 1)) ∈
        supported K {v : S × (Fin k × Fin n) | v.1 ∈ A} := by
      refine Subalgebra.prod_mem _ fun s _ => ?_
      split_ifs with h
      · exact blockEmb_supported s _ (· ∈ A) h
      · rw [map_one]; exact one_mem _
    have hYs : (∏ s, blockEmb K s (if s ∈ A then 1 else F s)) ∈
        supported K {v : S × (Fin k × Fin n) | v.1 ∉ A} := by
      refine Subalgebra.prod_mem _ fun s _ => ?_
      split_ifs with h
      · rw [map_one]; exact one_mem _
      · exact blockEmb_supported s _ (· ∉ A) h
    have hYm : (∏ s, blockEmb K s (if s ∈ A then 1 else F s)) ∈ tensorLat R K Msp := by
      unfold tensorLat
      refine Submodule.subset_span ⟨_, fun s => ?_, rfl⟩
      split_ifs with h
      · exact (h1 s h).2
      · exact (h2 s h).2 (hF s)
    obtain ⟨a, ha⟩ := hγ _ hYm
    refine ⟨a • ∏ s, blockEmb K s (if s ∈ A then F s else 1), Submodule.smul_mem _ a ?_, ?_⟩
    · unfold tensorLat
      refine Submodule.subset_span ⟨_, fun s => ?_, rfl⟩
      split_ifs with h
      · exact (h1 s h).1 (hF s)
      · exact (h2 s h).1
    · rw [prod_split A F, slice_mul A γ _ _ hXs hYs, ha, mul_smul, algebraMap_smul]
  | zero => exact ⟨0, zero_mem _, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨a, ha, ea⟩ := hx
    obtain ⟨b, hb, eb⟩ := hy
    exact ⟨a + b, add_mem ha hb, by rw [map_add, ea, eb, smul_add]⟩
  | smul r x _ hx =>
    obtain ⟨a, ha, ea⟩ := hx
    exact ⟨r • a, Submodule.smul_mem _ r ha, by rw [LinearMap.map_smul_of_tower, ea, smul_comm]⟩

end Tensor

end Formalism.MainNotions.TestSideCounting
