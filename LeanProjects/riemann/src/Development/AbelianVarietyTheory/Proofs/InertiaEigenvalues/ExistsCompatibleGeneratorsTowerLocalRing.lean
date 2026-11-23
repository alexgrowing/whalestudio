import Mathlib

open scoped TensorProduct

namespace GlobalTheory

private theorem tower_minimal_presentation (Λ : Type) [CommRing Λ] [IsLocalRing Λ] (A : Type)
    [AddCommGroup A] [Module Λ A] [Module.Finite Λ A] :
    ∃ (d : ℕ) (p : (Fin d → Λ) →ₗ[Λ] A), Function.Surjective p ∧
      ∀ x, p x = 0 → ∀ i, x i ∈ IsLocalRing.maximalIdeal Λ := by
  classical
  let k := IsLocalRing.ResidueField Λ
  let b := Module.finBasis k (k ⊗[Λ] A)
  have hs : Function.Surjective (TensorProduct.mk Λ k A 1) :=
    TensorProduct.mk_surjective Λ A k IsLocalRing.residue_surjective
  choose v hv using fun i => hs (b i)
  have hv' : ∀ i, (1 : k) ⊗ₜ[Λ] v i = b i := hv
  have hspan : Submodule.span Λ (Set.range v) = ⊤ :=
    IsLocalRing.span_eq_top_of_tmul_eq_basis v b hv'
  refine ⟨_, Fintype.linearCombination Λ v, ?_, ?_⟩
  · rw [← LinearMap.range_eq_top, Fintype.range_linearCombination, hspan]
  · intro x hx i
    have h1 : ∑ j, algebraMap Λ k (x j) • b j = 0 := by
      have h2 := congrArg (TensorProduct.mk Λ k A 1) hx
      rw [Fintype.linearCombination_apply, map_sum, map_zero] at h2
      rw [← h2]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [map_smul, hv, algebraMap_smul]
    have h3 := Fintype.linearIndependent_iff.1 b.linearIndependent _ h1 i
    exact (IsLocalRing.residue_eq_zero_iff _).1 h3

theorem exists_surjective_lift_of_ker_le_maximalIdeal_smul {Λ : Type} [CommRing Λ] [IsLocalRing Λ]
    {A B : Type} [AddCommGroup A] [Module Λ A] [Module.Finite Λ A] [AddCommGroup B] [Module Λ B]
    (t : A →ₗ[Λ] B) (ht : Function.Surjective t)
    (hk : LinearMap.ker t ≤ IsLocalRing.maximalIdeal Λ • (⊤ : Submodule Λ A))
    {a : ℕ} (p : (Fin a → Λ) →ₗ[Λ] B) (hp : Function.Surjective p) :
    ∃ q : (Fin a → Λ) →ₗ[Λ] A, Function.Surjective q ∧ t ∘ₗ q = p := by
  obtain ⟨q, hq⟩ := Module.projective_lifting_property t p ht
  refine ⟨q, ?_, hq⟩
  rw [← LinearMap.range_eq_top, eq_top_iff]
  refine Submodule.le_of_le_smul_of_le_jacobson_bot (I := IsLocalRing.maximalIdeal Λ)
    Module.Finite.fg_top (IsLocalRing.maximalIdeal_le_jacobson _) fun y _ => ?_
  obtain ⟨x, hx⟩ := hp (t y)
  have h1 : y - q x ∈ LinearMap.ker t := by
    rw [LinearMap.mem_ker, map_sub, ← hx, ← hq, LinearMap.comp_apply, sub_self]
  have h2 : y = q x + (y - q x) := by abel
  rw [h2]
  exact Submodule.add_mem_sup (LinearMap.mem_range_self q x) (hk h1)

theorem exists_compatible_generators_tower :
    ∀ (Λ : Type) [CommRing Λ] [IsLocalRing Λ] (M : ℕ → Type) [∀ n, AddCommGroup (M n)] [∀ n, Module Λ (M n)] [∀ n, Module.Finite Λ (M n)]
  (t : ∀ n, M (n + 1) →ₗ[Λ] M n), (∀ n, Function.Surjective (t n)) →
  (∀ n, LinearMap.ker (t n) ≤ IsLocalRing.maximalIdeal Λ • (⊤ : Submodule Λ (M (n + 1)))) →
  ∃ (a : ℕ) (p : ∀ n, (Fin a → Λ) →ₗ[Λ] M n), (∀ n, Function.Surjective (p n)) ∧ (∀ n, (t n) ∘ₗ (p (n + 1)) = p n) ∧
    ∀ x, p 0 x = 0 → ∀ i, x i ∈ IsLocalRing.maximalIdeal Λ := by
  intro Λ _ _ M _ _ _ t ht hk
  obtain ⟨a, p0, hp0, hmin⟩ := tower_minimal_presentation Λ (M 0)
  choose q hq hq' using fun (n : ℕ) (p : (Fin a → Λ) →ₗ[Λ] M n) (hp : Function.Surjective p) =>
    exists_surjective_lift_of_ker_le_maximalIdeal_smul (t n) (ht n) (hk n) p hp
  let P : ∀ n, {p : (Fin a → Λ) →ₗ[Λ] M n // Function.Surjective p} := fun n =>
    Nat.rec (motive := fun n => {p : (Fin a → Λ) →ₗ[Λ] M n // Function.Surjective p})
      ⟨p0, hp0⟩ (fun n p => ⟨q n p.1 p.2, hq n p.1 p.2⟩) n
  exact ⟨a, fun n => (P n).1, fun n => (P n).2, fun n => hq' n (P n).1 (P n).2, hmin⟩

end GlobalTheory
