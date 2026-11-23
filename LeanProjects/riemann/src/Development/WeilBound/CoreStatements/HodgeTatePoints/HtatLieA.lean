import Mathlib

noncomputable section

namespace PositivityTheory.HtPt.Htat.Lie

open TensorProduct

theorem bijective_of_cover {R M N J : Type} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (f : J → R) (hf : Ideal.span (Set.range f) = ⊤) (φ : M →ₗ[R] N)
    (h : ∀ i, ∃ (Q : Type) (_ : AddCommGroup Q) (_ : Module R Q) (a : N →ₗ[R] Q),
      IsLocalizedModule (Submonoid.powers (f i)) a ∧ IsLocalizedModule (Submonoid.powers (f i)) (a ∘ₗ φ)) :
    Function.Bijective φ := by
  constructor
  · rw [← LinearMap.ker_eq_bot, eq_bot_iff]
    intro m hm
    refine Submodule.mem_of_span_eq_top_of_smul_pow_mem _ _ hf m ?_
    rintro ⟨_, i, rfl⟩
    obtain ⟨Q, _, _, a, -, h2⟩ := h i
    have h0 : (a ∘ₗ φ) m = (a ∘ₗ φ) 0 := by
      rw [LinearMap.comp_apply, LinearMap.mem_ker.1 hm, map_zero, map_zero]
    obtain ⟨⟨_, k, rfl⟩, hk⟩ := IsLocalizedModule.exists_of_eq (S := Submonoid.powers (f i)) h0
    refine ⟨k, ?_⟩
    simpa [Submonoid.smul_def] using hk
  · intro n
    refine Submodule.mem_of_span_eq_top_of_smul_pow_mem (LinearMap.range φ) _ hf n ?_
    rintro ⟨_, i, rfl⟩
    obtain ⟨Q, _, _, a, h1, h2⟩ := h i
    obtain ⟨⟨m, ⟨_, k, rfl⟩⟩, hk⟩ := IsLocalizedModule.surj (Submonoid.powers (f i)) (a ∘ₗ φ) (a n)
    have h0 : a (f i ^ k • n) = a (φ m) := by
      rw [map_smul]
      exact hk
    obtain ⟨⟨_, l, rfl⟩, hl⟩ := IsLocalizedModule.exists_of_eq (S := Submonoid.powers (f i)) h0
    refine ⟨l + k, f i ^ l • m, ?_⟩
    have hl' : f i ^ l • f i ^ k • n = f i ^ l • φ m := hl
    show φ (f i ^ l • m) = f i ^ (l + k) • n
    rw [map_smul, pow_add, mul_smul, hl']

theorem isBaseChange_hom {R A C P : Type} [CommRing R] [CommRing A] [CommRing C] [Algebra R A] [Algebra R C]
    [Algebra A C] [IsScalarTower R A C] [AddCommGroup P] [Module R P] [Module A P] [IsScalarTower R A P]
    [Module.Finite A P] [Module.Projective A P]
    (hA : ∀ (φ : P →ₗ[R] A) (a : A) p, φ (a • p) = a * φ p)
    (hC : ∀ (φ : P →ₗ[R] C) (a : A) p, φ (a • p) = algebraMap A C a * φ p)
    (g : (P →ₗ[R] A) →ₗ[A] (P →ₗ[R] C)) (hg : ∀ φ p, g φ p = algebraMap A C (φ p)) : IsBaseChange C g := by
  obtain ⟨n, π, hπ⟩ := Module.Finite.exists_fin' A P
  obtain ⟨s, hs⟩ := Module.projective_lifting_property π LinearMap.id hπ
  let b : Fin n → P := fun k => π (fun j => if k = j then 1 else 0)
  have hexp : ∀ p : P, ∑ k, s p k • b k = p := by
    intro p
    have h1 := LinearMap.congr_fun hs p
    have h2 := LinearMap.pi_apply_eq_sum_univ π (s p)
    simp only [LinearMap.comp_apply, LinearMap.id_apply] at h1
    rw [h1] at h2
    exact h2.symm
  let co : Fin n → (P →ₗ[R] A) := fun k => (LinearMap.proj k ∘ₗ s).restrictScalars R
  have hco : ∀ k p, co k p = s p k := fun _ _ => rfl
  have hsum : ∀ φ : P →ₗ[R] A, ∑ k, φ (b k) • co k = φ := by
    intro φ
    ext p
    conv_rhs => rw [← hexp p]
    simp [map_sum, hA, hco, mul_comm]
  let θ : C ⊗[A] (P →ₗ[R] A) →ₗ[C] (P →ₗ[R] C) := g.liftBaseChange C
  have hθ : ∀ c φ, θ (c ⊗ₜ φ) = c • g φ := fun c φ => LinearMap.liftBaseChange_tmul _ _ _ _
  let inv : (P →ₗ[R] C) → C ⊗[A] (P →ₗ[R] A) := fun ψ => ∑ k, ψ (b k) ⊗ₜ co k
  have hl : ∀ z, inv (θ z) = z := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp [inv]
    | add x y hx hy =>
      have : inv (θ (x + y)) = inv (θ x) + inv (θ y) := by
        simp [inv, add_tmul, Finset.sum_add_distrib]
      rw [this, hx, hy]
    | tmul c φ =>
      rw [hθ]
      conv_rhs => rw [← hsum φ, tmul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [LinearMap.smul_apply, hg, tmul_smul, smul_tmul', Algebra.smul_def (φ (b k)), smul_eq_mul, mul_comm]
  have hr : ∀ ψ, θ (inv ψ) = ψ := by
    intro ψ
    ext p
    conv_rhs => rw [← hexp p]
    simp only [inv, map_sum, hθ, LinearMap.sum_apply, LinearMap.smul_apply, hg, hco, hC, smul_eq_mul, mul_comm]
  refine IsBaseChange.of_equiv (LinearEquiv.ofBijective θ
    ⟨Function.LeftInverse.injective hl, Function.RightInverse.surjective hr⟩) fun φ => ?_
  exact (hθ 1 φ).trans (one_smul _ _)

end PositivityTheory.HtPt.Htat.Lie
