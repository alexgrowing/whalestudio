import Mathlib

namespace GlobalTheory

theorem trace_eq_zero_of_coord_move {X W : Type} [Fintype X] [DecidableEq X] [AddCommGroup W]
    [Module ℂ W] [FiniteDimensional ℂ W] (π : X → X) (hπ : ∀ c, π c ≠ c)
    (φ : X → Module.End ℂ W) (M : Module.End ℂ (X → W)) (hM : ∀ f c, M f c = φ c (f (π c))) :
    LinearMap.trace ℂ (X → W) M = 0 := by
  classical

  let b := Pi.basis (fun _ : X => Module.finBasis ℂ W)
  rw [LinearMap.trace_eq_matrix_trace ℂ b, Matrix.trace]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [Matrix.diag_apply, LinearMap.toMatrix_apply, Pi.basis_repr, Pi.basis_apply, hM,
    Pi.single_eq_of_ne (hπ i.1), map_zero, map_zero, Finsupp.zero_apply]

theorem finrank_eq_card_mul_and_trace_eq_zero_of_free_values :
    ∀ (Y X B W : Type) [Finite X] [AddCommGroup B] [Module ℂ B] [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W] (cls : Y → X) (ev : Y → (B →ₗ[ℂ] W)) (S : Submodule ℂ B), Function.Surjective cls → (∀ T : B, (∀ h, ev h T = 0) → T = 0) → (∀ h h', cls h = cls h' → ∃ φ : Module.End ℂ W, ∀ T ∈ S, ev h' T = φ (ev h T)) → (∀ h (ℓ : W), ∃ T ∈ S, ev h T = ℓ ∧ ∀ h', cls h' ≠ cls h → ev h' T = 0) → FiniteDimensional ℂ S ∧ Module.finrank ℂ S = Nat.card X * Module.finrank ℂ W ∧ ∀ (H : Type) [AddCommGroup H] [Module ℂ H] (e : H →ₗ[ℂ] B), Function.Injective e → LinearMap.range e = S → ∀ (A : Module.End ℂ H) (t : Y → Y), (∀ x h, ev h (e (A x)) = ev (t h) (e x)) → (∀ h, cls (t h) ≠ cls h) → LinearMap.trace ℂ H A = 0 := by
  intro Y X B W _ _ _ _ _ _ cls ev S hcls hinj hcls_eq hfree
  classical
  haveI : Fintype X := Fintype.ofFinite X

  obtain ⟨s, hs⟩ : ∃ s : X → Y, ∀ x, cls (s x) = x :=
    ⟨fun x => (hcls x).choose, fun x => (hcls x).choose_spec⟩

  let Φ : S →ₗ[ℂ] (X → W) := LinearMap.pi (fun x => (ev (s x)).comp S.subtype)
  have hΦ : ∀ (T : S) x, Φ T x = ev (s x) T := fun _ _ => rfl
  have hzero : ∀ T ∈ S, (∀ x, ev (s x) T = 0) → T = 0 := by
    intro T hT h0
    apply hinj
    intro h
    obtain ⟨φ, hφ⟩ := hcls_eq (s (cls h)) h (hs _)
    rw [hφ T hT, h0, map_zero]
  have hΦinj : Function.Injective Φ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro T hT
    refine Subtype.ext (hzero T T.2 (fun x => ?_))
    have hx := congrFun hT x
    rw [hΦ] at hx
    exact hx
  have hΦsurj : Function.Surjective Φ := by
    intro g
    choose T hTS hTg hT0 using fun x => hfree (s x) (g x)
    refine ⟨⟨∑ x, T x, Submodule.sum_mem _ (fun x _ => hTS x)⟩, ?_⟩
    funext y
    show ev (s y) (∑ x, T x) = g y
    rw [map_sum, Finset.sum_eq_single y]
    · exact hTg y
    · intro x _ hxy
      apply hT0
      rw [hs, hs]
      exact Ne.symm hxy
    · intro h
      exact absurd (Finset.mem_univ y) h
  let Ψ : S ≃ₗ[ℂ] (X → W) := LinearEquiv.ofBijective Φ ⟨hΦinj, hΦsurj⟩
  have hfd : FiniteDimensional ℂ S := LinearEquiv.finiteDimensional Ψ.symm
  refine ⟨hfd, ?_, ?_⟩
  · rw [Ψ.finrank_eq, Module.finrank_pi_fintype, Finset.sum_const, Finset.card_univ, smul_eq_mul,
      Nat.card_eq_fintype_card]
  · intro H _ _ e he hrange A t hA ht

    let eS : H ≃ₗ[ℂ] S := (LinearEquiv.ofInjective e he).trans (LinearEquiv.ofEq _ _ hrange)
    let Θ : H ≃ₗ[ℂ] (X → W) := eS.trans Ψ
    have hΘ : ∀ x c, Θ x c = ev (s c) (e x) := fun _ _ => rfl
    haveI : FiniteDimensional ℂ H := LinearEquiv.finiteDimensional Θ.symm
    rw [← LinearMap.trace_conj' A Θ]
    choose φ hφ using fun c => hcls_eq (s (cls (t (s c)))) (t (s c)) (hs _)
    refine trace_eq_zero_of_coord_move (fun c => cls (t (s c)))
      (fun c => by have h := ht (s c); rwa [hs] at h) φ _ ?_
    intro g c
    obtain ⟨x, rfl⟩ := Θ.surjective g
    rw [LinearEquiv.conj_apply_apply, LinearEquiv.symm_apply_apply, hΘ, hΘ, hA]
    have hmem : e x ∈ S := by
      rw [← hrange]
      exact LinearMap.mem_range_self e x
    exact hφ c (e x) hmem

end GlobalTheory
