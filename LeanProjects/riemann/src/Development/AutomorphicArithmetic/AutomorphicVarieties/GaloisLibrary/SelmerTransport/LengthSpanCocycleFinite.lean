import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.RestrictionMemInvariantH1
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.LenCokerLe

open ReciprocityTheory.Gal UpperTheory.V.Base

private theorem UpperTheory.V.Base.length_span_cocycle_finite {R N I : Type} [CommRing R] [AddCommGroup N] [Module R N] [Finite I]
    (hN : ∀ m : N, Module.length R (Submodule.span R {m}) ≠ ⊤) (Z : Submodule R (I → N)) (f : Z) :
    Module.length R (Submodule.span R {f}) ≠ ⊤ := by
  classical
  have := Fintype.ofFinite I
  let φ : Submodule.span R {f} →ₗ[R] (Π i : I, Submodule.span R {(f : I → N) i}) :=
    { toFun := fun g i => ⟨((g : Z) : I → N) i, by
        obtain ⟨r, hr⟩ := Submodule.mem_span_singleton.mp g.2
        rw [← hr]
        exact Submodule.mem_span_singleton.mpr ⟨r, by simp⟩⟩
      map_add' := fun g h => by ext i; simp
      map_smul' := fun r g => by ext i; simp }
  have hφ : Function.Injective φ := by
    intro g h e
    apply Subtype.ext
    apply Subtype.ext
    funext i
    exact congrArg Subtype.val (congrFun e i)
  refine ne_top_of_le_ne_top ?_ (Module.length_le_of_injective φ hφ)
  rw [Module.length_pi_of_fintype]
  exact (WithTop.sum_lt_top.mpr fun i _ => (hN _).lt_top).ne

theorem UpperTheory.V.Base.h2Ab :
    ∀ (R Q N : Type) [CommRing R] [TopologicalSpace Q] [DiscreteTopology Q] [Finite Q] [AddCommGroup N] [Module R N]
      [TopologicalSpace N] [IsTopologicalAddGroup N] [ContinuousConstSMul R N] [DiscreteTopology N] [IsPrincipalIdealRing R] [Group Q] (σ : Representation R Q N), (∀ a b : Q, a * b = b * a) → (∀ m : N, Module.length R (Submodule.span R {m}) ≠ ⊤) →
      (∀ g, ∃ c : R, ∀ m, σ g m = c • m) → Module.length R (H2 σ) ≤ (Nat.card Q : ℕ∞) ^ 2 * Module.length R (H0 σ) := by
  intro R Q N _ _ _ _ _ _ _ _ _ _ _ _ σ hcomm hN hsc
  classical
  choose c hc using hsc
  set J : Ideal R := Ideal.span (Set.range fun g => c g - 1) with hJ
  set a : R := Submodule.IsPrincipal.generator J with ha
  have haJ : a ∈ J := Submodule.IsPrincipal.generator_mem J
  have hJa : ∀ g, ∃ r : R, c g - 1 = r * a := by
    intro g
    have hmem : c g - 1 ∈ J := Ideal.subset_span ⟨g, rfl⟩
    rw [← Ideal.span_singleton_generator J] at hmem
    obtain ⟨r, hr⟩ := Ideal.mem_span_singleton'.mp hmem
    exact ⟨r, hr.symm⟩
  have hH0 : ∀ m : N, a • m = 0 → m ∈ H0 σ := by
    intro m hm
    rw [H0, Representation.mem_invariants]
    intro g
    obtain ⟨r, hr⟩ := hJa g
    have hz : (c g - 1) • m = 0 := by rw [hr, mul_smul, hm, smul_zero]
    rw [hc, ← sub_eq_zero, ← hz, sub_smul, one_smul]
  have hB : ∀ f : Z2 σ, a • (f : Q × Q → N) ∈ B2 σ := by
    intro f
    set F : Q × Q → N := (f : Q × Q → N) with hF
    obtain ⟨-, hcoc⟩ := f.2
    refine Submodule.span_induction (p := fun x _ => x • F ∈ B2 σ) ?_ ?_ ?_ ?_ haJ
    · rintro _ ⟨g, rfl⟩
      rw [separated_dvr_second_cohomology_mem]
      refine ⟨fun x => F (g, x) - F (x, g), continuous_of_discreteTopology, ?_⟩
      funext ⟨x, y⟩
      have e1 := hcoc g x y
      have e2 := hcoc x g y
      have e3 := hcoc x y g
      rw [hc] at e1 e2 e3
      rw [hcomm x g] at e2
      rw [hcomm y g] at e3
      simp only [d1_apply, hc, Pi.smul_apply]
      have key : c x • (F (g, y) - F (y, g)) - (F (g, x * y) - F (x * y, g)) + (F (g, x) - F (x, g))
            - (c g - 1) • F (x, y)
          = -((c g • F (x, y) - F (g * x, y) + F (g, x * y) - F (g, x))
            - (c x • F (g, y) - F (g * x, y) + F (x, g * y) - F (x, g))
            + (c x • F (y, g) - F (x * y, g) + F (x, g * y) - F (x, y))) := by
        simp only [smul_sub, sub_smul, one_smul]
        abel
      rw [e1, e2, e3] at key
      simpa [sub_eq_zero] using key
    · rw [zero_smul]
      exact zero_mem _
    · intro x y _ _ hx hy
      rw [add_smul]
      exact add_mem hx hy
    · intro r x _ hx
      rw [smul_eq_mul, mul_smul]
      exact Submodule.smul_mem _ r hx
  let Zs := Z2 σ
  let mul : Zs →ₗ[R] Zs := a • LinearMap.id
  have h1 : Module.length R (H2 σ) ≤ Module.length R (Zs ⧸ LinearMap.range mul) := by
    let q := Submodule.liftQ (LinearMap.range mul) (Submodule.mkQ (Submodule.comap Zs.subtype (B2 σ))) (by
      rintro _ ⟨z, rfl⟩
      rw [LinearMap.mem_ker, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, Submodule.mem_comap]
      exact hB z)
    refine Module.length_le_of_surjective q ?_
    intro y
    obtain ⟨z, rfl⟩ := Submodule.mkQ_surjective _ y
    exact ⟨Submodule.mkQ _ z, rfl⟩
  have h2 := lenCokerLe R Zs (UpperTheory.V.Base.length_span_cocycle_finite hN Zs) a
  have h3 : Module.length R (LinearMap.ker mul) ≤ Module.length R (Q × Q → H0 σ) := by
    let φ : LinearMap.ker mul →ₗ[R] (Q × Q → H0 σ) :=
      { toFun := fun z p => ⟨((z : Zs) : Q × Q → N) p, hH0 _ (by
            have hz : mul (z : Zs) = 0 := LinearMap.mem_ker.mp z.2
            exact congrFun (congrArg Subtype.val hz) p)⟩
        map_add' := fun _ _ => by ext; simp
        map_smul' := fun _ _ => by ext; simp }
    refine Module.length_le_of_injective φ ?_
    intro z w e
    apply Subtype.ext
    apply Subtype.ext
    funext p
    have hp := congrArg Subtype.val (congrFun e p)
    exact hp
  calc Module.length R (H2 σ) ≤ _ := h1
    _ ≤ _ := h2
    _ ≤ _ := h3
    _ = (Nat.card Q : ℕ∞) ^ 2 * Module.length R (H0 σ) := by
      rw [Module.length_pi]
      congr 1
      rw [ENat.card_eq_coe_natCard, Nat.card_prod, pow_two]
      push_cast
      rfl
