import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.L2Cusps.AbsCompactAlt

open GroundTheory.Automorphic

private theorem UpperTheory.V.KernelIndexFullLattice.orbit_finite {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {V : Type*} [AddCommGroup V] [Module ℂ V] (τ : Representation ℂ G V) (v : V)
    (hv : IsOpen {g : G | τ g v = v}) (U : Set G) (hU : IsCompact U) :
    ((fun g => τ g v) '' U).Finite := by
  classical
  obtain ⟨t, ht⟩ := hU.elim_finite_subcover
    (fun g : G => (fun x : G => g⁻¹ * x) ⁻¹' {h : G | τ h v = v})
    (fun g => hv.preimage (continuous_const.mul continuous_id))
    (fun x _ => Set.mem_iUnion.2 ⟨x, by simp⟩)
  refine (t.finite_toSet.image (fun g => τ g v)).subset ?_
  rintro _ ⟨x, hx, rfl⟩
  obtain ⟨g, hg, hxg⟩ := Set.mem_iUnion₂.1 (ht hx)
  have hs : τ (g⁻¹ * x) v = v := hxg
  refine ⟨g, hg, ?_⟩
  have e : x = g * (g⁻¹ * x) := by group
  show τ g v = τ x v
  rw [e, map_mul, Module.End.mul_apply, hs]

private theorem UpperTheory.V.KernelIndexFullLattice.mul_two_dim_algebra_stable {C G : Type*} [Group C] [Group G]
    {V : Type*} [AddCommGroup V] [Module ℂ V] (σ : Representation ℂ C V) (τ : Representation ℂ G V)
    (hσ : ∀ v : V, FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k : C => σ k v)))
    (hc : ∀ k g, σ k * τ g = τ g * σ k) (U : Subgroup G) (v : V)
    (hf : ((fun g => τ g v) '' (U : Set G)).Finite) :
    ∃ Y : Submodule ℂ V, FiniteDimensional ℂ Y ∧ v ∈ Y ∧ (∀ k, ∀ y ∈ Y, σ k y ∈ Y) ∧
      ∀ u ∈ U, ∀ y ∈ Y, τ u y ∈ Y := by
  classical
  let Y : Submodule ℂ V := hf.toFinset.sup (fun w => Submodule.span ℂ (Set.range fun k : C => σ k w))
  have mem : ∀ w ∈ (fun g => τ g v) '' (U : Set G), ∀ k, σ k w ∈ Y := by
    intro w hw k
    exact Finset.le_sup (f := fun w => Submodule.span ℂ (Set.range fun k : C => σ k w))
      (hf.mem_toFinset.2 hw) (Submodule.subset_span ⟨k, rfl⟩)
  have stab : ∀ φ : Module.End ℂ V,
      (∀ w ∈ (fun g => τ g v) '' (U : Set G), ∀ k, φ (σ k w) ∈ Y) → ∀ y ∈ Y, φ y ∈ Y := by
    intro φ hφ y hy
    have hle : Y ≤ Y.comap φ := by
      refine Finset.sup_le fun w hw => ?_
      rw [Submodule.span_le]
      rintro _ ⟨k, rfl⟩
      exact hφ w (hf.mem_toFinset.1 hw) k
    exact hle hy
  refine ⟨Y, ?_, ?_, ?_, ?_⟩
  · refine Finset.sup_induction (p := fun N : Submodule ℂ V => FiniteDimensional ℂ N) ?_ ?_ ?_
    · exact inferInstance
    · intro a ha b hb
      exact Submodule.finiteDimensional_sup a b
    · intro w _
      exact hσ w
  · have h1 := mem v ⟨1, U.one_mem, by simp⟩ 1
    simpa using h1
  · intro k
    refine stab (σ k) ?_
    intro w hw k'
    rw [← Module.End.mul_apply, ← map_mul]
    exact mem w hw _
  · intro u hu
    refine stab (τ u) ?_
    rintro _ ⟨g, hg, rfl⟩ k
    have e : τ u (σ k (τ g v)) = σ k (τ (u * g) v) := by
      rw [map_mul, Module.End.mul_apply, ← Module.End.mul_apply (τ u) (σ k), ← hc k u,
        Module.End.mul_apply]
    rw [e]
    exact mem _ ⟨u * g, U.mul_mem hu hg, rfl⟩ k

theorem UpperTheory.V.KernelIndexFullLattice.stabFin_holds :
    UpperTheory.V.KernelIndexFullLattice.StabFin := by
  intro K _ _ n V _ _ M hM U hU v
  exact UpperTheory.V.KernelIndexFullLattice.mul_two_dim_algebra_stable M.gk.σ M.τ M.gk.locallyFinite M.comm_σ U v
    (UpperTheory.V.KernelIndexFullLattice.orbit_finite M.τ v (hM v) _ hU)
