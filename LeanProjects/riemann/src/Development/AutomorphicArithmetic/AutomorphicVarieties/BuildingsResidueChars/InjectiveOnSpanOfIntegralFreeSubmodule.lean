import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.FnIndep

open UpperTheory.V.Hi

theorem UpperTheory.injective_on_span_of_integral_free_submodule :
    ∀ (O Ω V α : Type) [CommRing O] [IsDomain O] [Field Ω] [Algebra O Ω] [AddCommGroup V] [Module Ω V] [Module O V] [IsScalarTower O Ω V] (m : ℕ) (ψ : V →ₗ[Ω] (α → Fin m → Ω)) (S : Submodule O V), Function.Injective (algebraMap O Ω) → Module.Free O S → (∀ F ∈ S, ∀ g i, ψ F g i ∈ (algebraMap O Ω).range) → (∀ F ∈ S, ψ F = 0 → F = 0) → ∀ F ∈ Submodule.span Ω (S : Set V), ψ F = 0 → F = 0 := by
  intro O Ω V α _ _ _ _ _ _ _ _ m ψ S hinj hfree hrange hker F hF hψF
  classical
  haveI := hfree
  let b := Module.Free.chooseBasis O S
  have hex : ∀ i g j, ∃ r : O, algebraMap O Ω r = ψ (b i : V) g j := fun i g j =>
    RingHom.mem_range.1 (hrange _ (b i).2 g j)
  choose v hv using hex
  have hvli : LinearIndependent O v := by
    rw [linearIndependent_iff']
    intro s c hsum i hi
    have hx : ψ ((∑ k ∈ s, c k • b k : S) : V) = 0 := by
      funext g j
      have h0 := congrFun (congrFun hsum g) j
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at h0
      simp only [Submodule.coe_sum, Submodule.coe_smul, map_sum, Finset.sum_apply, Pi.zero_apply]
      calc ∑ k ∈ s, ψ (c k • (b k : V)) g j = ∑ k ∈ s, algebraMap O Ω (c k * v k g j) := by
            refine Finset.sum_congr rfl fun k _ => ?_
            rw [← algebraMap_smul Ω (c k) (b k : V), map_smul, Pi.smul_apply, Pi.smul_apply,
              smul_eq_mul, map_mul, hv]
        _ = 0 := by rw [← map_sum, h0, map_zero]
    have hx0 : (∑ k ∈ s, c k • b k : S) = 0 := Subtype.ext (hker _ (Submodule.coe_mem _) hx)
    exact linearIndependent_iff'.1 b.linearIndependent s c hx0 i hi
  have hw : LinearIndependent Ω (fun i => ψ (b i : V)) := by
    have h1 := UpperTheory.V.Hi.fnIndep O Ω α _ hinj m v hvli
    convert h1 using 1
    funext i g j
    exact (hv i g j).symm
  have hS : Submodule.span O (Set.range (fun i => (b i : V))) = S := by
    have h2 : Set.range (fun i => (b i : V)) = S.subtype '' Set.range b := by
      rw [← Set.range_comp]
      rfl
    rw [h2, Submodule.span_image, b.span_eq, Submodule.map_top, Submodule.range_subtype]
  have hsub : (S : Set V) ⊆ Submodule.span Ω (Set.range (fun i => (b i : V))) := by
    intro x hx
    have hx' : x ∈ Submodule.span O (Set.range (fun i => (b i : V))) := by
      rw [hS]
      exact hx
    exact Submodule.span_le_restrictScalars O Ω _ hx'
  have hF' := Submodule.span_le.2 hsub hF
  obtain ⟨c, rfl⟩ := (Finsupp.mem_span_range_iff_exists_finsupp).1 hF'
  have hc : c = 0 := by
    refine linearIndependent_iff.1 hw c ?_
    rw [Finsupp.linearCombination_apply]
    simpa only [Finsupp.sum, map_sum, map_smul] using hψF
  rw [hc, Finsupp.sum_zero_index]
