import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.DualModuleCocycles.RepRSingle
open Matrix IsLocalRing UpperTheory.V UpperTheory.V.W UpperTheory.V.Alg UpperTheory.V.Pa UpperTheory.V.Th UpperTheory.V.Th.Coc

private theorem x_loc {O R : Type} [CommRing O] [IsLocalRing O] [CommRing R] [IsLocalRing R] [Algebra O R]
    (x : R →ₐ[O] O) (y : R) (hy : y ∈ maximalIdeal R) : x y ∈ maximalIdeal O := by
  intro hu
  have h2 : IsUnit (y - algebraMap O R (x y)) := by
    by_contra hn
    have h3 : y - algebraMap O R (x y) ∈ maximalIdeal R := hn
    have h4 : algebraMap O R (x y) ∈ maximalIdeal R := by simpa using Ideal.sub_mem _ hy h3
    exact h4 (hu.map _)
  have h5 := h2.map x
  rw [map_sub, AlgHom.commutes] at h5
  simp at h5

private theorem der_pow {O R X : Type} [CommRing O] [IsLocalRing O] [CommRing R] [IsLocalRing R] [Algebra O R]
    [AddCommGroup X] [Module O X] (x : R →ₐ[O] O) (δ : R →ₗ[O] X) (h : IsDer x δ) (k : ℕ) :
    ∀ a ∈ maximalIdeal R ^ (k + 1), x a ∈ maximalIdeal O ^ (k + 1) ∧
      δ a ∈ (maximalIdeal O ^ k • ⊤ : Submodule O X) := by
  induction k with
  | zero =>
    intro a ha
    rw [zero_add, pow_one] at ha
    refine ⟨by simpa using x_loc x a ha, by simp⟩
  | succ k ih =>
    intro a ha
    rw [pow_succ] at ha
    refine Submodule.mul_induction_on ha (fun b hb c hc => ?_) (fun b c hb hc => ?_)
    · obtain ⟨h1, h2⟩ := ih b hb
      have h3 := x_loc x c hc
      refine ⟨?_, ?_⟩
      · rw [map_mul, pow_succ _ (k + 1)]
        exact Ideal.mul_mem_mul h1 h3
      · rw [h b c]
        refine Submodule.add_mem _ (Submodule.smul_mem_smul h1 Submodule.mem_top) ?_
        rw [pow_succ', Submodule.mul_smul]
        exact Submodule.smul_mem_smul h3 h2
    · rw [map_add, map_add]
      exact ⟨Ideal.add_mem _ hb.1 hc.1, Submodule.add_mem _ hb.2 hc.2⟩

theorem UpperTheory.V.Th.Coc.lcDer :
    ∀ {O R Γ : Type} [CommRing O] [IsLocalRing O] [CommRing R] [Algebra O R] [IsCO O R] [TopologicalSpace Γ] (m : ℕ), (∀ f : Γ → O, AdicCont (maximalIdeal O) f → IsLocallyConstant fun g => Ideal.Quotient.mk (maximalIdeal O ^ m) (f g)) ∧ ∀ (x : R →ₐ[O] O) (δ : R →ₗ[O] Om O m), IsDer x δ → ∀ f : Γ → R, AdicCont (maximalIdeal R) f → IsLocallyConstant fun g => δ (f g) := by
  intro O R Γ _ _ _ _ _ _ m
  refine ⟨fun f hf => hf m, fun x δ h f hf => ?_⟩
  have hk : ∀ a ∈ maximalIdeal R ^ (m + 1), δ a = 0 := fun a ha => by
    refine Submodule.smul_induction_on (p := fun z => z = 0) (der_pow x δ h m a ha).2 (fun r hr z _ => ?_)
      (fun u v hu hv => by rw [hu, hv, add_zero])
    rw [Algebra.smul_def, Ideal.Quotient.algebraMap_eq, Ideal.Quotient.eq_zero_iff_mem.2 hr, zero_mul]
  have h1 := hf (m + 1)
  rw [IsLocallyConstant.iff_eventually_eq] at h1 ⊢
  intro g
  filter_upwards [h1 g] with g' hg
  rw [← sub_eq_zero, ← map_sub]
  exact hk _ (Ideal.Quotient.eq.1 hg)
