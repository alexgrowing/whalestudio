import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.RestrictionMemInvariantH1

open ReciprocityTheory.Gal UpperTheory.V.Base

private theorem len_le_add {R A B C D : Type} [CommRing R] [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B]
    [AddCommGroup C] [Module R C] [AddCommGroup D] [Module R D] (g : A →ₗ[R] B) (j : A →ₗ[R] C) (k : C →ₗ[R] D)
    (hj : Function.Injective j) (hk : ∀ x, g x = 0 → k (j x) = 0) :
    Module.length R A ≤ Module.length R B + Module.length R (LinearMap.ker k) := by
  have h1 : Module.length R A = Module.length R (LinearMap.ker g) + Module.length R (LinearMap.range g) :=
    Module.length_eq_add_of_exact (LinearMap.ker g).subtype g.rangeRestrict (Submodule.injective_subtype _)
      g.surjective_rangeRestrict (by
        rw [LinearMap.exact_iff, LinearMap.ker_rangeRestrict, Submodule.range_subtype])
  have h2 : Module.length R (LinearMap.range g) ≤ Module.length R B :=
    Module.length_le_of_injective (LinearMap.range g).subtype (Submodule.injective_subtype _)
  have h3 : Module.length R (LinearMap.ker g) ≤ Module.length R (LinearMap.ker k) :=
    Module.length_le_of_injective (j.restrict (p := LinearMap.ker g) (q := LinearMap.ker k) fun x hx => hk x hx)
      fun x y e => Subtype.ext (hj (congrArg Subtype.val e))
  rw [h1, add_comm]
  exact add_le_add h2 h3

private theorem len_sub {R A B C D : Type} [CommRing R] [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B]
    [AddCommGroup C] [Module R C] [AddCommGroup D] [Module R D] (g : A →ₗ[R] B) (j : A →ₗ[R] C) (k : C →ₗ[R] D)
    (hj : Function.Injective j) (hk : ∀ x, g x = 0 → k (j x) = 0) (P : Submodule R A) (Q : Submodule R B)
    (hPQ : ∀ x ∈ P, g x ∈ Q) :
    Module.length R P ≤ Module.length R Q + Module.length R (LinearMap.ker k) :=
  len_le_add (g.restrict hPQ) (j.comp P.subtype) k (hj.comp (Submodule.injective_subtype P))
    fun x hx => hk x.1 (congrArg Subtype.val hx)

theorem UpperTheory.V.Base.selUp :
    ∀ (R G M : Type) [CommRing R] [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup M] [Module R M]
      [TopologicalSpace M] [IsTopologicalAddGroup M] [ContinuousConstSMul R M] [DiscreteTopology M] (ρ : Representation R G M) (U' U : Subgroup G) (h : U' ≤ U) (𝒟 : Set (Subgroup G)) (h𝒟 : ConjStable 𝒟),
      Module.length R (LocSel ρ U 𝒟) ≤ Module.length R (LocSel ρ U' 𝒟) + Module.length R (LinearMap.ker (resU ρ h)) ∧
      (∀ [U'.Normal], Module.length R (LocSel ρ U 𝒟) ≤ Module.length R (selEig ρ U' h𝒟 U 1) + Module.length R (LinearMap.ker (resU ρ h))) ∧
      (∀ [U'.Normal] [U.Normal] (W : Subgroup G) (ψ : W →* Rˣ),
        Module.length R (selEig ρ U h𝒟 W ψ) ≤ Module.length R (selEig ρ U' h𝒟 W ψ) + Module.length R (LinearMap.ker (resU ρ h))) ∧
      ∀ [U'.Normal] [U.Normal] (g : G) (s : R), Module.length R (Module.End.eigenspace (selRep ρ U h𝒟 g) s) ≤
        Module.length R (Module.End.eigenspace (selRep ρ U' h𝒟 g) s) + Module.length R (LinearMap.ker (resU ρ h)) := by
  intro R G M _ _ _ _ _ _ _ _ _ _ ρ U' U h 𝒟 h𝒟
  have hj := Submodule.injective_subtype (LocSel ρ U 𝒟)
  have hk : ∀ x, selRes ρ h 𝒟 x = 0 → resU ρ h ((LocSel ρ U 𝒟).subtype x) = 0 :=
    fun x hx => congrArg Subtype.val hx
  refine ⟨len_le_add (selRes ρ h 𝒟) _ _ hj hk, ?_, ?_, ?_⟩
  · intro _
    have hm : ∀ x, selRes ρ h 𝒟 x ∈ selEig ρ U' h𝒟 U 1 := fun x => by
      rw [selEig, eig_one]
      intro g
      exact Subtype.ext (restriction_mem_invariant_H1 ρ h x.1 g)
    exact len_le_add ((selRes ρ h 𝒟).codRestrict _ hm) _ _ hj fun x hx => hk x (congrArg Subtype.val hx)
  · intro _ _ W ψ
    refine len_sub (selRes ρ h 𝒟) _ _ hj hk _ _ fun x hx => ?_
    rw [mem_eig] at hx ⊢
    intro g
    have e : selRep ρ U h𝒟 g.1 x = ((ψ g : Rˣ) : R) • x := hx g
    show selRep ρ U' h𝒟 g.1 _ = _
    rw [← selRes_selRep, e, map_smul]
  · intro _ _ g s
    refine len_sub (selRes ρ h 𝒟) _ _ hj hk _ _ fun x hx => ?_
    rw [Module.End.mem_eigenspace_iff] at hx ⊢
    rw [← selRes_selRep, hx, map_smul]
