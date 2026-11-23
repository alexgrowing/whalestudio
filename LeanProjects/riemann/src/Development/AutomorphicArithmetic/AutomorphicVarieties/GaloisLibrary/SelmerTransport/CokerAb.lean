import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.RestrictionMemInvariantH1
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.TransgOpen
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.LengthSpanCocycleFinite

open ReciprocityTheory.Gal UpperTheory.V.Base

theorem UpperTheory.V.Base.cokerAb :
    ∀ (R G M : Type) [CommRing R] [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup M] [Module R M]
      [TopologicalSpace M] [IsTopologicalAddGroup M] [ContinuousConstSMul R M] [DiscreteTopology M] (ρ : Representation R G M) [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G] [IsPrincipalIdealRing R], ContAction ρ → (∀ m : M, Module.length R (Submodule.span R {m}) ≠ ⊤) → (∀ g, ∃ c : R, ∀ m, ρ g m = c • m) →
      ∀ (U' U : Subgroup G) [U'.Normal] (h : U' ≤ U), IsClosed (U : Set G) → IsOpen (U'.subgroupOf U : Set U) →
      (∀ a ∈ U, ∀ b ∈ U, a * b * a⁻¹ * b⁻¹ ∈ U') → Module.length R (resCoker ρ h) ≤ (U'.relIndex U : ℕ∞) ^ 2 * Module.length R (H0U ρ U) := by
  intro R G M _ _ _ _ _ _ _ _ _ _ ρ _ _ _ _ hρ hfin hsc U' U _ h hcl ho hab
  haveI : CompactSpace U := isCompact_iff_compactSpace.1 hcl.isCompact
  haveI : Finite (U ⧸ U'.subgroupOf U) := Subgroup.quotient_finite_of_isOpen _ ho
  haveI : DiscreteTopology (U ⧸ U'.subgroupOf U) := QuotientGroup.discreteTopology ho
  refine (length_restriction_coker_le_H2 ρ hρ h ho).trans ((h2Ab R _ _ (quotRep ρ U U') (fun a b => ?_) (fun m => ?_)
    fun g => ?_).trans (mul_le_mul_right (length_H0_quotient_rep_le ρ U' U) _))
  · obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective b
    rw [← mul_inv_eq_one, mul_inv_rev, ← mul_assoc, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_inv,
      ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq_one_iff]
    exact hab a a.2 b b.2
  · have e := (Submodule.equivMapOfInjective _ (Submodule.injective_subtype _) (Submodule.span R {m})).length_eq
    rw [Submodule.map_span, Set.image_singleton] at e
    rw [e]
    exact hfin _
  · obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective g
    obtain ⟨c, hc⟩ := hsc g
    exact ⟨c, fun m => Subtype.ext (hc m)⟩
