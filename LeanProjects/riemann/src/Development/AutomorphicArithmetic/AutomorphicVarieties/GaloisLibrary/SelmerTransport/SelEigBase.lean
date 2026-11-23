import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.RestrictionMemInvariantH1
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.SelTwist
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.SelUnit

open ReciprocityTheory.Gal UpperTheory.V.Base

theorem UpperTheory.V.Base.selEigBase :
    ∀ (R G M : Type) [CommRing R] [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup M] [Module R M]
      [TopologicalSpace M] [IsTopologicalAddGroup M] [ContinuousConstSMul R M] [DiscreteTopology M] (ρ : Representation R G M) (ρ' : Representation R G M) (θ : G →* Rˣ), (∀ g m, ρ g m = ((θ g : Rˣ) : R) • ρ' g m) → ContAction ρ' →
      ∀ (U W : Subgroup G) [U.Normal], U ≤ W → (∀ u ∈ U, θ u = 1) → IsOpen (U.subgroupOf W : Set W) → IsUnit (U.relIndex W : R) →
      ∀ (𝒟 : Set (Subgroup G)) (h𝒟 : ConjStable 𝒟), Module.length R (selEig ρ U h𝒟 W (θ.comp W.subtype)) = Module.length R (LocSel ρ' W 𝒟) := by
  intro R G M _ _ _ _ _ _ _ _ _ _ ρ ρ' θ hρ hc U W _ hUW hθ ho hu 𝒟 h𝒟
  have h1 := (selTwist R G M ρ ρ' θ hρ U hθ 𝒟 h𝒟).2 W 1
  obtain ⟨hi, hr⟩ := selUnit R G M ρ' hc U W hUW ho hu 𝒟 h𝒟
  have e : θ.comp W.subtype * (1 : W →* Rˣ) = θ.comp W.subtype := mul_one _
  rw [e] at h1
  rw [h1, ← hr]
  exact (LinearEquiv.ofInjective _ hi).length_eq.symm
