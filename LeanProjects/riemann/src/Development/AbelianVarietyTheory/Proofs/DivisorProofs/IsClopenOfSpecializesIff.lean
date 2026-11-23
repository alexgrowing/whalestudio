import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDefiniteDatumGoodObj
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateCondCongr
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel GlobalTheory.UPelLevel
open scoped CategoryTheory.Obj TensorProduct

set_option autoImplicit false

noncomputable section

open Set Topology

namespace GlobalTheory.SpecGenClopen

theorem isClosed_of_stable (X : Scheme.{0}) [IsLocallyNoetherian X] (T : Set X)
    (hs : StableUnderSpecialization T) (hg : StableUnderGeneralization T) : IsClosed T := by
  rw [← isOpen_compl_iff, isOpen_iff_forall_mem_open]
  intro x hx
  obtain ⟨U, hU, hxU, -⟩ := exists_isAffineOpen_mem_and_subset (X := X) (U := ⊤) (x := x) trivial
  haveI : IsNoetherianRing Γ(X, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  haveI : TopologicalSpace.NoetherianSpace (U : Set X) := noetherianSpace_of_isAffineOpen U hU
  let T' : Set (U : Set X) := Subtype.val ⁻¹' T
  have key : ∀ Z : Set (U : Set X), IsIrreducible Z → (Z ∩ T').Nonempty → Z ⊆ T' := by
    rintro Z hZ ⟨t, htZ, htT⟩ z hz
    have hI : IsIrreducible (closure (Subtype.val '' Z : Set X)) :=
      (hZ.image _ continuous_subtype_val.continuousOn).closure
    obtain ⟨g₀, hg₀⟩ := QuasiSober.sober hI isClosed_closure
    have h1 : g₀ ⤳ (t : X) := hg₀.specializes (subset_closure ⟨t, htZ, rfl⟩)
    have h2 : g₀ ⤳ (z : X) := hg₀.specializes (subset_closure ⟨z, hz, rfl⟩)
    exact hs h2 (hg h1 htT)
  have hT' : T' = ⋃ Z ∈ {Z ∈ irreducibleComponents (U : Set X) | (Z ∩ T').Nonempty}, Z := by
    ext t
    refine ⟨fun ht => Set.mem_biUnion ⟨irreducibleComponent_mem_irreducibleComponents t,
      ⟨t, mem_irreducibleComponent, ht⟩⟩ mem_irreducibleComponent, fun ht => ?_⟩
    obtain ⟨Z, ⟨hZ, hZT⟩, htZ⟩ := Set.mem_iUnion₂.1 ht
    exact key Z hZ.1 hZT htZ
  have hc : IsClosed T' := by
    rw [hT']
    exact (TopologicalSpace.NoetherianSpace.finite_irreducibleComponents.subset fun _ h => h.1).isClosed_biUnion
      fun Z h => isClosed_of_mem_irreducibleComponents Z h.1
  refine ⟨Subtype.val '' T'ᶜ, ?_, U.isOpen.isOpenEmbedding_subtypeVal.isOpenMap _ hc.isOpen_compl, ⟨x, hxU⟩, hx, rfl⟩
  rintro _ ⟨t, ht, rfl⟩
  exact ht

theorem isClopen_of_specializes_iff : ∀ (X : Scheme.{0}) [IsLocallyNoetherian X] (Z : Set X),
    (∀ x y : X, x ⤳ y → (x ∈ Z ↔ y ∈ Z)) → IsClopen Z := by
  intro X _ Z h
  have hs : StableUnderSpecialization Z := fun x y hxy hx => (h x y hxy).1 hx
  have hg : StableUnderGeneralization Z := fun x y hxy hx => (h y x hxy).2 hx
  exact ⟨isClosed_of_stable X Z hs hg, isClosed_compl_iff.1 (isClosed_of_stable X Zᶜ
    (stableUnderSpecialization_compl_iff.2 hg) (stableUnderGeneralization_compl_iff.2 hs))⟩

end GlobalTheory.SpecGenClopen
