import Mathlib

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj TopologicalSpace TensorProduct
open scoped CategoryTheory.Obj

set_option autoImplicit false

namespace GlobalTheory.ConnOpen

theorem isOpen_connectedComponent_noetherian {Y : Type*} [TopologicalSpace Y] [NoetherianSpace Y] (y : Y) :
    IsOpen (connectedComponent y) := by
  set C := connectedComponent y
  have key : ∀ t, t ∉ C → irreducibleComponent t ⊆ Cᶜ := by
    intro t ht s hs hsC
    have h1 : irreducibleComponent t ⊆ connectedComponent s :=
      _root_.IsPreconnected.subset_connectedComponent
        (isIrreducible_irreducibleComponent (x := t)).isConnected.isPreconnected hs
    rw [← connectedComponent_eq hsC] at h1
    exact ht (h1 mem_irreducibleComponent)
  have hC : Cᶜ = ⋃ Z ∈ {Z ∈ irreducibleComponents Y | Z ⊆ Cᶜ}, Z := by
    ext t
    refine ⟨fun ht => Set.mem_biUnion ⟨irreducibleComponent_mem_irreducibleComponents t, key t ht⟩
      mem_irreducibleComponent, fun ht => ?_⟩
    obtain ⟨Z, ⟨-, hZ⟩, htZ⟩ := Set.mem_iUnion₂.1 ht
    exact hZ htZ
  have hcl : IsClosed Cᶜ := by
    rw [hC]
    exact (NoetherianSpace.finite_irreducibleComponents.subset fun _ h => h.1).isClosed_biUnion
      fun Z h => isClosed_of_mem_irreducibleComponents Z h.1
  exact isClosed_compl_iff.1 hcl

end GlobalTheory.ConnOpen

theorem GlobalTheory.isOpen_connectedComponent_of_isLocallyNoetherian :
    ∀ (X : Scheme.{0}), IsLocallyNoetherian X → ∀ x : X, IsOpen (connectedComponent x) := by
  intro X hX x
  rw [isOpen_iff_forall_mem_open]
  intro y hy
  obtain ⟨U, hU, hyU, -⟩ := exists_isAffineOpen_mem_and_subset (X := X) (U := ⊤) (x := y) trivial
  haveI : IsNoetherianRing Γ(X, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  haveI : NoetherianSpace (U : Set X) := noetherianSpace_of_isAffineOpen U hU
  let y' : (U : Set X) := ⟨y, hyU⟩
  refine ⟨Subtype.val '' connectedComponent y', ?_,
    U.isOpen.isOpenEmbedding_subtypeVal.isOpenMap _ (GlobalTheory.ConnOpen.isOpen_connectedComponent_noetherian y'),
    ⟨y', mem_connectedComponent, rfl⟩⟩
  have hc : _root_.IsPreconnected (Subtype.val '' connectedComponent y' : Set X) :=
    isPreconnected_connectedComponent.image _ continuous_subtype_val.continuousOn
  have := hc.subset_connectedComponent ⟨y', mem_connectedComponent, rfl⟩
  rwa [← connectedComponent_eq hy] at this
