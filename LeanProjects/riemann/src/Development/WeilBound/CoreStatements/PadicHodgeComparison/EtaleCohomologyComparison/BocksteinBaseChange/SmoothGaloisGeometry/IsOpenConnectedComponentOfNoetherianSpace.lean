import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.EtProps

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace

namespace CrystallineSemistableComparison

theorem isOpen_connectedComponent_of_noetherianSpace {X : Type*} [TopologicalSpace X] [NoetherianSpace X]
    (x : X) : IsOpen (connectedComponent x) := by
  have hfin : (irreducibleComponents X).Finite := NoetherianSpace.finite_irreducibleComponents
  have h : (connectedComponent x)ᶜ =
      ⋃ Z ∈ {Z ∈ irreducibleComponents X | ¬ Z ⊆ connectedComponent x}, Z := by
    ext y
    simp only [Set.mem_compl_iff, Set.mem_iUnion, Set.mem_ofPred_eq, exists_prop]
    constructor
    · intro hy
      obtain ⟨Z, hZ, hyZ⟩ := exists_mem_irreducibleComponents_subset_of_isIrreducible {y}
        isIrreducible_singleton
      refine ⟨Z, ⟨hZ, fun hsub ↦ hy (hsub (hyZ rfl))⟩, hyZ rfl⟩
    · rintro ⟨Z, ⟨hZ, hnot⟩, hyZ⟩ hy
      apply hnot
      have h1 : Z ⊆ connectedComponent y :=
        IsPreconnected.subset_connectedComponent (IsPreirreducible.isPreconnected hZ.1.2) hyZ
      rwa [← connectedComponent_eq hy] at h1
  have hc : IsClosed (connectedComponent x)ᶜ := by
    rw [h]
    exact (hfin.subset fun Z hZ ↦ hZ.1).isClosed_biUnion fun Z hZ ↦ isClosed_of_mem_irreducibleComponents Z hZ.1
  exact isClosed_compl_iff.mp hc

theorem finite_connectedComponents_of_noetherianSpace (X : Type*) [TopologicalSpace X] [NoetherianSpace X] :
    Finite (_root_.ConnectedComponents X) := by
  have : DiscreteTopology (_root_.ConnectedComponents X) := by
    rw [discreteTopology_iff_isOpen_singleton]
    intro c
    obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe c
    rw [← ConnectedComponents.isQuotientMap_coe.isOpen_preimage, connectedComponents_preimage_singleton]
    exact isOpen_connectedComponent_of_noetherianSpace x
  have : CompactSpace (_root_.ConnectedComponents X) := inferInstance
  exact finite_of_compact_of_discrete

theorem exists_isSum_components (X : Scheme.{0}) [NoetherianSpace X] :
    ∃ (r : ℕ) (U : Fin r → X.Opens), IsSum (fun a ↦ (U a).ι) ∧ ∀ a, ConnectedSpace (U a).toScheme := by
  have := finite_connectedComponents_of_noetherianSpace X
  let e := Finite.equivFin (_root_.ConnectedComponents X)
  have hopen : ∀ c : _root_.ConnectedComponents X, IsOpen (_root_.ConnectedComponents.mk ⁻¹' {c} : Set X) := by
    intro c
    obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe c
    rw [connectedComponents_preimage_singleton]
    exact isOpen_connectedComponent_of_noetherianSpace x
  let U : Fin (Nat.card (_root_.ConnectedComponents X)) → X.Opens := fun a ↦ ⟨_, hopen (e.symm a)⟩
  refine ⟨_, U, ⟨fun a ↦ inferInstance, fun x ↦ ⟨e (_root_.ConnectedComponents.mk x), ?_⟩, fun a b hab ↦ ?_⟩, fun a ↦ ?_⟩
  · rw [Scheme.Opens.range_ι]
    show _root_.ConnectedComponents.mk x = e.symm (e (_root_.ConnectedComponents.mk x))
    simp
  · rw [Scheme.Opens.range_ι, Scheme.Opens.range_ι]
    refine Set.disjoint_left.mpr fun y hy hy' ↦ hab (e.symm.injective ?_)
    exact (hy : _root_.ConnectedComponents.mk y = _).symm.trans hy'
  · obtain ⟨x, hx⟩ := ConnectedComponents.surjective_coe (e.symm a)
    have hU : ((U a : X.Opens) : Set X) = connectedComponent x := by
      show _root_.ConnectedComponents.mk ⁻¹' {e.symm a} = _
      rw [← hx, connectedComponents_preimage_singleton]
    have : ConnectedSpace ((U a : X.Opens) : Set X) := by
      rw [hU]; exact isConnected_iff_connectedSpace.mp isConnected_connectedComponent
    exact this

end CrystallineSemistableComparison
