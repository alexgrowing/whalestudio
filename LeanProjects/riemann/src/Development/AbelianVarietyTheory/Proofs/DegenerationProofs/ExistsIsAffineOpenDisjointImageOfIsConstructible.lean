import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteOfIsClosedTorusZariskiOfPowEqOne
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
local notation "OO" p:max => (Valuation.valuationSubring (Valued.v : Valuation (PadicAlgCl p) NNReal))
local notation "cPt" p:max => (IsLocalRing.closedPoint (OO p) : Sp (OO p))
local notation "gPt" p:max => spMap (ValuationSubring.subtype (OO p))

namespace GlobalTheory

theorem interior_closure_eq_empty_of_isConstructible_of_disjoint_dense
    {Y : Type*} [TopologicalSpace Y] {D Sg : Set Y} (hD : Topology.IsConstructible D)
    (hSg : Dense Sg) (h : Disjoint D Sg) : interior (closure D) = ∅ := by
  have h1 : interior (frontier D) = ∅ :=
    interior_frontier_preimage_of_isConstructible (f := id) continuous_id hD
  have h2 : interior D = ∅ :=
    interior_eq_empty_iff_dense_compl.2 (hSg.mono h.subset_compl_left)
  rwa [frontier, h2, Set.diff_empty] at h1

theorem exists_isAffineOpen_disjoint_image_of_isConstructible_of_disjoint_dense :
    ∀ (X S : Scheme.{0}) [IsIntegral S] [IsNoetherian S] (f : X ⟶ S) [LocallyOfFiniteType f] [QuasiCompact f] (C : Set X) (Sg : Set S), Topology.IsConstructible C → Dense Sg → Disjoint (f '' C) Sg → ∃ V : S.Opens, (V : Set S).Nonempty ∧ IsAffineOpen V ∧ Disjoint (f '' C) V := by
  intro X S _ _ f _ _ C Sg hC hSg h
  have hD : Topology.IsConstructible (f '' C) := f.isConstructible_image hC
  have h1 := interior_closure_eq_empty_of_isConstructible_of_disjoint_dense hD hSg h
  obtain ⟨x, hx⟩ : ((closure (f '' C))ᶜ).Nonempty :=
    (interior_eq_empty_iff_dense_compl.1 h1).nonempty
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVU⟩ :=
    S.isBasis_affineOpens.exists_subset_of_mem_open hx isClosed_closure.isOpen_compl
  refine ⟨V, ⟨x, hxV⟩, hV, ?_⟩
  exact Set.disjoint_left.2 fun y hy hyV => hVU hyV (subset_closure hy)

end GlobalTheory
