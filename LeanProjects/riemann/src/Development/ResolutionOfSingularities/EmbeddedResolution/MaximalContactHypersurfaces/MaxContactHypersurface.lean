import Mathlib
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.ChartRing
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.StrictNormalCrossings
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.SmoothRegular
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.IdealSheafOrder
import Development.ResolutionOfSingularities.EmbeddedResolution.MaximalContactHypersurfaces.MaxContactIdeal
import Development.ResolutionOfSingularities.EmbeddedResolution.MaximalContactHypersurfaces.MaxContactCoordinate
universe u

open AlgebraicGeometry CategoryTheory TopologicalSpace

namespace FunctorialResolution.EmbeddedResolution

section

variable (k : Type u) [Field k] {X : Scheme.{u}} (p : X ⟶ Spec (CommRingCat.of k))
  [LocallyOfFiniteType p]

def IsMaxContactHypersurface (A : X.IdealSheafData) (m : ℕ) (H : X.IdealSheafData) : Prop :=
  ∀ x : X, ∃ U : X.Opens, IsAffineOpen U ∧ x ∈ U ∧
    ((Disjoint (orderAtLeastLocus A m) (U : Set ↥X) ∧ restrictIdeal H U = ⊤) ∨
      (∃ (n : ℕ) (c : EtaleChart p U n) (j : Fin n),
        restrictIdeal H U = c.coordIdeal {j} ∧ IsMaxContactCoord k p A m c j))

theorem isMaxContactHypersurface_iff (A : X.IdealSheafData) (m : ℕ) (H : X.IdealSheafData) :
    IsMaxContactHypersurface k p A m H ↔
      ∀ x : X, ∃ U : X.Opens, IsAffineOpen U ∧ x ∈ U ∧
        ((Disjoint (orderAtLeastLocus A m) (U : Set ↥X) ∧ restrictIdeal H U = ⊤) ∨
          (∃ (n : ℕ) (c : EtaleChart p U n) (j : Fin n),
            restrictIdeal H U = c.coordIdeal {j} ∧ IsMaxContactCoord k p A m c j)) :=
  Iff.rfl

end

section

variable {k : Type u} [Field k] [CharZero k] {X : Scheme.{u}}
  {p : X ⟶ Spec (CommRingCat.of k)} [LocallyOfFiniteType p] [AlgebraicGeometry.Smooth p]

theorem IsMaxContactHypersurface.orderAtLeastLocus_subset_support {A : X.IdealSheafData} {m : ℕ}
    {H : X.IdealSheafData} (h : IsMaxContactHypersurface k p A m H) (hm : 1 ≤ m) :
    orderAtLeastLocus A m ⊆ (H.support : Set ↥X) := by
  intro x hx
  obtain ⟨U, hU, hxU, hcase⟩ := h x
  rcases hcase with ⟨hdisj, -⟩ | ⟨n, c, j, hH, hmc⟩
  · exact absurd hxU (Set.disjoint_left.mp hdisj hx)
  · have hmem : c.coord j ∈ (maxContactIdeal k p A m).ideal ⟨U, hU⟩ :=
      (isMaxContactCoord_iff_coord_mem k p A m hU c j).mp hmc
    have hHideal :
        H.ideal ⟨U, hU⟩ = Ideal.span (c.coord '' (({j} : Finset (Fin n)) : Set (Fin n))) :=
      c.ideal_eq_span_coord hU H {j} hH
    have hle : H.ideal ⟨U, hU⟩ ≤ (maxContactIdeal k p A m).ideal ⟨U, hU⟩ := by
      rw [hHideal, Finset.coe_singleton, Set.image_singleton, Ideal.span_le,
        Set.singleton_subset_iff]
      exact hmem
    have hst : stalkIdeal H x ≤ stalkIdeal (maxContactIdeal k p A m) x := by
      rw [stalkIdeal_eq_map_germ H x ⟨U, hU⟩ hxU,
        stalkIdeal_eq_map_germ (maxContactIdeal k p A m) x ⟨U, hU⟩ hxU]
      exact Ideal.map_mono hle
    have hx' : x ∈ (maxContactIdeal k p A m).support :=
      mem_support_maxContactIdeal_of_mem_orderAtLeastLocus k p A hm hx
    rw [mem_support_iff_stalkIdeal_le_maximalIdeal] at hx'
    have hfin : x ∈ H.support := by
      rw [mem_support_iff_stalkIdeal_le_maximalIdeal]
      exact hst.trans hx'
    exact hfin

end

end FunctorialResolution.EmbeddedResolution
