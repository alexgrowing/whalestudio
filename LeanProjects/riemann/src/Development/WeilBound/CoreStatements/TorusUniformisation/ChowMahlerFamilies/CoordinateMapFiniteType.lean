import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ToXQFst
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LocRatio
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.SegreChartBundle
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open GlobalTheory.CompanionTheory.Ar.TorusUnif
open scoped CategoryTheory.Obj

namespace PositivityTheory.Xgn.CoordinateMapFiniteType

theorem finiteType_of_range {A Ω R : Type} [CommRing A] [Field Ω] [CommRing R] (φ : A →+* Ω)
    (hφ : Function.Injective φ) (s : Set Ω) (hs : s.Finite)
    (h : ∀ a : Ω, a ∈ Algebra.adjoin ℤ s ↔ a ∈ φ.range) (ψ : R →+* A) : ψ.FiniteType := by
  have h1 : Algebra.FiniteType ℤ (Algebra.adjoin ℤ s) :=
    (Subalgebra.fg_iff_finiteType _).1 (Subalgebra.fg_def.2 ⟨s, hs, rfl⟩)
  have hr : φ.toIntAlgHom.range = Algebra.adjoin ℤ s := by
    ext a
    rw [h a]
    rfl
  have h2 : Algebra.FiniteType ℤ A :=
    Algebra.FiniteType.equiv h1
      ((AlgEquiv.ofInjective φ.toIntAlgHom hφ).trans (Subalgebra.equivOfEq _ _ hr)).symm
  have h3 : (ψ.comp (algebraMap ℤ R)).FiniteType := by
    rw [Subsingleton.elim (ψ.comp (algebraMap ℤ R)) (algebraMap ℤ A)]
    exact RingHom.finiteType_algebraMap.2 h2
  exact RingHom.FiniteType.of_comp_finiteType h3

theorem main {X Y : Scheme.{0}} [IsAffine Y] (f : X ⟶ Y) {Ω : Type} [Field Ω] {κ : Type} [Finite κ] {x : κ → Ω}
    {ξ : Spec (CommRingCat.of Ω) ⟶ X} (hq : ∀ q : X, genPt ξ ⤳ q) (hT : CoordTie ℤ ξ x) :
    LocallyOfFiniteType f ∧ QuasiCompact f := by
  choose U h hU hUq _ hinj hran using fun c : {c // x c ≠ 0} => TieFrame.exists_chart hT c.2
  have hcov : ∀ q : X, ∃ c, q ∈ U c := fun q => by
    obtain ⟨c, hc⟩ := hT.cover ⟨q, hq q⟩
    exact ⟨⟨c, hc.1⟩, (hUq ⟨c, hc.1⟩ ⟨q, hq q⟩).2 hc⟩
  constructor
  · have htop : ⨆ c, ((⟨U c, hU c⟩ : X.affineOpens) : X.Opens) = ⊤ := by
      refine top_le_iff.1 fun q _ => ?_
      obtain ⟨c, hc⟩ := hcov q
      exact TopologicalSpace.Opens.mem_iSup.2 ⟨c, hc⟩
    refine (HasRingHomProperty.iff_of_iSup_eq_top (P := @LocallyOfFiniteType)
      (fun c => (⟨U c, hU c⟩ : X.affineOpens)) htop).2 fun c => ?_
    exact finiteType_of_range _ (hinj c) _ (Set.finite_range _) (hran c) _
  · have : CompactSpace X := by
      refine ⟨?_⟩
      have e : (Set.univ : Set X) = ⋃ c, (U c : Set X) :=
        (Set.eq_univ_of_forall fun q => Set.mem_iUnion.2 (hcov q)).symm
      rw [e]
      exact isCompact_iUnion fun c => (hU c).isCompact
    exact (quasiCompact_iff_compactSpace f).2 this

end PositivityTheory.Xgn.CoordinateMapFiniteType

theorem PositivityTheory.Xgn.coordinate_map_finite_type : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)]
    (y : (Σ k, J k) → Ω) (ξ : Sp Ω ⟶ X), (∀ q : X, genPt ξ ⤳ q) →
    CoordTie ℤ ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) → LocallyOfFiniteType (toZ X) ∧ QuasiCompact (toZ X) := by
  intro X Ω _ K _ J _ y ξ hq hT
  exact PositivityTheory.Xgn.CoordinateMapFiniteType.main (toZ X) hq hT
