import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.HodgeWedgeFields.H1CommutesBaseChange

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR

attribute [local instance] Over.cartesianMonoidalCategory

namespace MainStatements.Hodge.Sh

def NEFin (J : Type) : Type := {t : Finset J // t.Nonempty}

open Classical in

instance (J : Type) : SemilatticeInf (NEFin J) where
  le a b := b.1 ⊆ a.1
  le_refl _ := Finset.Subset.refl _
  le_trans _ _ _ hab hbc := Finset.Subset.trans hbc hab
  le_antisymm a b hab hba := Subtype.ext (Finset.Subset.antisymm hba hab)
  inf a b := ⟨a.1 ∪ b.1, a.2.mono Finset.subset_union_left⟩
  inf_le_left _ _ := Finset.subset_union_left
  inf_le_right _ _ := Finset.subset_union_right
  le_inf _ _ _ hab hac := Finset.union_subset hab hac

instance (J : Type) [Finite J] : Finite (NEFin J) :=
  inferInstanceAs (Finite {t : Finset J // t.Nonempty})

theorem isAffineOpen_inf_of_isSeparated {R : Type} [CommRing R] {X : Scheme.{0}} (s : X ⟶ Sp R)
    (hs : IsSeparated s) {U V : X.Opens} (hU : IsAffineOpen U) (hV : IsAffineOpen V) : IsAffineOpen (U ⊓ V) := by
  have := hs
  exact (isAffineHom_diagonal_iff (f := s)).mp inferInstance ⊤ (isAffineOpen_top _) U (by simp) V (by simp) hU hV

def sysOfCover {R : Type} [CommRing R] {X : Scheme.{0}} (s : X ⟶ Sp R) (hs : IsSeparated s) {J : Type}
    (U : J → X.affineOpens) (hU : ⨆ i, (U i).1 = ⊤) : Sys X (NEFin J) where
  u a := ⟨a.1.inf' a.2 fun i ↦ (U i).1,
    Finset.inf'_induction a.2 _ (fun _ h₁ _ h₂ ↦ isAffineOpen_inf_of_isSeparated s hs h₁ h₂) fun i _ ↦ (U i).2⟩
  map_inf a b := by
    classical
    exact Finset.inf'_union a.2 b.2 _
  cover := by
    refine eq_top_iff.2 fun x _ ↦ ?_
    have hx : x ∈ ⨆ i, (U i).1 := hU ▸ trivial
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 hx
    refine TopologicalSpace.Opens.mem_iSup.2 ⟨⟨{i}, Finset.singleton_nonempty i⟩, ?_⟩
    simpa using hi

theorem exists_finite_sys {R : Type} [CommRing R] {X : Scheme.{0}} (s : X ⟶ Sp R) (hs : IsSeparated s)
    (hq : QuasiCompact s) : ∃ (P : Type) (_ : SemilatticeInf P) (_ : Finite P), Nonempty (Sys X P) := by
  have := hq
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace s
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun U : X.affineOpens ↦ (U.1 : Set X))
    (fun U ↦ U.1.isOpen) fun x _ ↦ by
      have hx : x ∈ ⨆ i : X.affineOpens, (i : X.Opens) := (iSup_affineOpens_eq_top X).symm ▸ trivial
      obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 hx
      exact Set.mem_iUnion.2 ⟨i, hi⟩
  refine ⟨NEFin t, inferInstance, inferInstance, ⟨sysOfCover s hs (fun i : t ↦ i.1) ?_⟩⟩
  refine eq_top_iff.2 fun x _ ↦ ?_
  obtain ⟨i, hit, hi⟩ := Set.mem_iUnion₂.1 (ht (Set.mem_univ x))
  exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨i, hit⟩, hi⟩

end MainStatements.Hodge.Sh
