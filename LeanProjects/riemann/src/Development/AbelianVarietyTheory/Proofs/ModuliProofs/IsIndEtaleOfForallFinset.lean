import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.CMModuli.ProjectiveSpaceOverSpec

open CategoryTheory Limits

noncomputable section

namespace GlobalTheory.IndEtaleUnion

variable (A S : Type) [CommRing A] [CommRing S] [Algebra A S]

abbrev EtaleSub : Type := {T : Subalgebra A S // Algebra.Etale A T}

def diagram : EtaleSub A S ⥤ CommRingCat.{0} where
  obj T := CommRingCat.of T.1
  map {T U} h := CommRingCat.ofHom (Subalgebra.inclusion (show T.1 ≤ U.1 from leOfHom h)).toRingHom
  map_id _ := rfl
  map_comp _ _ := rfl

def fromBase : (Functor.const (EtaleSub A S)).obj (CommRingCat.of A) ⟶ diagram A S where
  app T := CommRingCat.ofHom (algebraMap A T.1)
  naturality _ _ _ := rfl

def toTop : diagram A S ⟶ (Functor.const (EtaleSub A S)).obj (CommRingCat.of S) where
  app T := CommRingCat.ofHom T.1.val.toRingHom
  naturality _ _ _ := rfl

variable {A S}

theorem exists_finset_adjoin (T : EtaleSub A S) :
    ∃ s : Finset S, Algebra.adjoin A (s : Set S) = T.1 := by
  haveI := T.2
  exact (Subalgebra.fg_iff_finiteType T.1).2 inferInstance

theorem isDirected
    (h : ∀ s : Finset S, ∃ T : Subalgebra A S, Algebra.Etale A T ∧ (s : Set S) ⊆ T) :
    IsDirectedOrder (EtaleSub A S) := by
  classical
  refine ⟨fun T U => ?_⟩
  obtain ⟨s, hs⟩ := exists_finset_adjoin T
  obtain ⟨t, ht⟩ := exists_finset_adjoin U
  obtain ⟨V, hV, hst⟩ := h (s ∪ t)
  rw [Finset.coe_union, Set.union_subset_iff] at hst
  refine ⟨⟨V, hV⟩, ?_, ?_⟩
  · change T.1 ≤ V
    rw [← hs]
    exact Algebra.adjoin_le hst.1
  · change U.1 ≤ V
    rw [← ht]
    exact Algebra.adjoin_le hst.2

theorem isIndEtale_of_forall_finset (A S : Type) [CommRing A] [CommRing S] [Algebra A S]
    (h : ∀ s : Finset S, ∃ T : Subalgebra A S, Algebra.Etale A T ∧ (s : Set S) ⊆ T) :
    GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec.IsIndEtale (algebraMap A S) := by
  haveI := isDirected h
  haveI : Nonempty (EtaleSub A S) := by
    obtain ⟨T, hT, -⟩ := h ∅
    exact ⟨⟨T, hT⟩⟩
  haveI : IsFiltered (EtaleSub A S) := inferInstance
  refine ⟨EtaleSub A S, inferInstance, inferInstance, diagram A S, fromBase A S, toTop A S,
    ?_, fun T => ⟨RingHom.etale_algebraMap.2 T.2, rfl⟩⟩
  haveI : ReflectsColimit (diagram A S) (forget CommRingCat.{0}) :=
    reflectsColimit_of_reflectsIsomorphisms _ _
  refine isColimitOfReflects (forget CommRingCat.{0}) ?_
  refine Types.FilteredColimit.isColimitOf' _ _ (fun x => ?_) (fun T x y hxy => ?_)
  · obtain ⟨T, hT, hx⟩ := h {(x : S)}
    exact ⟨⟨T, hT⟩, ⟨x, hx (by simp)⟩, rfl⟩
  · have : x = y := Subtype.ext hxy
    exact ⟨T, 𝟙 T, by rw [this]⟩

end GlobalTheory.IndEtaleUnion
