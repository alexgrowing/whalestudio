import Mathlib
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.PolarizedAbelianEmbeddingBySections
import Development.AbelianVarietyTheory.Definitions.Degenerations.PullChartIsLB
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra

namespace GlobalTheory.ZH.SpanImm

theorem closure_eq_top_iff {A B J : Type} [CommRing A] [CommRing B] (c : A →+* B) (r : J → B) :
    Subring.closure (Set.range c ∪ Set.range r) = ⊤ ↔
      Function.Surjective (MvPolynomial.eval₂Hom c r) := by
  rw [← RingHom.range_eq_top]
  suffices h : Subring.closure (Set.range c ∪ Set.range r) = (MvPolynomial.eval₂Hom c r).range by
    rw [h]
  refine le_antisymm (Subring.closure_le.2 ?_) ?_
  · rintro _ (⟨a, rfl⟩ | ⟨j, rfl⟩)
    · exact ⟨MvPolynomial.C a, MvPolynomial.eval₂Hom_C _ _ _⟩
    · exact ⟨MvPolynomial.X j, MvPolynomial.eval₂Hom_X' _ _ _⟩
  · rintro _ ⟨q, rfl⟩
    induction q using MvPolynomial.induction_on with
    | C a =>
      rw [MvPolynomial.eval₂Hom_C]
      exact Subring.subset_closure (Or.inl ⟨a, rfl⟩)
    | add p q hp hq => rw [map_add]; exact add_mem hp hq
    | mul_X p j hp =>
      rw [map_mul, MvPolynomial.eval₂Hom_X']
      exact mul_mem hp (Subring.subset_closure (Or.inr ⟨j, rfl⟩))

theorem range_constFn {k : Type} [CommRing k] {X : Scheme.{0}} (p : X ⟶ Sp k) (U : X.Opens) :
    Set.range (constFn p U) = Set.range (p.appLE ⊤ U le_top).hom := by
  have hs := (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of k)).inv).2
  exact hs.range_comp (p.appLE ⊤ U le_top).hom

theorem immBy_iff {k : Type} [CommRing k] {X : Scheme.{0}} (p : X ⟶ Sp k) (H : LB X) {J : Type}
    (s : J → H.Sec) : ImmBy p H s Set.univ ↔ AmpleSpan.EmbedsBy p s := by
  unfold ImmBy AmpleSpan.EmbedsBy
  simp only [Set.mem_univ, iSup_pos, forall_true_left, range_constFn, closure_eq_top_iff]
  rfl

theorem immBy_of_span : (∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) [IsProper p] (H : LB X), H.IsLB → ∀ (I J : Type) [Fintype I] [Fintype J] (t : I → H.Sec) (s : J → H.Sec), ImmBy p H t Set.univ → (∀ i, ∃ a : J → k, IsLin p s a (t i)) → ImmBy p H s Set.univ) := by
  intro k _ X p _ H _ I J _ _ t s ht hs
  refine (immBy_iff p H s).2 (((immBy_iff p H t).1 ht).of_inSpan fun i => ?_)
  obtain ⟨a, ha⟩ := hs i
  exact ⟨fun j => (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom (a j), ha⟩

end GlobalTheory.ZH.SpanImm
