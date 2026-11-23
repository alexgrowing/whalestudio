import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
import Development.AbelianVarietyTheory.Definitions.Degenerations.PlOrdSomeOfAssociated
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.SemistableFin
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS

namespace GlobalTheory.RatPointConn

universe u

theorem fibre_subsingleton {k K : Type u} [Field k] [Field K] {X Z : Scheme.{u}}
    {f : X ⟶ Spec (.of k)} {y : Spec (.of K) ⟶ Spec (.of k)} {p : Z ⟶ X} {q : Z ⟶ Spec (.of K)}
    (h : IsPullback p q f y) (s : Spec (.of k) ⟶ X) (hs : s ≫ f = 𝟙 _) (a b : Z)
    (ha : p a = s (IsLocalRing.closedPoint k)) (hb : p b = s (IsLocalRing.closedPoint k)) :
    a = b := by
  let t : Spec (.of K) ⟶ Z := h.lift (y ≫ s) (𝟙 _) (by simp [hs])
  have ht : IsPullback t y p s := by
    refine IsPullback.of_right (h₁₂ := q) (v₁₃ := y) (h₂₂ := f) ?_ (by simp [t]) h.flip
    rw [hs, show t ≫ q = 𝟙 _ by simp [t]]
    exact IsPullback.of_id_fst
  obtain ⟨a', rfl, -⟩ := Scheme.exists_preimage_of_isPullback ht a (IsLocalRing.closedPoint k) ha
  obtain ⟨b', rfl, -⟩ := Scheme.exists_preimage_of_isPullback ht b (IsLocalRing.closedPoint k) hb
  rw [Subsingleton.elim a' b']

theorem of_isAlgClosed {k : Type u} [Field k] [IsAlgClosed k]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [LocallyOfFiniteType f] [ConnectedSpace X] :
    GeometricallyConnected f := by
  refine ⟨fun K _ y Z p q h => ?_⟩
  have := LocallyOfFiniteType.jacobsonSpace f
  have hy : Surjective y := ⟨fun a => ⟨Classical.arbitrary _, Subsingleton.elim _ _⟩⟩
  have hs : Surjective p := MorphismProperty.of_isPullback h.flip hy
  have ho : UniversallyOpen p := MorphismProperty.of_isPullback h.flip
    (inferInstance : UniversallyOpen y)
  have fib : ∀ x : X, IsClosed {x} → ∀ a b : Z, p a = x → p b = x → a = b := by
    intro x hx a b ha hb
    exact fibre_subsingleton h (pointOfClosedPoint f x hx) (pointOfClosedPoint_comp f x hx) a b
      (ha.trans (pointOfClosedPoint_apply f x hx _).symm)
      (hb.trans (pointOfClosedPoint_apply f x hx _).symm)
  have hne : Nonempty Z := (p.surjective (Classical.arbitrary X)).nonempty
  have : PreconnectedSpace Z := ⟨fun U V hU hV hUV hU' hV' => by
    rw [Set.univ_inter] at hU' hV' ⊢
    have o₁ : IsOpen (p '' U) := p.isOpenMap _ hU
    have o₂ : IsOpen (p '' V) := p.isOpenMap _ hV
    have hc : Set.univ ⊆ p '' U ∪ p '' V := by
      intro x _
      obtain ⟨z, rfl⟩ := p.surjective x
      exact (hUV (Set.mem_univ z)).imp (fun hz => ⟨z, hz, rfl⟩) (fun hz => ⟨z, hz, rfl⟩)
    have hi := isPreconnected_univ _ _ o₁ o₂ hc (by simpa using hU') (by simpa using hV')
    rw [Set.univ_inter] at hi
    obtain ⟨x, ⟨⟨a, ha, hax⟩, ⟨b, hb, hbx⟩⟩, hxc⟩ := nonempty_inter_closedPoints hi
      (o₁.inter o₂).isLocallyClosed
    exact ⟨a, ha, fib x hxc a b hax hbx ▸ hb⟩⟩
  exact ⟨hne⟩

theorem preconnectedSpace_of_fibre {Z X : Type*} [TopologicalSpace Z] [TopologicalSpace X]
    [PreconnectedSpace X] {p : Z → X} (ho : IsOpenMap p) (hc : IsClosedMap p) (x : X)
    (hx : ∀ a b, p a = x → p b = x → a = b) : PreconnectedSpace Z := by
  have key : ∀ U : Set Z, IsClopen U → U.Nonempty → ∃ a ∈ U, p a = x := by
    intro U hU hne
    have h1 : IsClopen (p '' U) := ⟨hc _ hU.1, ho _ hU.2⟩
    have h2 := h1.eq_univ (hne.image _)
    exact h2.ge (Set.mem_univ x)
  refine ⟨(isPreconnected_iff_subset_of_disjoint).2 fun U V hU hV hUV hd => ?_⟩
  rw [Set.univ_inter] at hd
  have hdis : Disjoint U V := Set.disjoint_iff_inter_eq_empty.2 hd
  have hcompl : IsCompl U V := ⟨hdis, codisjoint_iff.2 (Set.univ_subset_iff.1 hUV)⟩
  have cU : IsClopen U := ⟨⟨by rw [hcompl.compl_eq]; exact hV⟩, hU⟩
  have cV : IsClopen V := ⟨⟨by rw [hcompl.symm.compl_eq]; exact hU⟩, hV⟩
  rcases U.eq_empty_or_nonempty with rfl | nU
  · right; simpa using hUV
  rcases V.eq_empty_or_nonempty with rfl | nV
  · left; simpa using hUV
  obtain ⟨a, ha, hax⟩ := key U cU nU
  obtain ⟨b, hb, hbx⟩ := key V cV nV
  obtain rfl := hx a b hax hbx
  exact absurd hb (Set.disjoint_left.1 hdis ha)

theorem of_isPullback {A G U Z : Scheme.{u}} {φ : A ⟶ G} {f : A ⟶ U} {g : G ⟶ Z} {j : U ⟶ Z}
    [Surjective j] (h : IsPullback φ f g j) [GeometricallyConnected f] :
    GeometricallyConnected g := by
  refine ⟨fun K _ y W p q hW => ?_⟩
  obtain ⟨w⟩ : Nonempty ↥(pullback j y) :=
    ((pullback.snd j y).surjective (Classical.arbitrary _)).nonempty
  let r := (pullback j y).fromSpecResidueField w
  let a := r ≫ pullback.fst j y
  let b := r ≫ pullback.snd j y
  have hab : a ≫ j = b ≫ y := by simp [a, b, pullback.condition]
  have H : IsPullback (pullback.fst q b ≫ p) (pullback.snd q b) g (b ≫ y) :=
    (IsPullback.of_hasPullback q b).paste_horiz hW
  rw [← hab] at H
  have H' := IsPullback.of_right' H h
  have : ConnectedSpace ↥(pullback q b) :=
    GeometricallyConnected.geometrically_connectedSpace (f := f) a _ _ H'
  have hb : Surjective b := ⟨fun a => ⟨Classical.arbitrary _, Subsingleton.elim _ _⟩⟩
  exact (pullback.fst q b).surjective.connectedSpace (pullback.fst q b).continuous

theorem of_section {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
    [LocallyOfFiniteType f] [ConnectedSpace X] (s : Spec (.of k) ⟶ X) (hs : s ≫ f = 𝟙 _) :
    GeometricallyConnected f := by
  let y : Spec (.of (AlgebraicClosure k)) ⟶ Spec (.of k) :=
    Spec.map (CommRingCat.ofHom (algebraMap k (AlgebraicClosure k)))
  have hy : Surjective y := ⟨fun a => ⟨Classical.arbitrary _, Subsingleton.elim _ _⟩⟩
  have hi : IsIntegralHom y := by
    rw [IsIntegralHom.SpecMap_iff]
    exact algebraMap_isIntegral_iff.2 inferInstance
  have h := IsPullback.of_hasPullback f y
  have ho : UniversallyOpen (pullback.fst f y) := MorphismProperty.of_isPullback h.flip
    (inferInstance : UniversallyOpen y)
  have : PreconnectedSpace ↥(pullback f y) :=
    preconnectedSpace_of_fibre (pullback.fst f y).isOpenMap (pullback.fst f y).isClosedMap _
      (fibre_subsingleton h s hs)
  have : ConnectedSpace ↥(pullback f y) :=
    ⟨((pullback.fst f y).surjective (Classical.arbitrary X)).nonempty⟩
  have := of_isAlgClosed (pullback.snd f y)
  exact of_isPullback h

theorem geometricallyConnected_of_ratPoint :
    ∀ (k : Type) [Field k] (X : Over (Sp k)), LocallyOfFiniteType X.hom → QuasiCompact X.hom → ConnectedSpace X.left → Nonempty (𝟙_ (Over (Sp k)) ⟶ X) → GeometricallyConnected X.hom := by
  rintro k _ X _ - _ ⟨s⟩
  exact of_section (k := k) X.hom s.left (Over.w s)

end GlobalTheory.RatPointConn
