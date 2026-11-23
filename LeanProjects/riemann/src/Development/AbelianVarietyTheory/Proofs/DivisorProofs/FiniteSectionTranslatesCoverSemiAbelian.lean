import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.QuasiCompact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IrreducibleSpaceOfSmoothFieldOfConnectedSpace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChartSome
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitSectionNearClosedFibreDescendsToBaseStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSectionTranslateMemNearClosedFibreStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem mul_sec_left_eq {S : Scheme.{0}} (G : Over S) [GrpObj G] {Ω : Type} [Field Ω] (s : Sp Ω ⟶ S)
    (g : Over.mk s ⟶ G) (x : Over.mk (𝟙 S) ⟶ G) :
    (g * (Over.homMk s (by simp) : Over.mk s ⟶ Over.mk (𝟙 S)) ≫ x).left = g.left ≫ (transl x).left := by
  have h2 : g ≫ (Over.homMk G.hom (by simp) : G ⟶ Over.mk (𝟙 S)) = Over.homMk s (by simp) := by
    ext; exact Over.w g
  rw [← Over.comp_left, transl, MonObj.comp_mul, Category.comp_id, ← Category.assoc, h2]

theorem irreducibleSpace_fibre_of_semiAbelian {S : Scheme.{0}} (G' : Over S) [GrpObj G'] (hG : IsSemiAbelian G')
    (Ω : Type) [Field Ω] (s : Sp Ω ⟶ S) : IrreducibleSpace (pullback G'.hom s : Scheme.{0}) := by
  have : Smooth G'.hom := hG.smooth
  have : GeometricallyConnected G'.hom := hG.geomConnected
  have hc : ConnectedSpace (pullback G'.hom s : Scheme.{0}) :=
    GeometricallyConnected.geometrically_connectedSpace (f := G'.hom) s _ _ (IsPullback.of_hasPullback G'.hom s)
  exact GlobalTheory.irreducibleSpace_of_smooth_field_of_connectedSpace Ω _ (pullback.snd G'.hom s) inferInstance hc

theorem range_one_subset_near {R : Type} [CommRing R] [IsLocalRing R] {S : Scheme.{0}} (π : S ⟶ Sp R) (hπ : IsProper π)
    (G' : Over S) [GrpObj G'] (N : Near π G') :
    Set.range (1 : Over.mk (𝟙 S) ⟶ G').left ⊆ Set.range N.u := by
  have hW : IsOpen ((1 : Over.mk (𝟙 S) ⟶ G').left ⁻¹' Set.range N.u) :=
    N.isOpen.isOpen_range.preimage (1 : Over.mk (𝟙 S) ⟶ G').left.continuous
  have hcl : IsClosed (π '' ((1 : Over.mk (𝟙 S) ⟶ G').left ⁻¹' Set.range N.u)ᶜ) :=
    π.isClosedMap _ hW.isClosed_compl
  have hover : ∀ z : S, G'.hom ((1 : Over.mk (𝟙 S) ⟶ G').left z) = z := fun z => by
    have := Over.w (1 : Over.mk (𝟙 S) ⟶ G')
    change ((1 : Over.mk (𝟙 S) ⟶ G').left ≫ G'.hom) z = z
    rw [this]; rfl
  rintro _ ⟨z, rfl⟩
  by_contra hz
  have hmem : π z ∈ π '' ((1 : Over.mk (𝟙 S) ⟶ G').left ⁻¹' Set.range N.u)ᶜ := ⟨z, hz, rfl⟩
  obtain ⟨w, hw, hwc⟩ := (IsLocalRing.specializes_closedPoint (π z)).mem_closed hcl hmem
  apply hw
  apply N.all
  rw [hover]; exact hwc

theorem cover_by_translates : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (S : Scheme.{0}) (π : S ⟶ Sp R), IsProper π → Surjective π → IsIntegral S → ∀ (G' : Over S) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ N : Near π G', N.Law → ∃ (n : ℕ) (a : Fin n → (Sp R ⟶ N.U.left)) (x : Fin n → (Over.mk (𝟙 S) ⟶ G')), (∀ i, a i ≫ N.U.hom = 𝟙 _ ∧ N.Pt (𝟙 S) (π ≫ a i) (x i).left) ∧ ∀ (Ω : Type) [Field Ω] (s : Sp Ω ⟶ S) (g : Over.mk s ⟶ G'), Set.range g.left ⊆ Set.range N.u ∨ ∃ i, Set.range (g * (Over.homMk s (by simp) : Over.mk s ⟶ Over.mk (𝟙 S)) ≫ x i).left ⊆ Set.range N.u := by
  intro R _ _ _ hR S π hπ hs hS G' _ _ hG N hL
  obtain ⟨e, he, hPe⟩ := GlobalTheory.T.unitSection_near_closedFibre_descends_to_base R hR S π hπ hs hS G' hG N hL (range_one_subset_near π hπ G' N)
  have : CompactSpace S := QuasiCompact.compactSpace_of_compactSpace π
  have : QuasiCompact G'.hom := hG.quasiCompact
  have : CompactSpace G'.left := QuasiCompact.compactSpace_of_compactSpace G'.hom
  let Idx := {ax : (Sp R ⟶ N.U.left) × (Over.mk (𝟙 S) ⟶ G') // ax.1 ≫ N.U.hom = 𝟙 _ ∧ N.Pt (𝟙 S) (π ≫ ax.1) ax.2.left}
  let V : Idx → Set G'.left := fun i => Set.range N.u ∪ (transl i.1.2).left ⁻¹' Set.range N.u
  have hopen : IsOpen (Set.range N.u) := N.isOpen.isOpen_range
  have hV : ∀ i, IsOpen (V i) := fun i => hopen.union (hopen.preimage (transl _).left.continuous)
  have hcov : Set.univ ⊆ ⋃ i, V i := by
    intro p _
    by_cases hp : p ∈ Set.range N.u
    · exact Set.mem_iUnion.2 ⟨⟨(e, 1), he, hPe⟩, Or.inl hp⟩
    · have hfp : (G'.left.fromSpecResidueField p) (closedPoint _) = p := G'.left.fromSpecResidueField_apply p _
      have hnc : closedPoint R ∉ Set.range (G'.left.fromSpecResidueField p ≫ G'.hom ≫ π) := by
        rintro ⟨y, hy⟩
        apply hp
        apply N.all
        rw [← hy, Subsingleton.elim y (closedPoint _)]
        change π (G'.hom p) = π (G'.hom ((G'.left.fromSpecResidueField p) _))
        rw [hfp]
      obtain ⟨a, x, ha, hPa, hr⟩ := GlobalTheory.T.exists_section_translate_mem_near_closedFibre R hR S π G' hG N e he hPe (G'.left.residueField p)
        (G'.left.fromSpecResidueField p ≫ G'.hom) (Over.homMk (G'.left.fromSpecResidueField p) rfl)
        (irreducibleSpace_fibre_of_semiAbelian G' hG _ _) (by simpa [Category.assoc] using hnc)
      rw [mul_sec_left_eq] at hr
      refine Set.mem_iUnion.2 ⟨⟨(a, x), ha, hPa⟩, Or.inr ?_⟩
      have := hr ⟨closedPoint _, rfl⟩
      change (transl x).left ((G'.left.fromSpecResidueField p) (closedPoint _)) ∈ _ at this
      rwa [hfp] at this
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover V hV hcov
  refine ⟨t.card, fun k => (t.equivFin.symm k).1.1.1, fun k => (t.equivFin.symm k).1.1.2,
    fun k => (t.equivFin.symm k).1.2, ?_⟩
  intro Ω _ s g
  have hpt : ∀ y : Sp Ω, y = closedPoint Ω := fun y => Subsingleton.elim _ _
  obtain ⟨i, hit, hi⟩ := Set.mem_iUnion₂.1 (ht (Set.mem_univ (g.left (closedPoint Ω))))
  rcases hi with hi | hi
  · left
    rintro _ ⟨y, rfl⟩
    rw [hpt y]; exact hi
  · right
    refine ⟨t.equivFin ⟨i, hit⟩, ?_⟩
    simp only [Equiv.symm_apply_apply]
    rw [mul_sec_left_eq]
    rintro _ ⟨y, rfl⟩
    rw [hpt y]; exact hi

end GlobalTheory.Mum
