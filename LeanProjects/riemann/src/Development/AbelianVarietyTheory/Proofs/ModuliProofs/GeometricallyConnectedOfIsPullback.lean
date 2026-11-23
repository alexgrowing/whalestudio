import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Splits
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GtBaseChangeSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbProj
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.OneArc

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise

namespace GlobalTheory.SemiAbelianDescent

theorem exists_section {Z : Scheme.{0}} {Ω : Type} [Field Ω] [IsAlgClosed Ω]
    (f : Z ⟶ Spec (CommRingCat.of Ω)) [IsIntegralHom f] [Surjective f] :
    ∃ s : Spec (CommRingCat.of Ω) ⟶ Z, s ≫ f = 𝟙 _ := by
  have : IsAffine Z := isAffine_of_isAffineHom f
  have : Nonempty Z := ⟨(f.surjective (Nonempty.some inferInstance)).choose⟩
  obtain ⟨z, -, hz⟩ := (isClosed_univ (X := Z)).exists_closed_singleton Set.univ_nonempty
  rw [isClosed_singleton_iff_isClosedImmersion] at hz
  set g : Spec (Z.residueField z) ⟶ Spec (CommRingCat.of Ω) := Z.fromSpecResidueField z ≫ f with hg
  have : IsIntegralHom g := inferInstance
  have : IsIso (Spec.preimage g) := by
    rw [ConcreteCategory.isIso_iff_bijective]
    refine IsAlgClosed.ringHom_bijective_of_isIntegral _ ?_
    rw [← IsIntegralHom.SpecMap_iff, Spec.map_preimage]
    infer_instance
  refine ⟨Spec.map (inv (Spec.preimage g)) ≫ Z.fromSpecResidueField z, ?_⟩
  calc (Spec.map (inv (Spec.preimage g)) ≫ Z.fromSpecResidueField z) ≫ f
      = Spec.map (inv (Spec.preimage g)) ≫ Spec.map (Spec.preimage g) := by
        rw [Category.assoc, Spec.map_preimage]
    _ = 𝟙 _ := by rw [← Spec.map_comp, IsIso.hom_inv_id, Spec.map_id]

theorem exists_lift {X X' : Scheme.{0}} (π : X ⟶ X') [IsIntegralHom π] [Surjective π]
    {Ω : Type} [Field Ω] [IsAlgClosed Ω] (p : Spec (CommRingCat.of Ω) ⟶ X') :
    ∃ q : Spec (CommRingCat.of Ω) ⟶ X, q ≫ π = p := by
  obtain ⟨s, hs⟩ := exists_section (pullback.snd π p)
  refine ⟨s ≫ pullback.fst π p, ?_⟩
  rw [Category.assoc, pullback.condition, ← Category.assoc, hs, Category.id_comp]

private theorem isClosed_range_diagonal_of_surjective_universallyClosed {X Y S : Scheme.{0}} (j : X ⟶ Y) (f : Y ⟶ S) [Surjective j]
    {P : Scheme.{0}} (m : P ⟶ Limits.pullback f f) [UniversallyClosed m] (d : X ⟶ P)
    (hd : IsClosed (Set.range d)) (hc : d ≫ m = j ≫ pullback.diagonal f) :
    IsClosed (Set.range (pullback.diagonal f)) := by
  have key : Set.range (pullback.diagonal f) = m '' Set.range d := by
    ext z
    constructor
    · rintro ⟨y, rfl⟩
      obtain ⟨x, rfl⟩ := j.surjective y
      exact ⟨d x, ⟨x, rfl⟩, by rw [← Scheme.Hom.comp_apply, hc, Scheme.Hom.comp_apply]⟩
    · rintro ⟨_, ⟨x, rfl⟩, rfl⟩
      exact ⟨j x, by rw [← Scheme.Hom.comp_apply, ← hc, Scheme.Hom.comp_apply]⟩
  rw [key]
  exact m.isClosedMap _ hd

theorem isSeparated_of_comp {X Y S : Scheme.{0}} (j : X ⟶ Y) (f : Y ⟶ S)
    [Surjective j] [UniversallyClosed j] [IsSeparated (j ≫ f)] : IsSeparated f := by
  have hm := MorphismProperty.pullbackMap (P := @UniversallyClosed) (f := j ≫ f) (g := j ≫ f)
    (f' := f) (g' := f) (i₁ := j) (i₂ := j) ‹UniversallyClosed j› ‹UniversallyClosed j› rfl rfl
  have hcl := isClosed_range_diagonal_of_surjective_universallyClosed j f
    (pullback.map (j ≫ f) (j ≫ f) f f j j (𝟙 _) (Category.comp_id _) (Category.comp_id _)) (pullback.diagonal (j ≫ f))
    (pullback.diagonal (j ≫ f)).isClosedEmbedding.isClosed_range (pullback.comp_diagonal j f).symm
  exact ⟨IsClosedImmersion.of_isPreimmersion _ hcl⟩

theorem quasiCompact_of_comp {X Y S : Scheme.{0}} (j : X ⟶ Y) (f : Y ⟶ S)
    [Surjective j] [QuasiCompact (j ≫ f)] : QuasiCompact f := by
  refine ⟨fun U hU hU' => ?_⟩
  have h := (QuasiCompact.isCompact_preimage (f := j ≫ f) U hU hU').image j.continuous
  convert h using 1
  ext x
  constructor
  · intro hx
    obtain ⟨y, rfl⟩ := j.surjective x
    exact ⟨y, by simpa using hx, rfl⟩
  · rintro ⟨y, hy, rfl⟩
    simpa using hy

theorem geometricallyConnected_of_isPullback {X X' Y Y' : Scheme.{0}} {π : X ⟶ X'} [IsIntegralHom π]
    [Surjective π] {f : Y ⟶ X} {f' : Y' ⟶ X'} {φ : Y ⟶ Y'} (h : IsPullback φ f f' π)
    [GeometricallyConnected f] : GeometricallyConnected f' := by
  refine ⟨geometrically_iff_of_isClosedUnderIsomorphisms.mpr fun K _ y => ?_⟩
  let ιK : Spec (CommRingCat.of (AlgebraicClosure K)) ⟶ Spec (CommRingCat.of K) :=
    Spec.map (CommRingCat.ofHom (algebraMap K (AlgebraicClosure K)))
  obtain ⟨q, hq⟩ := exists_lift π (ιK ≫ y)
  have hA : ConnectedSpace ↥(pullback f q) :=
    GeometricallyConnected.geometrically_connectedSpace _ _ _ (.of_hasPullback _ _)
  have hιK : Surjective ιK := ⟨fun x => ⟨Nonempty.some inferInstance, Subsingleton.elim _ _⟩⟩
  let M := (IsPullback.paste_horiz (IsPullback.of_hasPullback f q) h).isoPullback.hom ≫
    (pullback.congrHom rfl hq).hom ≫ (pullbackLeftPullbackSndIso f' y ιK).inv ≫
      pullback.fst (pullback.snd f' y) ιK
  have hM : Surjective M := by dsimp only [M]; infer_instance
  exact M.surjective.connectedSpace M.continuous

theorem isSemiAbelian_descends {X X' : Scheme.{0}} {π : X ⟶ X'} {G : Over X} [GrpObj G] {G' : Over X'}
    [GrpObj G'] [IsCommMonObj G'] {φ : G.left ⟶ G'.left} [IsIntegralHom π] [Surjective π]
    (h : IsGrpPullback G G' π φ) [Smooth G'.hom] (hG : IsSemiAbelian G) : IsSemiAbelian G' := by
  obtain ⟨hc, hsm, hsep, hqc, hgc, hfib⟩ := hG
  have hpb : IsPullback φ G.hom G'.hom π := h.1
  have hφi : IsIntegralHom φ := MorphismProperty.of_isPullback hpb.flip ‹IsIntegralHom π›
  have hφs : Surjective φ := MorphismProperty.of_isPullback hpb.flip ‹Surjective π›
  have hw : φ ≫ G'.hom = G.hom ≫ π := hpb.w
  have hsep' : IsSeparated G'.hom := by
    have : IsSeparated (φ ≫ G'.hom) := by rw [hw]; infer_instance
    exact isSeparated_of_comp φ G'.hom
  have hqc' : QuasiCompact G'.hom := by
    have : QuasiCompact (φ ≫ G'.hom) := by rw [hw]; infer_instance
    exact quasiCompact_of_comp φ G'.hom
  have hgc' : GeometricallyConnected G'.hom := geometricallyConnected_of_isPullback hpb
  refine ⟨‹_›, ‹_›, hsep', hqc', hgc', ?_⟩
  intro Ω _ _ p
  obtain ⟨q, hq⟩ := exists_lift π p
  obtain ⟨T⟩ := hfib Ω q
  have h1 := isGrpPullback_pullback G q
  have h2 := IsGrpPullback.comp h1 h
  have h3 := isGrpPullback_pullback G' p
  obtain ⟨e, he, -⟩ := grpPullback_iso (h2.congr hq rfl) h3
  exact ⟨torusExtOfIso e T⟩

theorem main : ∀ (X X' : Scheme.{0}) (π : X ⟶ X') (G : Over X) [GrpObj G] (G' : Over X') [GrpObj G'] [IsCommMonObj G'] (φ : G.left ⟶ G'.left), IsIntegralHom π → Surjective π → IsGrpPullback G G' π φ → Smooth G'.hom → IsSemiAbelian G → IsSemiAbelian G' ∧ ((∃ U : X.Opens, (U : Set X) = abLocus G ∧ IsProper (G.hom ∣_ U)) → (∃ U : X'.Opens, (U : Set X') = abLocus G' ∧ IsProper (G'.hom ∣_ U))) := by
  intro X X' π G _ G' _ _ φ hi hs h hsm hG
  have hG' : IsSemiAbelian G' := isSemiAbelian_descends h hG
  refine ⟨hG', ?_⟩
  rintro ⟨U, hU, hP⟩
  have hloc : ∀ x, π x ∈ abLocus G' ↔ x ∈ abLocus G := abLocus_pullback abLocusOne hG' h.1
  have hV : IsOpen (abLocus G') := by
    have hc : (abLocus G')ᶜ = π '' (U : Set X)ᶜ := by
      ext y
      obtain ⟨x, rfl⟩ := π.surjective y
      constructor
      · intro hy
        refine ⟨x, ?_, rfl⟩
        rw [Set.mem_compl_iff, hU, ← hloc]
        exact hy
      · rintro ⟨x', hx', hxx⟩
        rw [Set.mem_compl_iff, ← hxx, hloc, ← hU]
        exact hx'
    rw [← isClosed_compl_iff, hc]
    exact π.isClosedMap _ U.isOpen.isClosed_compl
  let V' : X'.Opens := ⟨abLocus G', hV⟩
  have hpre : π ⁻¹ᵁ V' = U := by
    ext x
    change π x ∈ abLocus G' ↔ x ∈ (U : Set X)
    rw [hU, hloc]
  rw [← hpre] at hP
  have hpb : IsPullback φ G.hom G'.hom π := h.1
  have hw : φ ≫ G'.hom = G.hom ≫ π := hpb.w
  have hφs : Surjective φ := MorphismProperty.of_isPullback hpb.flip ‹Surjective π›
  have hle : G.hom ⁻¹ᵁ (π ⁻¹ᵁ V') ≤ φ ⁻¹ᵁ (G'.hom ⁻¹ᵁ V') := by
    intro x hx
    change G'.hom (φ x) ∈ V'
    rw [← Scheme.Hom.comp_apply, hw, Scheme.Hom.comp_apply]
    exact hx
  let a := φ.resLE (G'.hom ⁻¹ᵁ V') (G.hom ⁻¹ᵁ (π ⁻¹ᵁ V')) hle
  have heq : a ≫ (G'.hom ∣_ V') = (G.hom ∣_ (π ⁻¹ᵁ V')) ≫ (π ∣_ V') := by
    rw [← cancel_mono V'.ι]
    simp only [a, Category.assoc, morphismRestrict_ι, morphismRestrict_ι_assoc,
      Scheme.Hom.resLE_comp_ι_assoc, hw]
  have ha : Surjective a := by
    constructor
    intro z
    obtain ⟨w, hw'⟩ := φ.surjective ((G'.hom ⁻¹ᵁ V').ι z)
    have hz : (G'.hom ⁻¹ᵁ V').ι z ∈ ((G'.hom ⁻¹ᵁ V' : G'.left.Opens) : Set G'.left) := by
      rw [← Scheme.Opens.range_ι (G'.hom ⁻¹ᵁ V')]
      exact ⟨z, rfl⟩
    have hm : w ∈ Set.range (G.hom ⁻¹ᵁ (π ⁻¹ᵁ V')).ι := by
      rw [Scheme.Opens.range_ι]
      change π (G.hom w) ∈ V'
      rw [← Scheme.Hom.comp_apply, ← hw, Scheme.Hom.comp_apply, hw']
      exact hz
    obtain ⟨w', rfl⟩ := hm
    refine ⟨w', (G'.hom ⁻¹ᵁ V').ι.isOpenEmbedding.injective ?_⟩
    rw [← Scheme.Hom.comp_apply, Scheme.Hom.resLE_comp_ι, Scheme.Hom.comp_apply, hw']
  have hsep : IsSeparated G'.hom := hG'.separated
  have hcomp : UniversallyClosed (a ≫ (G'.hom ∣_ V')) := by
    rw [heq]
    infer_instance
  have huc : UniversallyClosed (G'.hom ∣_ V') := UniversallyClosed.of_comp_surjective a _
  exact ⟨V', rfl, by constructor⟩

end GlobalTheory.SemiAbelianDescent
