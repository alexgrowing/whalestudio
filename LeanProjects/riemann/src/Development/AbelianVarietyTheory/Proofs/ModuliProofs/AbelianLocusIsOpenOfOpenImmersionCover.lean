import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.OneArc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbProj
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GtBaseChangeSt
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.TopAmpExists
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.HasFramesOfAmpFrames

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models GlobalTheory.ModelSum

namespace GlobalTheory.AbLocusLocal

private theorem isProper_of_isPullback_of_pullback_snd {A B C D : Scheme.{0}} {fst : A ⟶ B} {snd : A ⟶ C} {f : B ⟶ D}
    {g : C ⟶ D} (h : IsPullback fst snd f g) (H : IsProper (pullback.snd f g)) : IsProper snd := by
  rw [← h.isoPullback_hom_snd]
  exact (MorphismProperty.cancel_left_of_respectsIso @IsProper h.isoPullback.hom (pullback.snd f g)).2 H

private theorem isProper_pullback_snd_of_isPullback {A B C D : Scheme.{0}} {fst : A ⟶ B} {snd : A ⟶ C} {f : B ⟶ D}
    {g : C ⟶ D} (h : IsPullback fst snd f g) (H : IsProper snd) : IsProper (pullback.snd f g) := by
  rw [← h.isoPullback_inv_snd]
  exact (MorphismProperty.cancel_left_of_respectsIso @IsProper h.isoPullback.inv snd).2 H

private theorem isProper_snd_of_isPullback_of_isProper {A B C D : Scheme.{0}} {fst : A ⟶ B} {snd : A ⟶ C} {f : B ⟶ D}
    {g : C ⟶ D} (h : IsPullback fst snd f g) (hf : IsProper f) : IsProper snd :=
  isProper_of_isPullback_of_pullback_snd h inferInstance

theorem isProper_restrict_of_cover {X Z : Scheme.{0}} (p : X ⟶ Z) {I : Type} {Y X' : I → Scheme.{0}}
    (f : ∀ i, Y i ⟶ Z) [∀ i, IsOpenImmersion (f i)] (p' : ∀ i, X' i ⟶ Y i) (F : ∀ i, X' i ⟶ X)
    (h : ∀ i, IsPullback (F i) (p' i) p (f i)) (V : ∀ i, (Y i).Opens) (hV : ∀ i, IsProper (p' i ∣_ V i))
    (U : Z.Opens) (hle : ∀ i, Set.range ((V i).ι ≫ f i) ⊆ Set.range U.ι)
    (hc : ∀ z ∈ U, ∃ i, z ∈ Set.range ((V i).ι ≫ f i)) : IsProper (p ∣_ U) := by
  have hsq : ∀ i, IsPullback (((p' i) ⁻¹ᵁ V i).ι ≫ F i) (p' i ∣_ V i) p ((V i).ι ≫ f i) := fun i =>
    (isPullback_morphismRestrict (p' i) (V i)).flip.paste_horiz (h i)
  refine IsZariskiLocalAtTarget.of_iSup_eq_top (fun i => U.ι ⁻¹ᵁ ((V i).ι ≫ f i).opensRange) ?_ ?_
  · rw [eq_top_iff]
    intro x _
    rw [TopologicalSpace.Opens.mem_iSup]
    obtain ⟨i, hi⟩ := hc (U.ι x) x.2
    exact ⟨i, by simpa [Scheme.Hom.coe_opensRange] using hi⟩
  · intro i
    let W : U.toScheme.Opens := U.ι ⁻¹ᵁ ((V i).ι ≫ f i).opensRange
    have hr : Set.range (W.ι ≫ U.ι) ⊆ Set.range ((V i).ι ≫ f i) := by
      rintro _ ⟨x, rfl⟩
      have hx : U.ι x.val ∈ ((V i).ι ≫ f i).opensRange := x.2
      rw [← SetLike.mem_coe, Scheme.Hom.coe_opensRange] at hx
      exact hx
    let e := IsOpenImmersion.lift ((V i).ι ≫ f i) (W.ι ≫ U.ι) hr
    have he : e ≫ ((V i).ι ≫ f i) = W.ι ≫ U.ι := IsOpenImmersion.lift_fac _ _ _
    have big := (isPullback_morphismRestrict (p ∣_ U) W).flip.paste_horiz (isPullback_morphismRestrict p U).flip
    rw [← he] at big
    have hw : ((((p ∣_ U) ⁻¹ᵁ W).ι ≫ (p ⁻¹ᵁ U).ι)) ≫ p = ((p ∣_ U) ∣_ W ≫ e) ≫ ((V i).ι ≫ f i) := by
      rw [big.w, Category.assoc]
    have sq : IsPullback ((hsq i).lift _ _ hw) ((p ∣_ U) ∣_ W) (p' i ∣_ V i) e := by
      refine IsPullback.of_right ?_ ((hsq i).lift_snd _ _ hw) (hsq i)
      rw [(hsq i).lift_fst]
      exact big
    exact isProper_snd_of_isPullback_of_isProper sq (hV i)

private theorem mem_abLocus_of_map_mem_of_isPullback {Y Z : Scheme.{0}} {A : Over Y} {B : Over Z} {g : Y ⟶ Z}
    {φ : A.left ⟶ B.left} (h : IsPullback φ A.hom B.hom g) (y : Y) (hy : g y ∈ abLocus B) :
    y ∈ abLocus A := by
  simp only [abLocus, Set.mem_setOf_eq] at hy ⊢
  intro K _ _ s hs
  obtain ⟨x, rfl⟩ := hs
  have big := (IsPullback.of_hasPullback A.hom s).paste_horiz h
  exact isProper_of_isPullback_of_pullback_snd big (hy K (s ≫ g) ⟨x, by rw [Scheme.Hom.comp_apply]⟩)

private theorem map_mem_abLocus_of_isPullback {Y Z : Scheme.{0}} {A : Over Y} {B : Over Z} {g : Y ⟶ Z}
    [IsOpenImmersion g] {φ : A.left ⟶ B.left} (h : IsPullback φ A.hom B.hom g) (y : Y)
    (hy : y ∈ abLocus A) : g y ∈ abLocus B := by
  simp only [abLocus, Set.mem_setOf_eq] at hy ⊢
  intro K _ _ s hs
  obtain ⟨x0, hx0⟩ := hs
  have hr : Set.range s ⊆ Set.range g := by
    rintro _ ⟨x, rfl⟩
    rw [Subsingleton.elim x x0, hx0]
    exact ⟨y, rfl⟩
  have hs' : IsOpenImmersion.lift g s hr ≫ g = s := IsOpenImmersion.lift_fac g s hr
  have big := (IsPullback.of_hasPullback A.hom (IsOpenImmersion.lift g s hr)).paste_horiz h
  rw [hs'] at big
  have hy' : y ∈ Set.range (IsOpenImmersion.lift g s hr) := by
    refine ⟨x0, g.isOpenEmbedding.injective ?_⟩
    rw [← Scheme.Hom.comp_apply, hs', hx0]
  exact isProper_pullback_snd_of_isPullback big (hy K _ hy')

theorem abOpen_of_cover : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Z : Scheme.{0}) (t : SAB H Z) (I : Type) (Y : I → Scheme.{0}) (f : ∀ i, Y i ⟶ Z) (u : ∀ i, SAB H (Y i)) (_ : ∀ i, SABMap (u i) t (f i)), (∀ i, IsOpenImmersion (f i)) → (∀ z : Z, ∃ i, z ∈ Set.range (f i)) → (∀ i, AbOpen (u i).G) → AbOpen t.G := by
  intro E _ _ _ H Z t I Y f u m hf hc hab
  unfold AbOpen at hab ⊢
  choose V hVs hVp using hab
  have hpb : ∀ i, IsPullback (m i).φ (u i).G.hom t.G.hom (f i) := fun i => (m i).cart.1
  refine ⟨⨆ i, ((V i).ι ≫ f i).opensRange, ?_, ?_⟩
  · ext z
    simp only [TopologicalSpace.Opens.coe_iSup, Set.mem_iUnion, Scheme.Hom.coe_opensRange]
    constructor
    · rintro ⟨i, v, rfl⟩
      rw [Scheme.Hom.comp_apply]
      exact map_mem_abLocus_of_isPullback (hpb i) _ (by rw [← hVs i]; exact v.2)
    · intro hz
      obtain ⟨i, y, rfl⟩ := hc z
      have hy := mem_abLocus_of_map_mem_of_isPullback (hpb i) y hz
      rw [← hVs i] at hy
      exact ⟨i, ⟨y, hy⟩, rfl⟩
  · refine isProper_restrict_of_cover t.G.hom f (fun i => (u i).G.hom) _ hpb V hVp _ ?_ ?_
    · intro i z hz
      rw [Scheme.Opens.range_ι]
      exact TopologicalSpace.Opens.mem_iSup.2 ⟨i, by rw [← SetLike.mem_coe, Scheme.Hom.coe_opensRange]; exact hz⟩
    · intro z hz
      obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 hz
      rw [← SetLike.mem_coe, Scheme.Hom.coe_opensRange] at hi
      exact ⟨i, hi⟩

end GlobalTheory.AbLocusLocal
