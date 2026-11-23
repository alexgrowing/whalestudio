import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChartSome
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.GlueCopies

theorem desc_of_compat (D : Scheme.GlueData.{0}) {S : Scheme.{0}} (p : ∀ i, D.U i ⟶ S)
    (h : ∀ i j, D.f i j ≫ p i = (D.t i j ≫ D.f j i) ≫ p j) :
    ∃ F : D.glued ⟶ S, ∀ i, D.ι i ≫ F = p i :=
  ⟨Multicoequalizer.desc D.toGlueData.diagram S p (by rintro ⟨i, j⟩; exact h i j),
    fun i => Multicoequalizer.π_desc _ _ _ _ _⟩

theorem exists_glue_copies : ∀ (Y : Scheme.{0}) (J : Type) (V : J → J → Y.Opens) (τ : ∀ i j, (V i j).toScheme ⟶ Y), (∀ i, V i i = ⊤) → (∀ i, τ i i = (V i i).ι) → (∀ (i j k : J) (x : (V i j).toScheme), (V i j).ι x ∈ V i k → τ i j x ∈ V j k) → (∀ (i j k : J) (T : Scheme.{0}) (x : T ⟶ (V i j).toScheme) (y : T ⟶ (V i k).toScheme) (w : T ⟶ (V j k).toScheme), x ≫ (V i j).ι = y ≫ (V i k).ι → x ≫ τ i j = w ≫ (V j k).ι → w ≫ τ j k = y ≫ τ i k) → ∃ (G : Scheme.{0}) (ψ : J → (Y ⟶ G)), (∀ j, IsOpenImmersion (ψ j)) ∧ (∀ g : G, ∃ j, g ∈ Set.range (ψ j)) ∧ (∀ i j, IsPullback (V i j).ι (τ i j) (ψ i) (ψ j)) ∧ ∀ (Z : Scheme.{0}) (g : J → (Y ⟶ Z)), (∀ i j, (V i j).ι ≫ g i = τ i j ≫ g j) → ∃ F : G ⟶ Z, ∀ j, ψ j ≫ F = g j := by
  intro Y J V τ hV hτ hr hc
  have mem_of : ∀ (U : Y.Opens) {T : Scheme.{0}} (f : T ⟶ U.toScheme) (p : T), (f ≫ U.ι) p ∈ U :=
    fun U T f p => by
      have h := Set.mem_range_self (f := ⇑U.ι) (f p)
      rw [Scheme.Opens.range_ι] at h
      rw [Scheme.Hom.comp_apply]; exact h
  have hs : ∀ i, ∃ s : Y ⟶ (V i i).toScheme, s ≫ (V i i).ι = 𝟙 _ := fun i =>
    ⟨IsOpenImmersion.lift (V i i).ι (𝟙 _) (by
      rw [Scheme.Opens.range_ι, hV]; intro x _; simp), IsOpenImmersion.lift_fac _ _ _⟩
  choose s hs using hs
  have ht : ∀ i j, ∃ t : (V i j).toScheme ⟶ (V j i).toScheme, t ≫ (V j i).ι = τ i j := fun i j =>
    ⟨IsOpenImmersion.lift (V j i).ι (τ i j) (by
      rintro _ ⟨x, rfl⟩
      rw [Scheme.Opens.range_ι]
      exact hr i j i x (by rw [hV]; simp)), IsOpenImmersion.lift_fac _ _ _⟩
  choose t ht using ht
  have htb : ∀ i j, t i j ≫ τ j i = (V i j).ι := fun i j => by
    have h1 := hc i j i _ (𝟙 _) ((V i j).ι ≫ s i) (t i j) (by simp [hs]) (by simp [ht])
    rw [h1, hτ, Category.assoc, hs, Category.comp_id]
  have hu : ∀ i j k, ∃ u : pullback (V i j).ι (V i k).ι ⟶ (V j k).toScheme,
      u ≫ (V j k).ι = pullback.fst _ _ ≫ τ i j := fun i j k =>
    ⟨IsOpenImmersion.lift (V j k).ι (pullback.fst _ _ ≫ τ i j) (by
      rintro _ ⟨p, rfl⟩
      rw [Scheme.Opens.range_ι, Scheme.Hom.comp_apply]
      apply hr i j k
      rw [← Scheme.Hom.comp_apply, pullback.condition]
      exact mem_of _ _ _), IsOpenImmersion.lift_fac _ _ _⟩
  choose u hu using hu
  have hub : ∀ i j k, u i j k ≫ τ j k = pullback.snd _ _ ≫ τ i k := fun i j k =>
    hc i j k _ (pullback.fst _ _) (pullback.snd _ _) (u i j k) pullback.condition (hu i j k).symm
  let D : Scheme.GlueData.{0} :=
    { J := J
      U := fun _ => Y
      V := fun p => (V p.1 p.2).toScheme
      f := fun i j => (V i j).ι
      f_mono := fun i j => inferInstance
      f_id := fun i => ⟨s i, by rw [← cancel_mono (V i i).ι, Category.assoc, hs]; simp, hs i⟩
      t := t
      t_id := fun i => by rw [← cancel_mono (V i i).ι, ht, hτ, Category.id_comp]
      t' := fun i j k => pullback.lift (u i j k) (pullback.fst _ _ ≫ t i j) (by simp [hu, ht])
      t_fac := fun i j k => pullback.lift_snd _ _ _
      cocycle := fun i j k => by
        rw [← cancel_mono (pullback.fst (V i j).ι (V i k).ι), ← cancel_mono (V i j).ι]
        simp only [Category.assoc, pullback.lift_fst_assoc, hu, hub, pullback.lift_snd_assoc, htb,
          Category.id_comp]
      f_open := fun i j => inferInstance }
  have hP : ∀ i j, IsPullback (V i j).ι (τ i j) (D.ι i) (D.ι j) := fun i j => by
    rw [← ht]
    exact IsPullback.of_isLimit (D.vPullbackConeIsLimit i j)
  refine ⟨D.glued, D.ι, fun j => D.ι_isOpenImmersion j, fun g => ?_, hP, fun Z g hg => ?_⟩
  · obtain ⟨j, y, rfl⟩ := D.ι_jointly_surjective g
    exact ⟨j, y, rfl⟩
  · refine desc_of_compat D g fun i j => ?_
    change (V i j).ι ≫ g i = (t i j ≫ (V j i).ι) ≫ g j
    rw [ht, hg]

end GlobalTheory.GlueCopies
