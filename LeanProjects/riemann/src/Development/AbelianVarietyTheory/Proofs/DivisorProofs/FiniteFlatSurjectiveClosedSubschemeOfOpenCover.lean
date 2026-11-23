import Mathlib
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem exists_isPullback_of_factor_iff {C : Type*} [Category C] {X X' A B : C} (m : X' ⟶ X)
    (b : B ⟶ X) (a : A ⟶ X') [Mono a] [Mono b]
    (h : ∀ (Y : C) (g : Y ⟶ X'), (∃ z : Y ⟶ B, z ≫ b = g ≫ m) ↔ (∃ z : Y ⟶ A, z ≫ a = g)) :
    ∃ k : A ⟶ B, IsPullback k a b m := by
  obtain ⟨k, hk⟩ := (h A a).2 ⟨𝟙 A, Category.id_comp a⟩
  refine ⟨k, ⟨hk⟩, ⟨PullbackCone.IsLimit.mk hk
    (fun s => ((h s.pt s.snd).1 ⟨s.fst, s.condition⟩).choose) ?_ ?_ ?_⟩⟩
  · intro s
    have hs := ((h s.pt s.snd).1 ⟨s.fst, s.condition⟩).choose_spec
    rw [← cancel_mono b, Category.assoc, hk, ← Category.assoc, hs, s.condition]
  · intro s
    exact ((h s.pt s.snd).1 ⟨s.fst, s.condition⟩).choose_spec
  · intro s l _ hl
    have hs := ((h s.pt s.snd).1 ⟨s.fst, s.condition⟩).choose_spec
    rw [← cancel_mono a, hl, hs]

theorem of_isPullback_openCover (P : MorphismProperty Scheme.{0}) [IsZariskiLocalAtTarget P]
    {B T : Scheme.{0}} (f : B ⟶ T) {ι : Type} (V : ι → T.Opens) (hV : iSup V = ⊤)
    (A : ι → Scheme.{0}) (k : ∀ i, A i ⟶ B) (g : ∀ i, A i ⟶ (V i).toScheme)
    (h : ∀ i, IsPullback (k i) (g i) f (V i).ι) (hg : ∀ i, P (g i)) : P f := by
  rw [IsZariskiLocalAtTarget.iff_of_iSup_eq_top (P := P) V hV]
  intro i
  have h' := (isPullback_morphismRestrict f (V i)).flip
  have e : (h'.isoIsPullback _ _ (h i)).hom ≫ g i = f ∣_ V i := by simp
  rw [← e]
  exact (P.cancel_left_of_respectsIso _ _).2 (hg i)

set_option backward.isDefEq.respectTransparency.types false in

theorem finite_flat_surjective_of_openCover : ∀ (X T₀ : Scheme.{0}) (p : X ⟶ T₀) (ι : Type) (V : ι → T₀.Opens), iSup V = ⊤ → ∀ (Xi : ι → Scheme.{0}) (m : ∀ i, Xi i ⟶ X) (q : ∀ i, Xi i ⟶ (V i).toScheme), (∀ i, IsPullback (m i) (q i) p (V i).ι) → ∀ (B : Scheme.{0}) (b : B ⟶ X), IsClosedImmersion b → ∀ (A : ι → Scheme.{0}) (a : ∀ i, A i ⟶ Xi i), (∀ i, IsClosedImmersion (a i)) → (∀ (i : ι) (Y : Scheme.{0}) (g : Y ⟶ Xi i), (∃ z : Y ⟶ B, z ≫ b = g ≫ m i) ↔ (∃ z : Y ⟶ A i, z ≫ a i = g)) → (∀ i, IsFinite (a i ≫ q i) ∧ Flat (a i ≫ q i) ∧ Surjective (a i ≫ q i)) → IsFinite (b ≫ p) ∧ Flat (b ≫ p) ∧ Surjective (b ≫ p) := by
  intro X T₀ p ι V hV Xi m q hpb B b hb A a ha hrep hP
  have H : ∀ i, ∃ k : A i ⟶ B, IsPullback k (a i ≫ q i) (b ≫ p) (V i).ι := by
    intro i
    have := ha i
    obtain ⟨k, hk⟩ := exists_isPullback_of_factor_iff (m i) b (a i) (hrep i)
    exact ⟨k, hk.paste_vert (hpb i)⟩
  choose k hk using H
  have hfin : IsZariskiLocalAtTarget @IsFinite.{0} :=
    inferInstance
  have hflat : IsZariskiLocalAtTarget @Flat.{0} :=
    HasRingHomProperty.instIsZariskiLocalAtTarget (P := @Flat.{0})
  exact ⟨of_isPullback_openCover @IsFinite _ V hV A k _ hk (fun i => (hP i).1),
    of_isPullback_openCover @Flat _ V hV A k _ hk (fun i => (hP i).2.1),
    of_isPullback_openCover @Surjective _ V hV A k _ hk (fun i => (hP i).2.2)⟩

end GlobalTheory
