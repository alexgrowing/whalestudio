import Mathlib
import Development.AutomorphicArithmetic.RepresentationRank.RepOfRank

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory

namespace UpperTheory.ClopSum

variable {S : Scheme.{0}}

private theorem isPullback_wl (T : Over S) {A B : Over S} (i : A ⟶ B) :
    IsPullback (T ◁ i).left (snd T A).left (snd T B).left i.left := by
  have eq1 : (T ◁ i).left ≫ (fst T B).left = (fst T A).left := Over.whiskerLeft_left_fst i
  have eq2 : i.left ≫ B.hom = A.hom := Over.w i
  have s : IsPullback ((T ◁ i).left ≫ (fst T B).left) (snd T A).left T.hom (i.left ≫ B.hom) := by
    rw [eq1, eq2]
    exact IsPullback.of_hasPullback T.hom A.hom
  exact IsPullback.of_right s (Over.whiskerLeft_left_snd i) (IsPullback.of_hasPullback T.hom B.hom)

private theorem range_wl (T : Over S) {A B : Over S} (i : A ⟶ B) :
    Set.range (T ◁ i).left = (snd T B).left ⁻¹' Set.range i.left := by
  have h := isPullback_wl T i
  rw [← Scheme.Pullback.range_fst, ← h.isoPullback_hom_fst]
  ext x
  constructor
  · rintro ⟨a, rfl⟩
    exact ⟨h.isoPullback.hom a, rfl⟩
  · rintro ⟨b, rfl⟩
    refine ⟨h.isoPullback.inv b, ?_⟩
    show (h.isoPullback.inv ≫ h.isoPullback.hom ≫ pullback.fst _ _) b = _
    rw [Iso.inv_hom_id_assoc]

private theorem opens_ext {C A₁ A₂ : Scheme.{0}} (j₁ : A₁ ⟶ C) (j₂ : A₂ ⟶ C)
    (hr : Set.range j₁ = (Set.range j₂)ᶜ) {V V' : C.Opens}
    (h₁ : j₁ ⁻¹ᵁ V = j₁ ⁻¹ᵁ V') (h₂ : j₂ ⁻¹ᵁ V = j₂ ⁻¹ᵁ V') : V = V' := by
  ext x
  by_cases hx : x ∈ Set.range j₁
  · obtain ⟨a, rfl⟩ := hx
    have := SetLike.ext_iff.mp h₁ a
    simpa using this
  · have hx2 : x ∈ Set.range j₂ := by
      rw [hr] at hx
      simpa using hx
    obtain ⟨b, rfl⟩ := hx2
    have := SetLike.ext_iff.mp h₂ b
    simpa using this

private theorem glue {C A₁ A₂ : Scheme.{0}} (j₁ : A₁ ⟶ C) (j₂ : A₂ ⟶ C)
    [IsOpenImmersion j₁] [IsOpenImmersion j₂] (hr : Set.range j₁ = (Set.range j₂)ᶜ)
    (V₁ : A₁.Opens) (V₂ : A₂.Opens) (h₁ : IsClosed (V₁ : Set A₁)) (h₂ : IsClosed (V₂ : Set A₂)) :
    ∃ V : C.Opens, IsClosed (V : Set C) ∧ j₁ ⁻¹ᵁ V = V₁ ∧ j₂ ⁻¹ᵁ V = V₂ := by
  have hc1 : IsClosed (Set.range j₁) := by
    rw [hr]
    exact j₂.isOpenEmbedding.isOpen_range.isClosed_compl
  have hc2 : IsClosed (Set.range j₂) := by
    have e : Set.range j₂ = (Set.range j₁)ᶜ := by rw [hr, compl_compl]
    rw [e]
    exact j₁.isOpenEmbedding.isOpen_range.isClosed_compl
  have e1 : Topology.IsClosedEmbedding j₁ := ⟨j₁.isOpenEmbedding.isEmbedding, hc1⟩
  have e2 : Topology.IsClosedEmbedding j₂ := ⟨j₂.isOpenEmbedding.isEmbedding, hc2⟩
  have hopen : IsOpen (j₁ '' (V₁ : Set A₁) ∪ j₂ '' (V₂ : Set A₂)) :=
    (j₁.isOpenEmbedding.isOpenMap _ V₁.isOpen).union (j₂.isOpenEmbedding.isOpenMap _ V₂.isOpen)
  refine ⟨⟨_, hopen⟩, (e1.isClosedMap _ h₁).union (e2.isClosedMap _ h₂), ?_, ?_⟩
  · ext a
    show j₁ a ∈ j₁ '' (V₁ : Set A₁) ∪ j₂ '' (V₂ : Set A₂) ↔ a ∈ V₁
    constructor
    · rintro (⟨a', ha', he⟩ | ⟨b, hb, he⟩)
      · rw [← j₁.isOpenEmbedding.injective he]
        exact ha'
      · exfalso
        have hm : j₁ a ∈ Set.range j₁ := ⟨a, rfl⟩
        rw [hr] at hm
        exact hm ⟨b, he⟩
    · intro ha
      exact Or.inl ⟨a, ha, rfl⟩
  · ext b
    show j₂ b ∈ j₁ '' (V₁ : Set A₁) ∪ j₂ '' (V₂ : Set A₂) ↔ b ∈ V₂
    constructor
    · rintro (⟨a, ha, he⟩ | ⟨b', hb', he⟩)
      · exfalso
        have hm : j₂ b ∈ Set.range j₁ := ⟨a, he⟩
        rw [hr] at hm
        exact hm ⟨b, rfl⟩
      · rw [← j₂.isOpenEmbedding.injective he]
        exact hb'
    · intro hb
      exact Or.inr ⟨b, hb, rfl⟩

end UpperTheory.ClopSum

private theorem UpperTheory.preimage_comp_scheme_opens {X Y Z : Scheme.{0}} (f : X ⟶ Y) (g : Y ⟶ Z) (W : Z.Opens) :
    (f ≫ g) ⁻¹ᵁ W = f ⁻¹ᵁ (g ⁻¹ᵁ W) := by
  simp

private theorem UpperTheory.preimage_whisker_left_right_comm {S : Scheme.{0}} {T Y G' G : Over S} (y : T ⟶ Y) (i : G' ⟶ G)
    (W : (Y ⊗ G).left.Opens) :
    (T ◁ i).left ⁻¹ᵁ ((y ▷ G).left ⁻¹ᵁ W) = (y ▷ G').left ⁻¹ᵁ ((Y ◁ i).left ⁻¹ᵁ W) := by
  rw [← UpperTheory.preimage_comp_scheme_opens, ← UpperTheory.preimage_comp_scheme_opens, ← Over.comp_left, ← Over.comp_left,
    whisker_exchange]

private theorem UpperTheory.preimage_whiskerRight_whiskerRight_comp {S : Scheme.{0}} {T Y Z G : Over S} (y : T ⟶ Y) (f : Y ⟶ Z)
    (W : (Z ⊗ G).left.Opens) :
    (y ▷ G).left ⁻¹ᵁ ((f ▷ G).left ⁻¹ᵁ W) = ((y ≫ f) ▷ G).left ⁻¹ᵁ W := by
  rw [← UpperTheory.preimage_comp_scheme_opens, ← Over.comp_left, comp_whiskerRight]

open UpperTheory.ClopSum in
theorem UpperTheory.exists_clopRep_of_disjoint_open_cover :
    ∀ {S : Scheme.{0}} (G G₁ G₂ Y₁ Y₂ : Over S) (i₁ : G₁ ⟶ G) (i₂ : G₂ ⟶ G) (U₁ : (Y₁ ⊗ G₁).left.Opens) (U₂ : (Y₂ ⊗ G₂).left.Opens), IsOpenImmersion i₁.left → IsOpenImmersion i₂.left → Set.range i₁.left = (Set.range i₂.left)ᶜ → UpperTheory.RepresentationRank.Rep G₁ Y₁ U₁ → UpperTheory.RepresentationRank.Rep G₂ Y₂ U₂ → ∃ U : ((Y₁ ⊗ Y₂) ⊗ G).left.Opens, UpperTheory.RepresentationRank.Rep G (Y₁ ⊗ Y₂) U := by
  intro S G G₁ G₂ Y₁ Y₂ i₁ i₂ U₁ U₂ ho₁ ho₂ hr hU₁ hU₂
  have o1 : ∀ T : Over S, IsOpenImmersion (T ◁ i₁).left := fun T =>
    MorphismProperty.of_isPullback (UpperTheory.ClopSum.isPullback_wl T i₁).flip ho₁
  have o2 : ∀ T : Over S, IsOpenImmersion (T ◁ i₂).left := fun T =>
    MorphismProperty.of_isPullback (UpperTheory.ClopSum.isPullback_wl T i₂).flip ho₂
  have rr : ∀ T : Over S, Set.range (T ◁ i₁).left = (Set.range (T ◁ i₂).left)ᶜ := by
    intro T
    rw [UpperTheory.ClopSum.range_wl, UpperTheory.ClopSum.range_wl, hr]
    rfl
  haveI := o1 (Y₁ ⊗ Y₂)
  haveI := o2 (Y₁ ⊗ Y₂)
  obtain ⟨U, hUc, hU1, hU2⟩ := UpperTheory.ClopSum.glue ((Y₁ ⊗ Y₂) ◁ i₁).left ((Y₁ ⊗ Y₂) ◁ i₂).left
    (rr _) ((fst Y₁ Y₂ ▷ G₁).left ⁻¹ᵁ U₁) ((snd Y₁ Y₂ ▷ G₂).left ⁻¹ᵁ U₂)
    (hU₁.1.preimage (Scheme.Hom.continuous _)) (hU₂.1.preimage (Scheme.Hom.continuous _))
  refine ⟨U, hUc, ?_⟩
  intro T V hV
  have c1 : ∀ y : T ⟶ Y₁ ⊗ Y₂,
      (T ◁ i₁).left ⁻¹ᵁ ((y ▷ G).left ⁻¹ᵁ U) = ((y ≫ fst Y₁ Y₂) ▷ G₁).left ⁻¹ᵁ U₁ := by
    intro y
    rw [UpperTheory.preimage_whisker_left_right_comm, hU1, UpperTheory.preimage_whiskerRight_whiskerRight_comp]
  have c2 : ∀ y : T ⟶ Y₁ ⊗ Y₂,
      (T ◁ i₂).left ⁻¹ᵁ ((y ▷ G).left ⁻¹ᵁ U) = ((y ≫ snd Y₁ Y₂) ▷ G₂).left ⁻¹ᵁ U₂ := by
    intro y
    rw [UpperTheory.preimage_whisker_left_right_comm, hU2, UpperTheory.preimage_whiskerRight_whiskerRight_comp]
  obtain ⟨y₁, hy₁, hu₁⟩ := hU₁.2 T ((T ◁ i₁).left ⁻¹ᵁ V) (hV.preimage (Scheme.Hom.continuous _))
  obtain ⟨y₂, hy₂, hu₂⟩ := hU₂.2 T ((T ◁ i₂).left ⁻¹ᵁ V) (hV.preimage (Scheme.Hom.continuous _))
  refine ⟨lift y₁ y₂, ?_, ?_⟩
  · show ((lift y₁ y₂) ▷ G).left ⁻¹ᵁ U = V
    apply UpperTheory.ClopSum.opens_ext (T ◁ i₁).left (T ◁ i₂).left (rr T)
    · rw [c1, lift_fst]
      exact hy₁
    · rw [c2, lift_snd]
      exact hy₂
  · intro y hy
    have hy' : (y ▷ G).left ⁻¹ᵁ U = V := hy
    apply CartesianMonoidalCategory.hom_ext
    · rw [lift_fst]
      exact hu₁ _ (by
        show ((y ≫ fst Y₁ Y₂) ▷ G₁).left ⁻¹ᵁ U₁ = _
        rw [← c1, hy'])
    · rw [lift_snd]
      exact hu₂ _ (by
        show ((y ≫ snd Y₁ Y₂) ▷ G₂).left ⁻¹ᵁ U₂ = _
        rw [← c2, hy'])
