import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

namespace GlobalTheory.BaseChangeColim

variable {J : Type} [SmallCategory J] (D : J ⥤ CommRingCat.{0}) (j : J) {B' : CommRingCat.{0}}
  (g' : D.obj j ⟶ B')

noncomputable def mapPush {k k' : Under j} (f : k ⟶ k') :
    pushout g' (D.map k.hom) ⟶ pushout g' (D.map k'.hom) :=
  pushout.desc (pushout.inl g' (D.map k'.hom)) (D.map f.right ≫ pushout.inr g' (D.map k'.hom))
    (by rw [pushout.condition, ← Category.assoc, ← D.map_comp, Under.w f])

@[reassoc]
lemma inl_mapPush {k k' : Under j} (f : k ⟶ k') :
    pushout.inl g' (D.map k.hom) ≫ mapPush D j g' f = pushout.inl g' (D.map k'.hom) :=
  pushout.inl_desc _ _ _

@[reassoc]
lemma inr_mapPush {k k' : Under j} (f : k ⟶ k') :
    pushout.inr g' (D.map k.hom) ≫ mapPush D j g' f = D.map f.right ≫ pushout.inr g' (D.map k'.hom) :=
  pushout.inr_desc _ _ _

@[simps]
noncomputable def diag : Under j ⥤ CommRingCat.{0} where
  obj k := pushout g' (D.map k.hom)
  map f := mapPush D j g' f
  map_id k := by
    apply pushout.hom_ext
    · rw [inl_mapPush, Category.comp_id]
    · rw [inr_mapPush, Category.comp_id, Under.id_right, D.map_id, Category.id_comp]
  map_comp f f' := by
    apply pushout.hom_ext
    · rw [inl_mapPush, inl_mapPush_assoc, inl_mapPush]
    · rw [inr_mapPush, inr_mapPush_assoc, inr_mapPush, Under.comp_right, D.map_comp,
        Category.assoc]

noncomputable def inrNat : Under.forget j ⋙ D ⟶ diag D j g' where
  app k := pushout.inr g' (D.map k.hom)
  naturality k k' f := by
    show D.map f.right ≫ pushout.inr g' (D.map k'.hom) = pushout.inr g' (D.map k.hom) ≫ mapPush D j g' f
    rw [inr_mapPush]

noncomputable def inlNat : (Functor.const _).obj B' ⟶ diag D j g' where
  app k := pushout.inl g' (D.map k.hom)
  naturality k k' f := by
    show 𝟙 B' ≫ pushout.inl g' (D.map k'.hom) = pushout.inl g' (D.map k.hom) ≫ mapPush D j g' f
    rw [inl_mapPush, Category.id_comp]

noncomputable def toB (c : Cocone D) {B : CommRingCat.{0}} (h : B' ⟶ B) (g : c.pt ⟶ B)
    (sq : g' ≫ h = c.ι.app j ≫ g) : diag D j g' ⟶ (Functor.const _).obj B where
  app k := pushout.desc h (c.ι.app k.right ≫ g) (by rw [sq, ← c.w k.hom, Category.assoc])
  naturality k k' f := by
    show mapPush D j g' f ≫ pushout.desc h (c.ι.app k'.right ≫ g) _ =
      pushout.desc h (c.ι.app k.right ≫ g) _ ≫ 𝟙 B
    apply pushout.hom_ext
    · rw [inl_mapPush_assoc, pushout.inl_desc, pushout.inl_desc_assoc, Category.comp_id]
    · rw [inr_mapPush_assoc, pushout.inr_desc, pushout.inr_desc_assoc, Category.comp_id,
        ← Category.assoc, c.w]

theorem exists_isColimit_pushout_under : ∀ (J : Type) [SmallCategory J] [IsFiltered J] (D : J ⥤ CommRingCat.{0}) (c : Cocone D), IsColimit c → ∀ (j : J) (B' B : CommRingCat.{0}) (g' : D.obj j ⟶ B') (h : B' ⟶ B) (g : c.pt ⟶ B), IsPushout g' (c.ι.app j) h g → ∃ (D' : Under j ⥤ CommRingCat.{0}) (ι : D' ⟶ (Functor.const _).obj B) (u : Under.forget j ⋙ D ⟶ D') (v : (Functor.const _).obj B' ⟶ D'), Nonempty (IsColimit (Cocone.mk B ι)) ∧ ∀ k : Under j, IsPushout g' (D.map k.hom) (v.app k) (u.app k) ∧ v.app k ≫ ι.app k = h ∧ u.app k ≫ ι.app k = c.ι.app k.right ≫ g := by
  intro J _ _ D c hc j B' B g' h g hsq
  refine ⟨diag D j g', toB D j g' c h g hsq.w, inrNat D j g', inlNat D j g', ⟨?_⟩,
    fun k => ⟨IsPushout.of_hasPushout _ _, pushout.inl_desc _ _ _, pushout.inr_desc _ _ _⟩⟩
  have hc' : IsColimit (c.whisker (Under.forget j)) :=
    (Functor.Final.isColimitWhiskerEquiv _ _).symm hc
  let k0 : Under j := Under.mk (𝟙 j)

  let e : ∀ (s : Cocone (diag D j g')) (k : Under j), pushout g' (D.map k.hom) ⟶ s.pt :=
    fun s k => s.ι.app k
  have he : ∀ (s : Cocone (diag D j g')) {k k' : Under j} (f : k ⟶ k'),
      mapPush D j g' f ≫ e s k' = e s k := fun s _ _ f => s.w f
  let r : Cocone (diag D j g') → Cocone (Under.forget j ⋙ D) := fun s =>
    { pt := s.pt, ι := inrNat D j g' ≫ s.ι }
  have hl : ∀ (s : Cocone (diag D j g')) (k : Under j),
      pushout.inl g' (D.map k.hom) ≫ e s k = pushout.inl g' (D.map k0.hom) ≫ e s k0 := by
    intro s k
    rw [← he s (Under.homMk k.hom (Category.id_comp k.hom) : k0 ⟶ k), inl_mapPush_assoc]
  have hfr : ∀ (s : Cocone (diag D j g')) (k : Under j),
      c.ι.app k.right ≫ hc'.desc (r s) = pushout.inr g' (D.map k.hom) ≫ e s k :=
    fun s k => hc'.fac (r s) k
  have hw : ∀ s : Cocone (diag D j g'),
      g' ≫ (pushout.inl g' (D.map k0.hom) ≫ e s k0) = c.ι.app j ≫ hc'.desc (r s) := by
    intro s
    rw [show c.ι.app j = c.ι.app k0.right from rfl, hfr, ← Category.assoc, pushout.condition,
      Category.assoc]
    exact (congrArg (· ≫ (pushout.inr g' (D.map k0.hom) ≫ e s k0)) (D.map_id j)).trans
      (Category.id_comp _)
  exact
    { desc := fun s => hsq.desc _ _ (hw s)
      fac := fun s k => by
        change pushout.desc _ _ _ ≫ _ = e s k
        apply pushout.hom_ext
        · rw [pushout.inl_desc_assoc, hsq.inl_desc, hl s k]
        · rw [pushout.inr_desc_assoc, Category.assoc, hsq.inr_desc, hfr]
      uniq := fun s m hm => by
        have hm' : ∀ k : Under j, pushout.desc h (c.ι.app k.right ≫ g)
            (by rw [hsq.w, ← c.w k.hom, Category.assoc]) ≫ m = e s k := hm
        apply hsq.hom_ext
        · rw [hsq.inl_desc, ← hm' k0, pushout.inl_desc_assoc]
        · rw [hsq.inr_desc]
          apply hc'.hom_ext
          intro k
          change c.ι.app k.right ≫ g ≫ m = c.ι.app k.right ≫ hc'.desc (r s)
          rw [hfr, ← hm' k, pushout.inr_desc_assoc, Category.assoc] }

end GlobalTheory.BaseChangeColim
