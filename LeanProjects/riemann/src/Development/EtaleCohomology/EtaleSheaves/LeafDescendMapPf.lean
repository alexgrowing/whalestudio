import Development.EtaleCohomology.EtaleSheaves.LeafDescendVCut

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite LateralTheory.E.E4 LateralTheory.E.LeafDescendVCut

namespace LateralTheory.E.LeafDescendMapPf

variable {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω]

abbrev J (R : Subalgebra k Ω) : Type := {S : Subalgebra k Ω // R ≤ S ∧ S.FG}

instance (R : Subalgebra k Ω) : PartialOrder (J R) := inferInstanceAs (PartialOrder {S : Subalgebra k Ω // R ≤ S ∧ S.FG})

instance (R : Subalgebra k Ω) : IsDirected (J R) (· ≤ ·) :=
  ⟨fun a b => ⟨⟨a.1 ⊔ b.1, le_sup_of_le_left a.2.1, a.2.2.sup b.2.2⟩, le_sup_left (a := a.1), le_sup_right (a := a.1)⟩⟩

lemma toR_incl {R S : Subalgebra k Ω} (h : R ≤ S) : toR S ≫ incl h = toR R := by
  rw [toR, incl, toR, ← Spec.map_comp]; rfl

lemma incl_incl {R S T : Subalgebra k Ω} (h : R ≤ S) (h' : S ≤ T) :
    incl h' ≫ incl h = incl (h.trans h') := by
  rw [incl, incl, incl, ← Spec.map_comp]; rfl

lemma incl_base {R S : Subalgebra k Ω} (h : R ≤ S) :
    incl h ≫ Spec.map (CommRingCat.ofHom (algebraMap k R)) = Spec.map (CommRingCat.ofHom (algebraMap k S)) := by
  rw [incl, ← Spec.map_comp]; rfl

lemma toR_base (R : Subalgebra k Ω) :
    toR R ≫ Spec.map (CommRingCat.ofHom (algebraMap k R)) = Spec.map (CommRingCat.ofHom (algebraMap k Ω)) := by
  rw [toR, ← Spec.map_comp]; rfl

end LateralTheory.E.LeafDescendMapPf

namespace LateralTheory.E.LeafDescendMapPf
variable {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω]

lemma incl_self {S : Subalgebra k Ω} (h : S ≤ S) : incl h = 𝟙 _ := by
  rw [incl, ← Spec.map_id]; rfl

variable (R : Subalgebra k Ω)

def F : J R ⥤ CommRingCat.{0} where
  obj S := CommRingCat.of S.1
  map {S T} h := CommRingCat.ofHom (Subalgebra.inclusion (leOfHom h)).toRingHom

def coc : Cocone (F R) where
  pt := CommRingCat.of Ω
  ι := { app S := CommRingCat.ofHom (algebraMap S.1 Ω) }

def cocIsColimit (hR : R.FG) : IsColimit (coc R) := by
  haveI : Nonempty (J R) := ⟨⟨R, le_rfl, hR⟩⟩
  haveI : ReflectsColimitsOfShape (J R) (forget CommRingCat.{0}) :=
    reflectsColimitsOfShape_of_reflectsIsomorphisms
  apply isColimitOfReflects (forget CommRingCat.{0})
  refine Types.FilteredColimit.isColimitOf _ _ ?_ ?_
  · intro (x : Ω)
    have hx : x ∈ R ⊔ Algebra.adjoin k {x} := le_sup_right (a := R) (Algebra.subset_adjoin rfl)
    exact ⟨⟨R ⊔ Algebra.adjoin k {x}, le_sup_left, hR.sup (by simpa using Subalgebra.fg_adjoin_finset (R := k) ({x} : Finset Ω))⟩, ⟨x, hx⟩, rfl⟩
  · intro i j xi xj h
    refine ⟨⟨i.1 ⊔ j.1, le_sup_of_le_left i.2.1, i.2.2.sup j.2.2⟩, homOfLE (le_sup_left (a := i.1)),
      homOfLE (le_sup_right (a := i.1)), ?_⟩
    apply Subtype.ext
    exact h

def specLim (hR : R.FG) : IsLimit (Scheme.Spec.mapCone (coc R).op) :=
  isLimitOfPreserves Scheme.Spec (cocIsColimit R hR).op

example (S : J R) : (Scheme.Spec.mapCone (coc R).op).π.app (op S) = toR S.1 := rfl

end LateralTheory.E.LeafDescendMapPf

namespace LateralTheory.E.LeafDescendMapPf
variable {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω] (R : Subalgebra k Ω)
variable {D0 : Scheme.{0}} (q : D0 ⟶ Sp R)

abbrev D : (J R)ᵒᵖ ⥤ Scheme.{0} where
  obj S := pullback q (incl S.unop.2.1)
  map {S T} h := pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ incl (leOfHom h.unop))
    (by rw [pullback.condition, Category.assoc, incl_incl])
  map_id S := by apply pullback.hom_ext <;> simp only [pullback.lift_fst, pullback.lift_snd, pullback.lift_fst_assoc, pullback.lift_snd_assoc, Category.assoc, Category.id_comp, Category.comp_id, Functor.const_obj_map, incl_incl, toR_incl, incl_self, incl_base, CategoryTheory.Functor.id_obj]
  map_comp f g := by apply pullback.hom_ext <;> simp only [pullback.lift_fst, pullback.lift_snd, pullback.lift_fst_assoc, pullback.lift_snd_assoc, Category.assoc, Category.id_comp, Category.comp_id, Functor.const_obj_map, incl_incl, toR_incl, incl_self, incl_base, CategoryTheory.Functor.id_obj]

def tS : D R q ⟶ (Functor.const _).obj (Sp k) where
  app S := pullback.snd _ _ ≫ Spec.map (CommRingCat.ofHom (algebraMap k S.unop.1))
  naturality S T h := by
    simp only [Functor.const_obj_map, Category.comp_id]
    erw [pullback.lift_snd_assoc]
    rw [Category.assoc, incl_base]
    exact (Category.comp_id _).symm

variable {C0 : Scheme.{0}} (c0 : C0 ⟶ Sp Ω) (v0 : C0 ⟶ D0) (hPB : IsPullback v0 c0 q (toR R))

abbrev cone : Cone (D R q) where
  pt := C0
  π := { app S := pullback.lift v0 (c0 ≫ toR S.unop.1) (by rw [hPB.w, Category.assoc, toR_incl])
         naturality S T h := by apply pullback.hom_ext <;> (dsimp only [D]; simp only [pullback.lift_fst, pullback.lift_snd, pullback.lift_fst_assoc, pullback.lift_snd_assoc, Category.assoc, Category.id_comp, Category.comp_id, Functor.const_obj_map, incl_incl, toR_incl, incl_self, incl_base, CategoryTheory.Functor.id_obj]) <;> simp }

instance (S : (J R)ᵒᵖ) [IsProper q] : CompactSpace ((D R q).obj S) := by
  dsimp [D]; exact QuasiCompact.compactSpace_of_compactSpace (pullback.snd q _)

instance (S : (J R)ᵒᵖ) [IsProper q] : QuasiSeparatedSpace ((D R q).obj S) := by
  dsimp [D]; exact quasiSeparatedSpace_of_quasiSeparated (pullback.snd q _)

lemma fstAff {S : Subalgebra k Ω} (h : R ≤ S) : IsAffineHom (pullback.fst q (incl h)) :=
  MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @IsAffineHom) (IsPullback.of_hasPullback q (incl h)).flip
    (by dsimp [incl]; infer_instance)

instance {S T : (J R)ᵒᵖ} (h : S ⟶ T) : IsAffineHom ((D R q).map h) := by
  have h1 := fstAff R q S.unop.2.1
  have h2 := fstAff R q T.unop.2.1
  have : IsAffineHom ((D R q).map h ≫ pullback.fst _ _) := by
    dsimp only [D]; rw [pullback.lift_fst]; exact h1
  have hs : IsSeparated (pullback.fst q (incl T.unop.2.1)) := @IsSeparated.of_isAffineHom _ _ _ h2
  exact IsAffineHom.of_comp _ (pullback.fst q (incl T.unop.2.1))

end LateralTheory.E.LeafDescendMapPf

namespace LateralTheory.E.LeafDescendMapPf
variable {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω] (R : Subalgebra k Ω)
variable {D0 : Scheme.{0}} (q : D0 ⟶ Sp R)
variable {C0 : Scheme.{0}} (c0 : C0 ⟶ Sp Ω) (v0 : C0 ⟶ D0) (hPB : IsPullback v0 c0 q (toR R))

abbrev specCone (s : Cone (D R q)) : Cone ((F R).op ⋙ Scheme.Spec) where
  pt := s.pt
  π := { app S := s.π.app S ≫ pullback.snd _ _
         naturality S T h := by
           have hw := s.w h
           rw [← hw]
           erw [Category.id_comp, Category.assoc, pullback.lift_snd]
           exact (Category.assoc _ _ _).symm }

def bL (hR : R.FG) (s : Cone (D R q)) : s.pt ⟶ Sp Ω := (specLim R hR).lift (specCone R q s)

lemma bL_fac (hR : R.FG) (s : Cone (D R q)) (j : (J R)ᵒᵖ) :
    bL R q hR s ≫ toR j.unop.1 = s.π.app j ≫ pullback.snd q (incl j.unop.2.1) :=
  (specLim R hR).fac (specCone R q s) j

lemma bL_uniq (hR : R.FG) (s : Cone (D R q)) (m : s.pt ⟶ Sp Ω)
    (hm : ∀ j : (J R)ᵒᵖ, m ≫ toR j.unop.1 = s.π.app j ≫ pullback.snd q (incl j.unop.2.1)) : m = bL R q hR s :=
  (specLim R hR).uniq (specCone R q s) m hm

def aL (hR : R.FG) (s : Cone (D R q)) : s.pt ⟶ D0 :=
  s.π.app (op (⟨R, le_rfl, hR⟩ : J R)) ≫ pullback.fst q (incl (le_refl R))

lemma aL_w (hR : R.FG) (s : Cone (D R q)) : aL R q hR s ≫ q = bL R q hR s ≫ toR R := by
  have := bL_fac R q hR s (op (⟨R, le_rfl, hR⟩ : J R))
  simp only [aL, Category.assoc, pullback.condition, incl_self, Category.comp_id]
  exact this.symm

def coneIsLimit (hR : R.FG) : IsLimit (cone R q c0 v0 hPB) where
  lift s := hPB.lift (aL R q hR s) (bL R q hR s) (aL_w R q hR s)
  fac s j := by
    have hw := s.w (homOfLE j.unop.2.1 : (⟨R, le_rfl, hR⟩ : J R) ⟶ j.unop).op
    apply pullback.hom_ext
    · simp only [cone, Category.assoc, pullback.lift_fst, IsPullback.lift_fst, aL, ← hw]
    · simp only [cone, Category.assoc, pullback.lift_snd]
      rw [← Category.assoc, IsPullback.lift_snd]
      exact bL_fac R q hR s j
  uniq s m hm := by
    apply hPB.hom_ext
    · rw [IsPullback.lift_fst, aL, ← hm]
      simp only [cone, Category.assoc, pullback.lift_fst]
    · rw [IsPullback.lift_snd]
      apply bL_uniq
      intro j
      rw [← hm j]
      simp only [cone, Category.assoc, pullback.lift_snd]

lemma lfp {X : Scheme.{0}} (p : X ⟶ Sp k) [IsProper p] : LocallyOfFinitePresentation p := by
  rw [HasRingHomProperty.iff_appLE (P := @LocallyOfFinitePresentation)]
  intro U V e
  haveI : IsNoetherianRing Γ(Sp k, U) := IsLocallyNoetherian.component_noetherian U
  exact RingHom.FinitePresentation.of_finiteType.mp (HasRingHomProperty.appLE @LocallyOfFiniteType p inferInstance U V e)

end LateralTheory.E.LeafDescendMapPf
