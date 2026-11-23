import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TransportSymmetricLiftsThetaGroupTraitImports
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.ThetaMove

noncomputable section

namespace GlobalTheory.Mum

theorem tensorLeft_hom_ext {S : Scheme.{0}} {X Y : Over S} {Z : Scheme.{0}} {a b : Z ⟶ (X ⊗ Y).left}
    (h1 : a ≫ (fst X Y).left = b ≫ (fst X Y).left) (h2 : a ≫ (snd X Y).left = b ≫ (snd X Y).left) : a = b :=
  pullback.hom_ext h1 h2

theorem trait_transl_comm : ∀ {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] {D : DegData R (maximalIdeal R)} (C : LabCover D) {W : Type} [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W) (F : Type) [Field F] [Algebra (FractionRing R) F] [Algebra (FractionRing W) F] (f : (TFK (R := W) F ⊗ T.A.A).left ⟶ (TFK (R := R) F ⊗ C.A.A).left) (hf1 : f ≫ (fst (TFK (R := R) F) C.A.A).left = (fst (TFK (R := W) F) T.A.A).left) (hf2 : f ≫ (snd (TFK (R := R) F) C.A.A).left ≫ C.α = (snd (TFK (R := W) F) T.A.A).left ≫ T.U.gen.inv.left ≫ pullback.fst T.G.hom (jK W) ≫ T.β) (x' : TFK (R := W) F ⟶ T.A.A) (x : TFK (R := R) F ⟶ C.A.A) (hx : (ptSecT T.A.A x').left ≫ f = (ptSecT C.A.A x).left), f ≫ (translT C.A.A x).left = (translT T.A.A x').left ≫ f := by
  intro R _ _ _ D C W _ _ _ T F _ _ _ f hf1 hf2 x' x hx
  have gT : IsGrpPullback T.A.A C.G (jK W ≫ T.ξ)
      (T.U.gen.inv.left ≫ pullback.fst T.G.hom (jK W) ≫ T.β) := by
    have := (ThetaBaseChange.grp_generic T.U.toUnifPre).comp T.cart
    simpa only [Category.assoc] using this
  have gC := C.α_cart
  have hxx : x.left ≫ C.α = x'.left ≫ T.U.gen.inv.left ≫ pullback.fst T.G.hom (jK W) ≫ T.β := by
    have e1 : x.left = (ptSecT C.A.A x).left ≫ (snd (TFK (R := R) F) C.A.A).left := by
      rw [← Over.comp_left, ptSecT, lift_snd]
    have e2 : x'.left = (ptSecT T.A.A x').left ≫ (snd (TFK (R := W) F) T.A.A).left := by
      rw [← Over.comp_left, ptSecT, lift_snd]
    rw [e1, ← hx, Category.assoc, Category.assoc, hf2, ← Category.assoc, ← Category.assoc, ← e2]
    simp only [Category.assoc]
  have hbase : f ≫ (TFK (R := R) F ⊗ C.A.A).hom ≫ C.gp = (TFK (R := W) F ⊗ T.A.A).hom ≫ jK W ≫ T.ξ := by
    have a1 : (TFK (R := R) F ⊗ C.A.A).hom = (snd (TFK (R := R) F) C.A.A).left ≫ C.A.A.hom := (Over.w _).symm
    have a2 : (TFK (R := W) F ⊗ T.A.A).hom = (snd (TFK (R := W) F) T.A.A).left ≫ T.A.A.hom := (Over.w _).symm
    have w := gT.1.w
    simp only [Category.assoc] at w
    rw [a1, a2, Category.assoc, Category.assoc, ← gC.1.w, reassoc_of% hf2, w]
  apply tensorLeft_hom_ext
  · simp only [Category.assoc, ← Over.comp_left, translT, lift_fst, hf1]
  · rw [Category.assoc, Category.assoc]
    apply gC.1.hom_ext
    · have eL : (translT C.A.A x).left ≫ (snd (TFK (R := R) F) C.A.A).left ≫ C.α =
          ((pushPt gC.1.w (fst (TFK (R := R) F) C.A.A ≫ x)) * (pushPt gC.1.w (snd (TFK (R := R) F) C.A.A))).left := by
        rw [gC.2 _ _ _ _ _ rfl rfl, ← Category.assoc, ← Over.comp_left, translT, lift_snd, translPt_eq]
      have eR : (translT T.A.A x').left ≫ (snd (TFK (R := W) F) T.A.A).left ≫ T.U.gen.inv.left ≫
          pullback.fst T.G.hom (jK W) ≫ T.β =
          ((pushPt gT.1.w (fst (TFK (R := W) F) T.A.A ≫ x')) * (pushPt gT.1.w (snd (TFK (R := W) F) T.A.A))).left := by
        rw [gT.2 _ _ _ _ _ rfl rfl, ← Category.assoc, ← Over.comp_left, translT, lift_snd, translPt_eq]
      let ρ : Over.mk ((TFK (R := W) F ⊗ T.A.A).hom ≫ jK W ≫ T.ξ) ⟶ Over.mk ((TFK (R := R) F ⊗ C.A.A).hom ≫ C.gp) :=
        Over.homMk f hbase
      have e0 : ρ ≫ pushPt gC.1.w (fst (TFK (R := R) F) C.A.A ≫ x) = pushPt gT.1.w (fst (TFK (R := W) F) T.A.A ≫ x') := by
        ext
        show f ≫ (fst (TFK (R := R) F) C.A.A ≫ x).left ≫ C.α = (fst (TFK (R := W) F) T.A.A ≫ x').left ≫ _
        simp only [Over.comp_left, Category.assoc]
        rw [hxx, reassoc_of% hf1]
      have e1 : ρ ≫ pushPt gC.1.w (snd (TFK (R := R) F) C.A.A) = pushPt gT.1.w (snd (TFK (R := W) F) T.A.A) := by
        ext
        exact hf2
      simp only [Category.assoc]
      rw [eL, hf2, eR, ← e0, ← e1, ← MonObj.comp_mul]
      rfl
    · simp only [Category.assoc]
      rw [Over.w (snd (TFK (R := R) F) C.A.A), Over.w (translT C.A.A x), ← Over.w (fst (TFK (R := R) F) C.A.A),
        reassoc_of% hf1, ← Category.assoc, ← Over.comp_left, translT, lift_fst]

end GlobalTheory.Mum
