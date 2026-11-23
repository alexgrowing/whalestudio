import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TransportSymmetricLiftsThetaGroupTraitImports
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.QkToAkBaseChange
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull

noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.ThetaMove

namespace GlobalTheory.ThetaMove

theorem negT_fibre_comm : ∀ {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] {D : DegData R (maximalIdeal R)} (C : LabCover D) {W : Type} [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W) (F : Type) [Field F] [Algebra (FractionRing R) F] [Algebra (FractionRing W) F] (f : (TFK (R := W) F ⊗ T.A.A).left ⟶ (TFK (R := R) F ⊗ C.A.A).left) (hf1 : f ≫ (fst (TFK (R := R) F) C.A.A).left = (fst (TFK (R := W) F) T.A.A).left) (hf2 : f ≫ (snd (TFK (R := R) F) C.A.A).left ≫ C.α = (snd (TFK (R := W) F) T.A.A).left ≫ T.U.gen.inv.left ≫ pullback.fst T.G.hom (jK W) ≫ T.β), f ≫ (negT C.A.A (TFK (R := R) F)).left = (negT T.A.A (TFK (R := W) F)).left ≫ f := by
  intro R _ _ _ D C W _ _ _ T F _ _ _ f hf1 hf2
  have gB : IsGrpPullback T.A.A C.G (jK W ≫ T.ξ)
      (T.U.gen.inv.left ≫ pullback.fst T.G.hom (jK W) ≫ T.β) :=
    ((GlobalTheory.ThetaBaseChange.grp_generic T.U.toUnifPre).comp T.cart).congr rfl (by simp only [Category.assoc])
  have gA := C.α_cart
  have nfA : negT C.A.A (TFK (R := R) F) ≫ fst (TFK (R := R) F) C.A.A = fst _ _ := by unfold negT; exact lift_fst _ _
  have nsA : negT C.A.A (TFK (R := R) F) ≫ snd (TFK (R := R) F) C.A.A = snd _ _ ≫ GrpObj.inv := by
    unfold negT; exact lift_snd _ _
  have nfB : negT T.A.A (TFK (R := W) F) ≫ fst (TFK (R := W) F) T.A.A = fst _ _ := by unfold negT; exact lift_fst _ _
  have nsB : negT T.A.A (TFK (R := W) F) ≫ snd (TFK (R := W) F) T.A.A = snd _ _ ≫ GrpObj.inv := by
    unfold negT; exact lift_snd _ _
  have hw : f ≫ (TFK (R := R) F ⊗ C.A.A).hom ≫ C.gp = (TFK (R := W) F ⊗ T.A.A).hom ≫ jK W ≫ T.ξ := by
    have e := congrArg (· ≫ C.G.hom) hf2
    have wB := gB.1.w
    simp only [Category.assoc] at e wB
    rw [gA.1.w, wB, ← Category.assoc (snd (TFK (R := R) F) C.A.A).left, ← Category.assoc (snd (TFK (R := W) F) T.A.A).left,
      Over.w, Over.w] at e
    exact e
  let ρ : Over.mk ((TFK (R := W) F ⊗ T.A.A).hom ≫ jK W ≫ T.ξ) ⟶ Over.mk ((TFK (R := R) F ⊗ C.A.A).hom ≫ C.gp) :=
    Over.homMk f hw
  have key : ρ ≫ pushHom gA _ (snd _ _) = pushHom gB _ (snd _ _) :=
    Over.OverMorphism.ext (by
      show f ≫ (snd (TFK (R := R) F) C.A.A).left ≫ C.α = (snd (TFK (R := W) F) T.A.A).left ≫ _
      exact hf2)
  have keyi : ρ ≫ pushHom gA _ (snd _ _ ≫ GrpObj.inv) = pushHom gB _ (snd _ _ ≫ GrpObj.inv) := by
    have i1 : (snd (TFK (R := R) F) C.A.A ≫ GrpObj.inv) = (snd _ _)⁻¹ := rfl
    have i2 : (snd (TFK (R := W) F) T.A.A ≫ GrpObj.inv) = (snd _ _)⁻¹ := rfl
    rw [i1, i2, map_inv, map_inv, GrpObj.comp_inv, key]
  apply pullback.hom_ext
  · change (f ≫ (negT C.A.A (TFK (R := R) F)).left) ≫ (fst (TFK (R := R) F) C.A.A).left =
      ((negT T.A.A (TFK (R := W) F)).left ≫ f) ≫ (fst (TFK (R := R) F) C.A.A).left
    rw [Category.assoc, Category.assoc, ← Over.comp_left, nfA, hf1, ← Over.comp_left, nfB]
  · change (f ≫ (negT C.A.A (TFK (R := R) F)).left) ≫ (snd (TFK (R := R) F) C.A.A).left =
      ((negT T.A.A (TFK (R := W) F)).left ≫ f) ≫ (snd (TFK (R := R) F) C.A.A).left
    rw [Category.assoc, Category.assoc, ← Over.comp_left, nsA]
    apply gA.1.hom_ext
    · have k : f ≫ (snd (TFK (R := R) F) C.A.A ≫ GrpObj.inv).left ≫ C.α =
          (snd (TFK (R := W) F) T.A.A ≫ GrpObj.inv).left ≫ T.U.gen.inv.left ≫ pullback.fst T.G.hom (jK W) ≫ T.β :=
        congrArg Over.Hom.left keyi
      rw [Category.assoc, k]
      simp only [Category.assoc]
      rw [hf2, ← Category.assoc (negT T.A.A (TFK (R := W) F)).left, ← Over.comp_left, nsB]
    · rw [Category.assoc, Over.w, Category.assoc, Category.assoc, Over.w]
      rw [← Over.w (fst (TFK (R := R) F) C.A.A), ← Category.assoc, hf1,
        ← Category.assoc (negT T.A.A (TFK (R := W) F)).left, ← Over.comp_left, nfB]

end GlobalTheory.ThetaMove
