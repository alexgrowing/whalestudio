import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RosatiFor
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabComp
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT

attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section

namespace GlobalTheory.UPel.HT.LevPull

theorem exists_pull_level : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (N : ℕ) (H : Scheme.{0}) (AH : Over H) [GrpObj AH] [IsCommMonObj AH] (actH : OActN D.O AH) (Y : Over H) (u : D.La → (Y ⟶ AH)), (∀ x y, u (x + y) = u x * u y) → (∀ (c : D.O) x, u (c • x) = u x ≫ actH.act c) → (∀ x, u (N • x) = 1) → ∃ (AE : Over Y.left) (_ : GrpObj AE) (_ : IsCommMonObj AE) (φE : AE.left ⟶ AH.left) (actE : OActN D.O AE) (ηE : D.La → (𝟙_ (Over Y.left) ⟶ AE)), IsGrpPullback AE AH Y.hom φE ∧ (∀ a : D.O, (actE.act a).left ≫ φE = φE ≫ (actH.act a).left) ∧ EtaOK D N actE ηE ∧ ∀ y, (ηE y).left ≫ φE = (u y).left := by
  intro p _ D N H AH _ _ actH Y u hadd hlin htor
  let AE : Over Y.left := (Over.pullback Y.hom).obj AH
  letI iG : GrpObj AE := Functor.grpObjObj
  letI iC : IsCommMonObj AE := Functor.isCommMonObj_obj
  let φE : AE.left ⟶ AH.left := pullback.fst AH.hom Y.hom
  have hg : IsGrpPullback AE AH Y.hom φE := isGrpPullback_pullback AH Y.hom
  have inj : ∀ {T : Over Y.left} {x y : T ⟶ AE}, x.left ≫ φE = y.left ≫ φE → x = y := fun {T x y} h =>
    Over.OverMorphism.ext (hg.1.hom_ext h (by rw [Over.w, Over.w]))
  have pm : ∀ {T : Over Y.left} (x y : T ⟶ AE), (x * y).left ≫ φE = (pushPt hg.1.w x * pushPt hg.1.w y).left :=
    fun x y => (hg.2 _ x y _ _ rfl rfl).symm

  let act' : D.O → (AE ⟶ AE) := fun a => Over.homMk (hg.1.lift (φE ≫ (actH.act a).left) AE.hom
    (by rw [Category.assoc, Over.w, hg.1.w])) (hg.1.lift_snd _ _ _)
  have ha : ∀ a, (act' a).left ≫ φE = φE ≫ (actH.act a).left := fun a => hg.1.lift_fst _ _ _
  have pa : ∀ {T : Over Y.left} (x : T ⟶ AE) a, pushPt hg.1.w (x ≫ act' a) = pushPt hg.1.w x ≫ actH.act a :=
    fun x a => Over.OverMorphism.ext (by
      show (x.left ≫ _) ≫ _ = (x.left ≫ _) ≫ _
      rw [Category.assoc, ha, Category.assoc])
  have injP : ∀ {T : Over Y.left} {x y : T ⟶ AE}, pushPt hg.1.w x = pushPt hg.1.w y → x = y := fun h =>
    inj (congrArg (fun q => q.left) h)
  have pm' : ∀ {T : Over Y.left} (x y : T ⟶ AE), pushPt hg.1.w (x * y) = pushPt hg.1.w x * pushPt hg.1.w y :=
    fun x y => map_mul (pushHom hg _) x y
  let actE : OActN D.O AE :=
    { act := act'
      hom := fun a => isMonHom_of_mul _ fun T x y => injP (by
        have := actH.hom a
        rw [pa, pm', pm', pa, pa, MonObj.mul_comp])
      one := injP (by rw [← Category.id_comp (act' 1), pa, actH.one, Category.comp_id])
      mul := fun a b => injP (by
        rw [← Category.id_comp (act' (a * b)), pa, pa, actH.mul, ← Category.id_comp (act' b), pa, Category.assoc])
      add := fun a b => injP (by
        refine Eq.trans ?_ (pm' (act' a) (act' b)).symm
        rw [← Category.id_comp (act' (a + b)), ← Category.id_comp (act' a), ← Category.id_comp (act' b), pa, pa, pa,
          actH.add]
        exact MonObj.comp_mul _ _ _) }

  let ηE : D.La → (𝟙_ (Over Y.left) ⟶ AE) := fun y =>
    Over.homMk (hg.1.lift (u y).left (𝟙_ (Over Y.left)).hom (by rw [Over.w (u y)]; simp)) (hg.1.lift_snd _ _ _)
  have hη : ∀ y, (ηE y).left ≫ φE = (u y).left := fun y => hg.1.lift_fst _ _ _
  have hT : (𝟙_ (Over Y.left)).hom ≫ Y.hom = Y.hom := by simp
  have one_congr : ∀ {a b : Y.left ⟶ H}, a = b → (1 : Over.mk a ⟶ AH).left = (1 : Over.mk b ⟶ AH).left := by
    intro a b h; subst h; rfl
  refine ⟨AE, inferInstance, inferInstance, φE, actE, ηE, hg, ha, ⟨fun x y => inj ?_, fun c x => inj ?_,
    fun x => inj ?_⟩, hη⟩
  · rw [hη, pm, hadd]
    exact (mul_left_congr hT (pushPt hg.1.w (ηE x)) (pushPt hg.1.w (ηE y)) (u x : Over.mk Y.hom ⟶ AH) (u y) (hη x) (hη y)).symm
  · show (ηE (c • x)).left ≫ φE = ((ηE x).left ≫ (act' c).left) ≫ φE
    rw [hη, hlin, Category.assoc, ha, ← Category.assoc, hη]; rfl
  · rw [hη, htor]
    have e := congrArg (fun q => q.left) (map_one (pushHom hg (𝟙_ (Over Y.left))))
    refine Eq.trans ?_ e.symm
    exact (one_congr hT).symm

end GlobalTheory.UPel.HT.LevPull
