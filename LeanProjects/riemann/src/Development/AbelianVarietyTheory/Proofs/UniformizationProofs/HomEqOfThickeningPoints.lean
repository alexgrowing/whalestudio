import Mathlib
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsIsoOfIsClosedImmersionOfThickeningsOfIsProper
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsInKNeOne
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.IsNsmul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.QkToAkU
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry in
open scoped CategoryTheory.Obj in
attribute [local instance] Over.cartesianMonoidalCategory in

theorem _root_.GlobalTheory.isProper_tensorObj_over {S : Scheme.{0}} {Z B : Over S} (hZ : IsProper Z.hom)
    (hB : IsProper B.hom) : IsProper (Z ⊗ B).hom := by
  simp only [Over.tensorObj_hom]
  infer_instance

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry in
open scoped CategoryTheory.Obj in
attribute [local instance] Over.cartesianMonoidalCategory in
private lemma hom_ext_of_thickenings (V : Type) [CommRing V] [IsDomain V]
    [IsDiscreteValuationRing V] {X B : Over (Spec (CommRingCat.of V))} [IsProper X.hom]
    [IsProper B.hom] (f g : X ⟶ B)
    (h : ∀ (e : ℕ) (T : Over (Spec (CommRingCat.of (V ⧸ (IsLocalRing.maximalIdeal V) ^ (e + 1)))))
      (t : Over.mk (T.hom ≫ _root_.ReciprocityTheory.ChartRestriction.G.Out.thick V (IsLocalRing.maximalIdeal V) e) ⟶ X), t ≫ f = t ≫ g) :
    f = g := by
  refine _root_.GlobalTheory.hom_eq_of_thickenings_of_isProper V (IsLocalRing.maximalIdeal V) ?_ X B f g ?_
  · rw [IsLocalRing.jacobson_eq_maximalIdeal]
    exact bot_ne_top
  · intro e
    exact congrArg Over.Hom.left (h e (_root_.ReciprocityTheory.ChartRestriction.G.Out.thickObj V _ e X) (_root_.ReciprocityTheory.ChartRestriction.G.Out.fstG _ e X))

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry in
open scoped CategoryTheory.Obj in
attribute [local instance] Over.cartesianMonoidalCategory in

theorem _root_.GlobalTheory.grpObj_of_thickenings : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (V ⧸ (IsLocalRing.maximalIdeal V) ^ (e + 1))))) [∀ e, GrpObj (Y e)] (β : ∀ e, (Y e).left ⟶ (Y (e + 1)).left), (∀ e, _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsGrpPullback (Y e) (Y (e + 1)) (_root_.ReciprocityTheory.ChartRestriction.G.Out.thickTrans V _ e) (β e)) → ∀ (B : Over (Spec (CommRingCat.of V))) (b : ∀ e, (Y e).left ⟶ B.left) [IsProper B.hom], (∀ e, IsPullback (b e) (Y e).hom B.hom (_root_.ReciprocityTheory.ChartRestriction.G.Out.thick V (IsLocalRing.maximalIdeal V) e)) → (∀ e, β e ≫ b (e + 1) = b e) → ∀ (mu : B ⊗ B ⟶ B) (io : B ⟶ B) (un : 𝟙_ _ ⟶ B), (∀ e (T : Over (Spec (CommRingCat.of (V ⧸ (IsLocalRing.maximalIdeal V) ^ (e + 1))))) (x y : T ⟶ Y e) (x₀ y₀ : Over.mk (T.hom ≫ _root_.ReciprocityTheory.ChartRestriction.G.Out.thick V (IsLocalRing.maximalIdeal V) e) ⟶ B), x₀.left = x.left ≫ b e → y₀.left = y.left ≫ b e → (lift x₀ y₀ ≫ mu).left = (x * y).left ≫ b e ∧ (x₀ ≫ io).left = (x⁻¹).left ≫ b e ∧ (toUnit (Over.mk (T.hom ≫ _root_.ReciprocityTheory.ChartRestriction.G.Out.thick V (IsLocalRing.maximalIdeal V) e)) ≫ un).left = (1 : T ⟶ Y e).left ≫ b e) → ∃ _ : GrpObj B, (∀ e, _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsGrpPullback (Y e) B (_root_.ReciprocityTheory.ChartRestriction.G.Out.thick V _ e) (b e)) ∧ ((∀ e, IsCommMonObj (Y e)) → IsCommMonObj B) := by
  intro V _ _ _ Y _ β _ B b _ hpb _ mu io un hY
  have lft : ∀ e (T : Over (Spec (CommRingCat.of (V ⧸ (IsLocalRing.maximalIdeal V) ^ (e + 1)))))
      (u : Over.mk (T.hom ≫ _root_.ReciprocityTheory.ChartRestriction.G.Out.thick V (IsLocalRing.maximalIdeal V) e) ⟶ B),
      ∃ x : T ⟶ Y e, u.left = x.left ≫ b e := by
    intro e T u
    refine ⟨Over.homMk ((hpb e).lift u.left T.hom (by simpa using Over.w u))
      ((hpb e).lift_snd _ _ _), ?_⟩
    simp
  have hmul : ∀ e (T : Over (Spec (CommRingCat.of (V ⧸ (IsLocalRing.maximalIdeal V) ^ (e + 1)))))
      (u v : Over.mk (T.hom ≫ _root_.ReciprocityTheory.ChartRestriction.G.Out.thick V (IsLocalRing.maximalIdeal V) e) ⟶ B) (x y : T ⟶ Y e),
      u.left = x.left ≫ b e → v.left = y.left ≫ b e → (lift u v ≫ mu).left = (x * y).left ≫ b e :=
    fun e T u v x y hu hv => (hY e T x y u v hu hv).1
  have hinv : ∀ e (T : Over (Spec (CommRingCat.of (V ⧸ (IsLocalRing.maximalIdeal V) ^ (e + 1)))))
      (u : Over.mk (T.hom ≫ _root_.ReciprocityTheory.ChartRestriction.G.Out.thick V (IsLocalRing.maximalIdeal V) e) ⟶ B) (x : T ⟶ Y e),
      u.left = x.left ≫ b e → (u ≫ io).left = x⁻¹.left ≫ b e :=
    fun e T u x hu => (hY e T x x u u hu hu).2.1
  have hone : ∀ e (T : Over (Spec (CommRingCat.of (V ⧸ (IsLocalRing.maximalIdeal V) ^ (e + 1))))),
      (toUnit (Over.mk (T.hom ≫ _root_.ReciprocityTheory.ChartRestriction.G.Out.thick V (IsLocalRing.maximalIdeal V) e)) ≫ un).left =
        (1 : T ⟶ Y e).left ≫ b e := by
    intro e T
    obtain ⟨u, hu⟩ : ∃ u : Over.mk (T.hom ≫ _root_.ReciprocityTheory.ChartRestriction.G.Out.thick V (IsLocalRing.maximalIdeal V) e) ⟶ B,
        u.left = (1 : T ⟶ Y e).left ≫ b e :=
      ⟨Over.homMk ((1 : T ⟶ Y e).left ≫ b e) (by
        simp only [Over.mk_hom, Category.assoc, (hpb e).w]
        rw [← Category.assoc, Over.w]), rfl⟩
    exact (hY e T 1 1 u u hu hu).2.2
  have hB2 : IsProper (B ⊗ B).hom := _root_.GlobalTheory.isProper_tensorObj_over inferInstance inferInstance
  have hB3 : IsProper ((B ⊗ B) ⊗ B).hom := _root_.GlobalTheory.isProper_tensorObj_over hB2 inferInstance
  have hB1 : IsProper (B ⊗ 𝟙_ _).hom :=
    _root_.GlobalTheory.isProper_tensorObj_over inferInstance (by simp; infer_instance)
  have hB1' : IsProper (𝟙_ _ ⊗ B).hom :=
    _root_.GlobalTheory.isProper_tensorObj_over (by simp; infer_instance) inferInstance
  letI : MonObj B :=
    { one := un
      mul := mu
      one_mul := by
        refine hom_ext_of_thickenings V _ _ fun e T t => ?_
        obtain ⟨x, hx⟩ := lft e T (t ≫ snd _ _)
        have ht : t = lift (t ≫ fst _ _) (t ≫ snd _ _) := by
          apply CartesianMonoidalCategory.hom_ext <;> simp
        rw [ht, toUnit_unique (t ≫ fst _ _) (toUnit _)]
        simp only [lift_whiskerRight_assoc, lift_leftUnitor_hom]
        ext
        rw [hmul e T _ _ 1 x (hone e T) hx, _root_.one_mul, hx]
      mul_one := by
        refine hom_ext_of_thickenings V _ _ fun e T t => ?_
        obtain ⟨x, hx⟩ := lft e T (t ≫ fst _ _)
        have ht : t = lift (t ≫ fst _ _) (t ≫ snd _ _) := by
          apply CartesianMonoidalCategory.hom_ext <;> simp
        rw [ht, toUnit_unique (t ≫ snd _ _) (toUnit _)]
        simp only [lift_whiskerLeft_assoc, lift_rightUnitor_hom]
        ext
        rw [hmul e T _ _ x 1 hx (hone e T), _root_.mul_one, hx]
      mul_assoc := by
        refine hom_ext_of_thickenings V _ _ fun e T t => ?_
        obtain ⟨x, hx⟩ := lft e T (t ≫ fst _ _ ≫ fst _ _)
        obtain ⟨y, hy⟩ := lft e T (t ≫ fst _ _ ≫ snd _ _)
        obtain ⟨z, hz⟩ := lft e T (t ≫ snd _ _)
        have ht : t = lift (lift (t ≫ fst _ _ ≫ fst _ _) (t ≫ fst _ _ ≫ snd _ _)) (t ≫ snd _ _) := by
          apply CartesianMonoidalCategory.hom_ext <;>
            [apply CartesianMonoidalCategory.hom_ext; skip] <;> simp
        rw [ht]
        simp only [lift_whiskerRight_assoc, lift_lift_associator_hom_assoc, lift_whiskerLeft_assoc]
        ext
        rw [hmul e T _ _ (x * y) z (hmul e T _ _ x y hx hy) hz,
          hmul e T _ _ x (y * z) hx (hmul e T _ _ y z hy hz), _root_.mul_assoc] }
  letI : GrpObj B :=
    { inv := io
      left_inv := by
        refine hom_ext_of_thickenings V _ _ fun e T t => ?_
        obtain ⟨x, hx⟩ := lft e T t
        simp only [comp_lift_assoc, Category.comp_id, comp_toUnit_assoc]
        ext
        refine (hmul e T _ _ x⁻¹ x (hinv e T t x hx) hx).trans ?_
        rw [inv_mul_cancel, ← hone e T]
        rfl
      right_inv := by
        refine hom_ext_of_thickenings V _ _ fun e T t => ?_
        obtain ⟨x, hx⟩ := lft e T t
        simp only [comp_lift_assoc, Category.comp_id, comp_toUnit_assoc]
        ext
        refine (hmul e T _ _ x x⁻¹ hx (hinv e T t x hx)).trans ?_
        rw [mul_inv_cancel, ← hone e T]
        rfl }
  refine ⟨this, fun e => ⟨hpb e, fun T x y x₀ y₀ hx hy => hmul e T x₀ y₀ x y hx hy⟩, fun hc => ?_⟩
  exact
    { mul_comm := by
        refine hom_ext_of_thickenings V _ _ fun e T t => ?_
        obtain ⟨x, hx⟩ := lft e T (t ≫ fst _ _)
        obtain ⟨y, hy⟩ := lft e T (t ≫ snd _ _)
        have ht : t = lift (t ≫ fst _ _) (t ≫ snd _ _) := by
          apply CartesianMonoidalCategory.hom_ext <;> simp
        rw [ht]
        simp only [lift_braiding_hom_assoc]
        ext
        have := hc e
        refine (hmul e T _ _ y x hy hx).trans ?_
        rw [_root_.mul_comm]
        exact (hmul e T _ _ x y hx hy).symm }

end GlobalTheory
