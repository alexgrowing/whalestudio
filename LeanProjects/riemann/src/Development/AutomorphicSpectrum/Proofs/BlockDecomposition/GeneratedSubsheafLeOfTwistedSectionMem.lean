import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GenHom

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE GlobalTheory.CompanionTheory.GE.TwGen

namespace GlobalTheory.CompanionTheory.GE.TwGen

theorem sectionHom_app_comp {X : Scheme.{0}} {F G : X.Modules} (φ : F ⟶ G) (s : Γ(F, ⊤)) :
    GlobalTheory.QCoh.sectionHom (φ.app ⊤ s) = GlobalTheory.QCoh.sectionHom s ≫ φ := by
  ext V a
  change (GlobalTheory.QCoh.sectionHom (φ.app ⊤ s)).app V a = φ.app V ((GlobalTheory.QCoh.sectionHom s).app V a)
  rw [GlobalTheory.QCoh.sectionHom_app, GlobalTheory.QCoh.sectionHom_app, Scheme.Modules.Hom.app_smul,
    GlobalTheory.Twist.app_resM]

theorem twistZZeroIso_inv_naturality {X : Scheme.{0}} {H : ReciprocityTheory.ChartRestriction.G.Semi.LB X} (hH : H.IsLB)
    {F G : X.Modules} (u : F ⟶ G) :
    (GlobalTheory.Twist.twistZZeroIso F hH).inv ≫ u =
      GlobalTheory.Twist.map (GlobalTheory.lbZPow H 0) u ≫ (GlobalTheory.Twist.twistZZeroIso G hH).inv := by
  rw [Iso.inv_comp_eq, ← Category.assoc, Iso.eq_comp_inv]
  refine GlobalTheory.Twist.zhom_ext fun V t i => ?_
  change GlobalTheory.Twist.zcoord ((GlobalTheory.Twist.twistZZeroIso G hH).hom.app V (u.app V t)) i =
    GlobalTheory.Twist.zcoord ((GlobalTheory.Twist.map (GlobalTheory.lbZPow H 0) u).app V
      ((GlobalTheory.Twist.twistZZeroIso F hH).hom.app V t)) i
  rw [GlobalTheory.Twist.zcoord_twistZZeroIso_hom_app, GlobalTheory.Twist.zcoord_map_app,
    GlobalTheory.Twist.zcoord_twistZZeroIso_hom_app, GlobalTheory.Twist.app_resM]

theorem genHom_map_app {X : Scheme.{0}} {H : ReciprocityTheory.ChartRestriction.G.Semi.LB X} (hH : H.IsLB)
    {F G : X.Modules} (u : F ⟶ G) (n : ℤ) (b : Γ(GlobalTheory.twistZ F H n, ⊤)) :
    genHom hH n ((GlobalTheory.Twist.map (GlobalTheory.lbZPow H n) u).app ⊤ b) = genHom hH n b ≫ u := by
  simp only [genHom, Category.assoc, twistZZeroIso_inv_naturality hH u]
  rw [sectionHom_app_comp]
  refine Eq.trans ?_ (congrArg (_ ≫ ·) (GlobalTheory.Twist.twistZAddIso_naturality_assoc hH
    (add_neg_cancel n) u (GlobalTheory.Twist.twistZZeroIso G hH).inv))
  exact Category.assoc (GlobalTheory.Twist.map (GlobalTheory.lbZPow H (-n)) (GlobalTheory.QCoh.sectionHom b))
    (GlobalTheory.Twist.map (GlobalTheory.lbZPow H (-n)) (GlobalTheory.Twist.map (GlobalTheory.lbZPow H n) u))
    ((GlobalTheory.Twist.twistZAddIso G hH (add_neg_cancel n)).hom ≫ (GlobalTheory.Twist.twistZZeroIso G hH).inv)

theorem genSub_le : ∀ {X : Scheme.{0}} {H : ReciprocityTheory.ChartRestriction.G.Semi.LB X} (hH : H.IsLB) {P : X.Modules}
    (S : Subobject P) (n : ℤ) (b : Γ(GlobalTheory.twistZ P H n, ⊤)), b ∈ twSecs H n S → genSub hH n b ≤ S := by
  rintro X H hH P S n _ ⟨b', rfl⟩
  exact imageSubobject_le _ (genHom hH n b') (genHom_map_app hH S.arrow n b').symm

end GlobalTheory.CompanionTheory.GE.TwGen
