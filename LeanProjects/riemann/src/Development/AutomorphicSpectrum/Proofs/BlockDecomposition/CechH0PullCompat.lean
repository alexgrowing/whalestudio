import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.DifferentialFormsCech.CechDifferentialPullback.Bridge
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite Limits GroundTheory.Arith.SchemeCoh GlobalTheory.SheafPull CrystallineSemistableComparison CrystallineSemistableComparison.Om CrystallineSemistableComparison.Om.Cech

namespace GlobalTheory.CompanionTheory.CechZero

theorem cechHZeroEquiv_cls {X : TopCat.{0}} {ι : Type} (P : (Opens X)ᵒᵖ ⥤ AddCommGrpCat.{0})
    (U : ι → Opens X) (hP : Presheaf.IsSheaf (Opens.grothendieckTopology X) P) (hU : iSup U = ⊤)
    (s : P.obj (op ⊤)) (σ : Cochain P U 0) (h : GroundTheory.Arith.SchemeCoh.d P U 0 σ = 0)
    (hσ : σ = (globalCocycle P U s).1) :
    GroundTheory.Arith.SchemeCoh.cechHZeroEquiv P U hP hU (GroundTheory.Arith.SchemeCoh.cls σ h) = s := by
  subst hσ
  simp only [GroundTheory.Arith.SchemeCoh.cechHZeroEquiv, AddEquiv.trans_apply]
  exact (globalCocycleEquiv P U hP hU).symm_apply_apply s

theorem pullCoch_globalCocycle {X Y : TopCat.{0}} (f : X ⟶ Y) {P : (Opens Y)ᵒᵖ ⥤ AddCommGrpCat.{0}}
    {Q : (Opens X)ᵒᵖ ⥤ AddCommGrpCat.{0}} (φ : P ⟶ (Opens.map f).op ⋙ Q)
    {κ ι : Type} (V : κ → Opens Y) (U : ι → Opens X) (τ : ι → κ)
    (hτ : ∀ i, U i ≤ (Opens.map f).obj (V (τ i))) (s : P.obj (op ⊤)) :
    pullCoch f φ V U τ hτ 0 (globalCocycle P V s).1 =
      (globalCocycle Q U (GroundTheory.Arith.SchemeCoh.res Q (le_top : (⊤ : Opens X) ≤ (Opens.map f).obj ⊤)
        (φ.app (op ⊤) s))).1 := by
  funext t
  change GroundTheory.Arith.SchemeCoh.res Q _ (φ.app _ (GroundTheory.Arith.SchemeCoh.res P _ s)) =
    GroundTheory.Arith.SchemeCoh.res Q _ (GroundTheory.Arith.SchemeCoh.res Q _ (φ.app (op ⊤) s))
  rw [app_res_map, res_res, res_res]

theorem zeroEquiv_eq_equivZero {X : TopCat.{0}} (F : AbSheaf X) (W : Opens X) (x : Sheaf.H'.{0} F 0 W) :
    GlobalTheory.SiteCoh.zeroEquiv F W x = GlobalTheory.SheafLES.equivZero.{0} F W x := by
  obtain ⟨φ, rfl⟩ := (Abelian.Ext.mk₀_bijective _ _).surjective x
  rw [GlobalTheory.SheafLES.equivZero_mk₀]
  exact GlobalTheory.SiteCoh.zeroEquiv_mk₀ F W φ

theorem hPull_zero {X Y : TopCat.{0}} (f : X ⟶ Y) {G : AbSheaf Y} {G' : AbSheaf X}
    (φ : G ⟶ (push f).obj G') (z : Sheaf.H.{0} G 0) :
    Sheaf.H.equiv₀ G' isTerminalTop (hPull f φ 0 z) =
      GroundTheory.Arith.SchemeCoh.res G'.obj (le_top : (⊤ : Opens X) ≤ (Opens.map f).obj ⊤)
        (φ.hom.app (op ⊤) (Sheaf.H.equiv₀ G isTerminalTop z)) := by
  obtain ⟨y, rfl⟩ := (GlobalTheory.SiteCoh.terminalEquiv G 0 isTerminalTop).surjective z
  change Sheaf.H.equiv₀ G' isTerminalTop (GlobalTheory.SiteCoh.terminalEquiv G' 0 isTerminalTop
    (pull.{0, 0} f φ 0 (homOfLE le_top : (⊤ : Opens X) ⟶ (Opens.map f).obj ⊤)
      ((GlobalTheory.SiteCoh.terminalEquiv G 0 isTerminalTop).symm
        (GlobalTheory.SiteCoh.terminalEquiv G 0 isTerminalTop y)))) = _
  rw [AddEquiv.symm_apply_apply, GlobalTheory.SiteCoh.equiv₀_terminalEquiv,
    GlobalTheory.SiteCoh.equiv₀_terminalEquiv, zeroEquiv_eq_equivZero, zeroEquiv_eq_equivZero,
    GlobalTheory.SheafPull.equivZero_pull]
  rfl

theorem cechHZeroEquivH_pull {X Y : TopCat.{0}} (f : X ⟶ Y) {κ ι : Type} (V : κ → Opens Y)
    (hV : iSup V = ⊤) (U : ι → Opens X) (hU : iSup U = ⊤) (τ : ι → κ)
    (hτ : ∀ i, U i ≤ (Opens.map f).obj (V (τ i)))
    {G : AbSheaf Y} {G' : AbSheaf X} (φ : G ⟶ (push f).obj G') (x : GroundTheory.Arith.SchemeCoh.cechH G.obj V 0) :
    (GroundTheory.Arith.SchemeCoh.cechHZeroEquivH G' U hU : GroundTheory.Arith.SchemeCoh.cechH G'.obj U 0 ≃+ Sheaf.H.{0} G' 0) (cechPullH f φ.hom V U τ hτ 0 x) =
      hPull f φ 0 ((GroundTheory.Arith.SchemeCoh.cechHZeroEquivH G V hV : GroundTheory.Arith.SchemeCoh.cechH G.obj V 0 ≃+ Sheaf.H.{0} G 0) x) := by
  obtain ⟨σ, hσ, rfl⟩ := exists_cls x
  obtain ⟨s, hs⟩ := globalCocycle_surjective G.obj V G.property hV ⟨σ, (mem_cocycles σ).2 hσ⟩
  have hσs : σ = (globalCocycle G.obj V s).1 := (congrArg Subtype.val hs).symm
  apply (Sheaf.H.equiv₀ G' isTerminalTop).injective
  rw [hPull_zero, cechPullH_cls]
  simp only [GroundTheory.Arith.SchemeCoh.cechHZeroEquivH, AddEquiv.trans_apply, AddEquiv.apply_symm_apply]
  rw [cechHZeroEquiv_cls G.obj V G.property hV s σ hσ hσs]
  refine cechHZeroEquiv_cls G'.obj U G'.property hU _ _ _ ?_
  rw [hσs]
  exact pullCoch_globalCocycle f φ.hom V U τ hτ s

end GlobalTheory.CompanionTheory.CechZero
