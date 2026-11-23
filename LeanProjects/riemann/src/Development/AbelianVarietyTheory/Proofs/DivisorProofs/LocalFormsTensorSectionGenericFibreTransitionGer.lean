import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.UnifAlong
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpMapGermFromSpec
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.KeyEven
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

noncomputable section

namespace GlobalTheory.KeySecRel

theorem appLE_map' {X Y : Scheme.{0}} (p : Y ⟶ X) {U V : X.Opens} (hVU : V ≤ U) {W : Y.Opens} (h : W ≤ p ⁻¹ᵁ V)
    (h' : W ≤ p ⁻¹ᵁ U) (a : Γ(X, U)) :
    (p.appLE V W h).hom ((X.presheaf.map (homOfLE hVU).op).hom a) = (p.appLE U W h').hom a := by
  rw [← CommRingCat.comp_apply, Scheme.Hom.map_appLE]

theorem appLE_app' {X Y S : Scheme.{0}} (p : Y ⟶ X) (π : X ⟶ S) {U : S.Opens} {W : Y.Opens}
    (h : W ≤ p ⁻¹ᵁ (π ⁻¹ᵁ U)) (h' : W ≤ (p ≫ π) ⁻¹ᵁ U) (a : Γ(S, U)) :
    (p.appLE _ W h).hom ((π.app U).hom a) = ((p ≫ π).appLE U W h').hom a := by
  rw [← CommRingCat.comp_apply, Scheme.Hom.comp_appLE]

theorem appLE_sec_tens {X Y S : Scheme.{0}} (p : Y ⟶ X) (π : X ⟶ S) (A : LB X) (hA : A.IsLB) (δ : LB S)
    (σ : (CechPic.tens A (δ.pull π)).Sec) (l : A.ι) (i i' : δ.ι) (W : Y.Opens)
    (h : W ≤ p ⁻¹ᵁ (CechPic.tens A (δ.pull π)).U (l, fun _ => i))
    (h' : W ≤ p ⁻¹ᵁ (CechPic.tens A (δ.pull π)).U (l, fun _ => i'))
    (hW : W ≤ (p ≫ π) ⁻¹ᵁ (δ.U i ⊓ δ.U i')) :
    (p.appLE _ W h).hom (σ.f (l, fun _ => i)) =
      ((p ≫ π).appLE _ W hW).hom (δ.g i i' : Γ(S, δ.U i ⊓ δ.U i')) * (p.appLE _ W h').hom (σ.f (l, fun _ => i')) := by
  have hh : W ≤ p ⁻¹ᵁ ((CechPic.tens A (δ.pull π)).U (l, fun _ => i) ⊓ (CechPic.tens A (δ.pull π)).U (l, fun _ => i')) :=
    fun y hy => ⟨h hy, h' hy⟩
  have e := congrArg (p.appLE _ W hh).hom (σ.compat (l, fun _ => i) (l, fun _ => i'))
  rw [map_mul, appLE_map' p _ hh h, appLE_map' p _ hh h'] at e
  rw [e]
  congr 1
  have h1 : W ≤ p ⁻¹ᵁ (A.U l) := fun y hy => (h hy).1
  have h11 : W ≤ p ⁻¹ᵁ (A.U l ⊓ A.U l) := fun y hy => ⟨h1 hy, h1 hy⟩
  have hg : (p.appLE _ W h11).hom (A.g l l : Γ(X, A.U l ⊓ A.U l)) = 1 := by
    have := congrArg (fun u : Γ(X, A.U l)ˣ => (p.appLE _ W h1).hom (u : Γ(X, A.U l))) (hA.g_self l)
    simp only [Units.val_one, map_one] at this
    rw [← this]
    exact (appLE_map' p _ h1 h11 _).symm
  have h2 : W ≤ p ⁻¹ᵁ ((δ.pull π).U (fun _ => i) ⊓ (δ.pull π).U (fun _ => i')) := fun y hy => ⟨(h hy).2, (h' hy).2⟩
  have hd : ((δ.pull π).g (fun _ => i) (fun _ => i') : Γ(X, (δ.pull π).U (fun _ => i) ⊓ (δ.pull π).U (fun _ => i'))) =
      (X.presheaf.map (homOfLE (le_inf (inf_le_left.trans (LB.wchart_le δ (fun _ : PUnit => π) (fun _ => i) PUnit.unit))
        (inf_le_right.trans (LB.wchart_le δ (fun _ : PUnit => π) (fun _ => i') PUnit.unit)) :
        (δ.pull π).U (fun _ => i) ⊓ (δ.pull π).U (fun _ => i') ≤ π ⁻¹ᵁ (δ.U i ⊓ δ.U i'))).op).hom
        ((π.app _).hom (δ.g i i' : Γ(S, δ.U i ⊓ δ.U i'))) := by
    unfold LB.pull LB.LinComb
    dsimp only
    erw [Fintype.prod_unique, zpow_one]
    rfl
  refine (map_mul _ _ _).trans ?_
  refine (congrArg₂ (· * ·) ((appLE_map' p _ hh h11 _).trans hg) (appLE_map' p _ hh h2 _)).trans ?_
  rw [_root_.one_mul]
  refine (congrArg (p.appLE _ W h2).hom hd).trans ?_
  have hW' : W ≤ p ⁻¹ᵁ (π ⁻¹ᵁ (δ.U i ⊓ δ.U i')) := hW
  exact (appLE_map' p _ h2 hW' _).trans (appLE_app' p π hW' hW _)

theorem genPt_appLE {S : Scheme.{0}} [IsIntegral S] (U : S.Opens) (hU : genericPoint S ∈ U) (a : Γ(S, U)) :
    ((KeyVals.genPt S).appLE U ⊤ (KeyVals.genPt_le U hU)).hom a =
      (Scheme.ΓSpecIso (CommRingCat.of (KeyVals.FF S))).inv.hom (S.presheaf.germ U (genericPoint S) hU a) := by
  have e := Scheme.fromSpecStalk_app (X := S) (x := genericPoint S) hU
  have : (KeyVals.genPt S).appLE U ⊤ (KeyVals.genPt_le U hU) =
      S.presheaf.germ U (genericPoint S) hU ≫ (Scheme.ΓSpecIso (S.presheaf.stalk (genericPoint S))).inv := by
    unfold KeyVals.genPt Scheme.Hom.appLE
    erw [e]
    simp only [Category.assoc]
    erw [← Functor.map_comp]
    refine congrArg (fun z => _ ≫ z) ?_
    refine (congrArg (fun z => _ ≫ (Spec (S.presheaf.stalk (genericPoint S))).presheaf.map z)
      (Subsingleton.elim _ (𝟙 _))).trans ?_
    rw [CategoryTheory.Functor.map_id, Category.comp_id]
  rw [this]
  rfl

theorem locSec_eq_germ_mul : ∀ (S : Scheme.{0}) [IsIntegral S] (G : Over S) [GrpObj G] [IsCommMonObj G] (L : RigLB G) (δ : LB S)
    (σ : (CechPic.tens L.L (δ.pull G.hom)).Sec), δ.IsLB → ∀ (i i' : δ.ι) (h2 : genericPoint S ∈ δ.U i ⊓ δ.U i')
    (t t' : (KeyVals.bL L (KeyVals.genPt S)).L.Sec), KeyVals.IsLocSec σ i (KeyVals.genPt S) t →
    KeyVals.IsLocSec σ i' (KeyVals.genPt S) t' → ∀ j, t.f j =
      constFn (KeyVals.bG G (KeyVals.genPt S)).hom _ (S.presheaf.germ _ (genericPoint S) h2 (δ.g i i' : Γ(S, δ.U i ⊓ δ.U i'))) * t'.f j := by
  intro S _ G _ _ L δ σ _ i i' h2 t t' ht ht' j
  have hc : pullback.fst G.hom (KeyVals.genPt S) ≫ G.hom =
      (KeyVals.bG G (KeyVals.genPt S)).hom ≫ KeyVals.genPt S := pullback.condition
  have hW : (KeyVals.bL L (KeyVals.genPt S)).L.U j ≤
      (pullback.fst G.hom (KeyVals.genPt S) ≫ G.hom) ⁻¹ᵁ (δ.U i ⊓ δ.U i') := by
    rw [hc]
    exact fun y _ => KeyVals.genPt_le _ h2 (Set.mem_univ _)
  have hl : (KeyVals.bL L (KeyVals.genPt S)).L.U j ≤
      pullback.fst G.hom (KeyVals.genPt S) ⁻¹ᵁ L.L.U (j PUnit.unit) :=
    LB.wchart_le L.L (fun _ : PUnit => pullback.fst G.hom (KeyVals.genPt S)) j PUnit.unit
  have h : (KeyVals.bL L (KeyVals.genPt S)).L.U j ≤ pullback.fst G.hom (KeyVals.genPt S) ⁻¹ᵁ
      (CechPic.tens L.L (δ.pull G.hom)).U (j PUnit.unit, fun _ => i) :=
    fun y hy => ⟨hl hy, Set.mem_iInter.2 fun _ => (hW hy).1⟩
  have h' : (KeyVals.bL L (KeyVals.genPt S)).L.U j ≤ pullback.fst G.hom (KeyVals.genPt S) ⁻¹ᵁ
      (CechPic.tens L.L (δ.pull G.hom)).U (j PUnit.unit, fun _ => i') :=
    fun y hy => ⟨hl hy, Set.mem_iInter.2 fun _ => (hW hy).2⟩
  rw [ht j h, ht' j h']
  refine (appLE_sec_tens _ G.hom L.L L.isLB δ σ _ i i' _ h h' hW).trans ?_
  congr 1
  unfold constFn
  rw [← genPt_appLE, ← CommRingCat.comp_apply]
  erw [Scheme.Hom.appLE_comp_appLE]
  have key : ∀ {Y : Scheme.{0}} (f f' : Y ⟶ S) (_ : f = f') (U : S.Opens) (W : Y.Opens) (a : W ≤ f ⁻¹ᵁ U)
      (a' : W ≤ f' ⁻¹ᵁ U) (x : Γ(S, U)), (f.appLE U W a).hom x = (f'.appLE U W a').hom x := by
    intro Y f f' e; subst e; intros; rfl
  exact key _ _ hc _ _ _ _ _

end GlobalTheory.KeySecRel

end
