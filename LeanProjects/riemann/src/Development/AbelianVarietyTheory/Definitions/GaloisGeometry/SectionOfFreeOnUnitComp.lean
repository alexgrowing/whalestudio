import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsMatrixForm
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsStrictlySemistableAlt
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.YonedaAddNaturalityLeft
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsGrothendieckAbelianPresheaf

noncomputable section

open CategoryTheory Limits AlgebraicGeometry Opposite Abelian

namespace GlobalTheory.Et

section Restriction

variable {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S)

abbrev resShv : Shv S ⥤ Shv R := ChangeRing.res Scheme.proetaleTopology.{0} (RingHom.ulift.{1, 1} φ)

example : PreservesFiniteLimits (resShv φ) := inferInstance
example : PreservesFiniteColimits (resShv φ) := inferInstance

def freeOnUnit (X : Scheme.{0}) : (freeOn R).obj X ⟶ (resShv φ).obj ((freeOn S).obj X) :=
  ChangeRing.freeUnit _ (RingHom.ulift.{1, 1} φ) (uliftYoneda.{1}.obj X)

theorem freeOnUnit_comp_bijective (X : Scheme.{0}) (G : Shv S) :
    Function.Bijective fun g : (freeOn S).obj X ⟶ G => freeOnUnit φ X ≫ (resShv φ).map g := by
  have h : (fun g : (freeOn S).obj X ⟶ G => freeOnUnit φ X ≫ (resShv φ).map g) =
      ChangeRing.resEquiv _ (RingHom.ulift.{1, 1} φ) (uliftYoneda.{1}.obj X) G :=
    funext (ChangeRing.freeUnit_comp _ (RingHom.ulift.{1, 1} φ) (uliftYoneda.{1}.obj X))
  rw [h]
  exact Equiv.bijective _

def resEquivHS (G : Shv S) (n : ℕ) (X : Scheme.{0}) : HS S G n X ≃+ HS R ((resShv φ).obj G) n X :=
  ChangeRing.cmp _ (RingHom.ulift.{1, 1} φ) (uliftYoneda.{1}.obj X) G n

theorem resEquivHS_apply (G : Shv S) (n : ℕ) (X : Scheme.{0}) (y : HS S G n X) :
    resEquivHS φ G n X y = (Ext.mk₀ (freeOnUnit φ X)).comp (y.mapExactFunctor (resShv φ)) (zero_add n) := rfl

def chgS {F : Shv R} {G : Shv S} (u : F ⟶ (resShv φ).obj G) (n : ℕ) (X : Scheme.{0}) : HS R F n X →+ HS S G n X :=
  ChangeRing.change _ (RingHom.ulift.{1, 1} φ) u (uliftYoneda.{1}.obj X) n

theorem resEquivHS_chgS {F : Shv R} {G : Shv S} (u : F ⟶ (resShv φ).obj G) (n : ℕ) (X : Scheme.{0})
    (x : HS R F n X) : resEquivHS φ G n X (chgS φ u n X x) = x.comp (Ext.mk₀ u) (add_zero n) :=
  ChangeRing.cmp_change _ _ u _ n x

theorem chgS_mk₀ {F : Shv R} {G : Shv S} (u : F ⟶ (resShv φ).obj G) (X : Scheme.{0}) (g : (freeOn R).obj X ⟶ F)
    (g' : (freeOn S).obj X ⟶ G) (h : freeOnUnit φ X ≫ (resShv φ).map g' = g ≫ u) :
    chgS φ u 0 X (Ext.mk₀ g) = Ext.mk₀ g' := by
  apply (resEquivHS φ G 0 X).injective
  rw [resEquivHS_chgS, resEquivHS_apply, Ext.mapExactFunctor_mk₀, Ext.mk₀_comp_mk₀, Ext.mk₀_comp_mk₀, h]

variable (R) in

def sectionOf (X : Scheme.{0}) (F : Shv R) : ((freeOn R).obj X ⟶ F) ≃ F.obj.obj (op X) :=
  (ChangeRing.freeEquiv Scheme.proetaleTopology.{0} (uliftYoneda.{1}.obj X) F).trans uliftYonedaEquiv

theorem sectionOf_comp (X : Scheme.{0}) {F G : Shv R} (g : (freeOn R).obj X ⟶ F) (u : F ⟶ G) :
    sectionOf R X G (g ≫ u) = u.hom.app (op X) (sectionOf R X F g) := rfl

theorem sectionOf_freeOnUnit_comp (X : Scheme.{0}) {G : Shv S} (g : (freeOn S).obj X ⟶ G) :
    sectionOf R X ((resShv φ).obj G) (freeOnUnit φ X ≫ (resShv φ).map g) = sectionOf S X G g :=
  (congrArg (sectionOf R X ((resShv φ).obj G))
    (ChangeRing.freeUnit_comp _ (RingHom.ulift.{1, 1} φ) (uliftYoneda.{1}.obj X) g)).trans
    (congrArg uliftYonedaEquiv
      (ChangeRing.freeEquiv_resEquiv _ (RingHom.ulift.{1, 1} φ) (uliftYoneda.{1}.obj X) G g))

def extendFree {X Z : Scheme.{0}} (t : (freeOn R).obj X ⟶ (freeOn R).obj Z) : (freeOn S).obj X ⟶ (freeOn S).obj Z :=
  (Equiv.ofBijective _ (freeOnUnit_comp_bijective φ X ((freeOn S).obj Z))).symm (t ≫ freeOnUnit φ Z)

end Restriction

section Coefficients

variable {R S T : Type} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
  [CommRing S] [TopologicalSpace S] [IsTopologicalRing S] [CommRing T] [TopologicalSpace T] [IsTopologicalRing T]
  (φ : R →+* S) (hφ : Continuous φ)

def coefPreMap : coefPre R ⟶ coefPre S ⋙ ModuleCat.restrictScalars.{1} (RingHom.ulift.{1, 1} φ) where
  app U := ModuleCat.ofHom (Y := (ModuleCat.restrictScalars.{1} (RingHom.ulift.{1, 1} φ)).obj ((coefPre S).obj U))
    { toFun := fun g => (ULift.up ((⟨φ, hφ⟩ : C(R, S)).comp g.down) : ULift.{1} C(U.unop, S))
      map_add' := fun a b => congrArg ULift.up (ContinuousMap.ext fun x => map_add φ (a.down x) (b.down x))
      map_smul' := fun r a => congrArg ULift.up (ContinuousMap.ext fun x => map_mul φ r.down (a.down x)) }
  naturality _ _ _ := rfl

def coefMap : coef R ⟶ (resShv φ).obj (coef S) :=
  ((sheafificationAdjunction _ _).homEquiv (coefPre R) ((resShv φ).obj (coef S))).symm
    (coefPreMap φ hφ ≫ Functor.whiskerRight (toSheafify _ (coefPre S)) _)

theorem coefMap_toSheafify (U : Scheme.{0}ᵒᵖ) (g : C(U.unop, R)) :
    (coefMap φ hφ).hom.app U ((toSheafify Scheme.proetaleTopology.{0} (coefPre R)).app U (ULift.up g)) =
      (toSheafify Scheme.proetaleTopology.{0} (coefPre S)).app U (ULift.up ((⟨φ, hφ⟩ : C(R, S)).comp g)) := by
  have h : toSheafify Scheme.proetaleTopology.{0} (coefPre R) ≫ (coefMap φ hφ).hom =
      coefPreMap φ hφ ≫ Functor.whiskerRight (toSheafify _ (coefPre S)) _ :=
    ((sheafificationAdjunction _ _).homEquiv (coefPre R) ((resShv φ).obj (coef S))).apply_symm_apply _
  exact ConcreteCategory.congr_hom (NatTrans.congr_app h U) (ULift.up g)

def chg (n : ℕ) (X : Scheme.{0}) : H R n X →ₛₗ[φ] H S n X where
  toFun x := chgS φ (coefMap φ hφ) n X x
  map_add' x y := (chgS φ (coefMap φ hφ) n X).map_add x y
  map_smul' r x := ChangeRing.change_smul _ (RingHom.ulift.{1, 1} φ) (coefMap φ hφ) _ n (ULift.up r) x

variable (R) in
theorem toSheafify_e_mk₀ (X : Scheme.{0}) (g : (freeOn R).obj X ⟶ coef R) :
    (toSheafify Scheme.proetaleTopology.{0} (coefPre R)).app (op X) (ULift.up (H0.e R X (Ext.mk₀ g))) =
      sectionOf R X (coef R) g := by
  have h : Ext.addEquiv₀ (X := (freeOn R).obj X) (Y := coef R) (Ext.mk₀ g) = g := Ext.addEquiv₀.apply_symm_apply g
  have key : (toSheafify Scheme.proetaleTopology.{0} (coefPre R)).app (op X) (ULift.up (H0.e R X (Ext.mk₀ g))) =
      (toSheafify Scheme.proetaleTopology.{0} (coefPre R)).app (op X) ((isoSheafify _ (H0.sh R)).inv.app (op X)
        (sectionOf R X (coef R) (Ext.addEquiv₀ (X := (freeOn R).obj X) (Y := coef R) (Ext.mk₀ g)))) := rfl
  exact key.trans ((ConcreteCategory.congr_hom ((isoSheafify _ (H0.sh R)).inv_hom_id_app (op X)) _).trans
    (congrArg (sectionOf R X (coef R)) h))

variable (R) in
theorem toSheafify_up_injective (U : Scheme.{0}ᵒᵖ) {a b : C(U.unop, R)}
    (h : (toSheafify Scheme.proetaleTopology.{0} (coefPre R)).app U (ULift.up a) =
      (toSheafify Scheme.proetaleTopology.{0} (coefPre R)).app U (ULift.up b)) : a = b :=
  congrArg ULift.down (((isoSheafify _ (H0.sh R)).app U).toLinearEquiv.injective h)

theorem e_chg (X : Scheme.{0}) (x : H R 0 X) : H0.e S X (chg φ hφ 0 X x) = (⟨φ, hφ⟩ : C(R, S)).comp (H0.e R X x) := by
  obtain ⟨g, rfl⟩ := (Ext.mk₀_bijective ((freeOn R).obj X) (coef R)).surjective x
  obtain ⟨g', hg'⟩ := (freeOnUnit_comp_bijective φ X (coef S)).surjective (g ≫ coefMap φ hφ)
  have h1 : chg φ hφ 0 X (Ext.mk₀ g) = Ext.mk₀ g' := chgS_mk₀ φ (coefMap φ hφ) X g g' hg'
  have h2 := sectionOf_freeOnUnit_comp φ X g'
  have h3 := sectionOf_comp X g (coefMap φ hφ)
  have h4 := coefMap_toSheafify φ hφ (op X) (H0.e R X (Ext.mk₀ g))
  have h5 := congrArg ((coefMap φ hφ).hom.app (op X)) (toSheafify_e_mk₀ R X g)
  have h6 := congrArg (sectionOf R X ((resShv φ).obj (coef S))) hg'
  rw [h1]
  exact toSheafify_up_injective S (op X)
    ((toSheafify_e_mk₀ S X g').trans (h2.symm.trans (h6.trans (h3.trans (h5.symm.trans h4)))))

end Coefficients

section Examples

example (n : ℕ) (X : Scheme.{0}) (x : H (ZMod 4) n X) :
    chg (ZMod.castHom (by decide : 2 ∣ 4) (ZMod 2)) continuous_of_discreteTopology n X ((2 : ZMod 4) • x) = 0 := by
  rw [LinearMap.map_smulₛₗ, (by decide : ZMod.castHom (by decide : 2 ∣ 4) (ZMod 2) 2 = 0), zero_smul]

example (X : Scheme.{0}) :
    chg (ZMod.castHom (by decide : 2 ∣ 4) (ZMod 2)) continuous_of_discreteTopology 0 X
      ((H0.e (ZMod 4) X).symm (ContinuousMap.const X 3)) = (H0.e (ZMod 2) X).symm (ContinuousMap.const X 1) := by
  apply (H0.e (ZMod 2) X).injective
  rw [e_chg, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
  ext x
  exact (by decide : ZMod.castHom (by decide : 2 ∣ 4) (ZMod 2) 3 = 1)

example (X : Scheme.{0}) [Nonempty X] :
    chg (ZMod.castHom (by decide : 2 ∣ 4) (ZMod 2)) continuous_of_discreteTopology 0 X ≠ 0 := by
  intro h
  have h1 := e_chg (ZMod.castHom (by decide : 2 ∣ 4) (ZMod 2)) continuous_of_discreteTopology X
    ((H0.e (ZMod 4) X).symm 1)
  rw [h, LinearMap.zero_apply, map_zero, LinearEquiv.apply_symm_apply] at h1
  exact absurd (DFunLike.congr_fun h1 (Classical.arbitrary X))
    (by decide : (0 : ZMod 2) ≠ ZMod.castHom (by decide : 2 ∣ 4) (ZMod 2) 1)

end Examples

end GlobalTheory.Et

end
