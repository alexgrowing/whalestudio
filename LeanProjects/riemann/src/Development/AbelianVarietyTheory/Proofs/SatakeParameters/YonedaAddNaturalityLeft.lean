import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsMatrixForm

noncomputable section

open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.Et

namespace GlobalTheory.Et.H0

variable (R : Type) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]

theorem sh : Presheaf.IsSheaf Scheme.proetaleTopology.{0} (coefPre R) := by
  rw [Presheaf.isSheaf_iff_isSheaf_forget _ _ (CategoryTheory.forget _)]
  have h : Presheaf.IsSheaf Scheme.proetaleTopology.{0} (continuousMapPresheaf.{0} R) :=
    .of_le Scheme.proetaleTopology_le_fpqcTopology (isSheaf_fpqcTopology_continuousMapPresheaf R)
  have h2 : Presheaf.IsSheaf Scheme.proetaleTopology.{0} (continuousMapPresheaf.{0} R ⋙ uliftFunctor.{1}) := by
    rw [isSheaf_iff_isSheaf_of_type] at h ⊢
    exact (Presieve.isSheaf_comp_uliftFunctor _) h
  exact h2

def yonedaAdd (X : Scheme.{0}) (P : Scheme.{0}ᵒᵖ ⥤ ModuleCat.{1} (ULift.{1} R)) :
    (uliftYoneda.{1}.obj X ⋙ ModuleCat.free (ULift.{1} R) ⟶ P) ≃+ P.obj (op X) where
  toEquiv := (((ModuleCat.adj (ULift.{1} R)).whiskerRight Scheme.{0}ᵒᵖ).homEquiv (uliftYoneda.{1}.obj X) P).trans
    uliftYonedaEquiv
  map_add' _ _ := rfl

def eAdd (X : Scheme.{0}) : H R 0 X ≃+ C(X, R) :=
  (Abelian.Ext.addEquiv₀ (X := (freeOn R).obj X) (Y := coef R)).trans <|
  ((sheafificationAdjunction Scheme.proetaleTopology.{0} (ModuleCat.{1} (ULift.{1} R))).homAddEquiv _ (coef R)).trans <|
  (yonedaAdd R X (coef R).obj).trans <|
  ((((isoSheafify _ (sh R)).app (op X)).symm.toLinearEquiv).toAddEquiv.trans AddEquiv.ulift)

theorem eAdd_smul (X : Scheme.{0}) (r : R) (x : H R 0 X) : eAdd R X (r • x) = r • eAdd R X x := by
  have h1 : Abelian.Ext.addEquiv₀ (X := (freeOn R).obj X) (Y := coef R) (r • x) =
      ULift.up r • Abelian.Ext.addEquiv₀ (X := (freeOn R).obj X) (Y := coef R) x :=
    (Abelian.Ext.linearEquiv₀ (R := ULift.{1} R) (X := (freeOn R).obj X) (Y := coef R)).map_smul (ULift.up r) x
  change AddEquiv.ulift ((((isoSheafify _ (sh R)).app (op X)).symm.toLinearEquiv)
      (yonedaAdd R X (coef R).obj ((sheafificationAdjunction _ _).homEquiv _ _
        (Abelian.Ext.addEquiv₀ (X := (freeOn R).obj X) (Y := coef R) (r • x))))) =
    r • AddEquiv.ulift ((((isoSheafify _ (sh R)).app (op X)).symm.toLinearEquiv)
      (yonedaAdd R X (coef R).obj ((sheafificationAdjunction _ _).homEquiv _ _
        (Abelian.Ext.addEquiv₀ (X := (freeOn R).obj X) (Y := coef R) x))))
  rw [h1]
  have h2 : yonedaAdd R X (coef R).obj ((sheafificationAdjunction _ _).homEquiv _ _
      (ULift.up r • Abelian.Ext.addEquiv₀ (X := (freeOn R).obj X) (Y := coef R) x)) =
      ULift.up r • yonedaAdd R X (coef R).obj ((sheafificationAdjunction _ _).homEquiv _ _
        (Abelian.Ext.addEquiv₀ (X := (freeOn R).obj X) (Y := coef R) x)) := rfl
  rw [h2]
  exact (congrArg AddEquiv.ulift (LinearEquiv.map_smul (((isoSheafify _ (sh R)).app (op X)).symm.toLinearEquiv) (ULift.up r) _)).trans rfl

def e (X : Scheme.{0}) : H R 0 X ≃ₗ[R] C(X, R) :=
  { eAdd R X with map_smul' := eAdd_smul R X }

theorem yonedaAdd_naturality_left {X Y : Scheme.{0}} (f : X ⟶ Y) (P : Scheme.{0}ᵒᵖ ⥤ ModuleCat.{1} (ULift.{1} R))
    (g : uliftYoneda.{1}.obj Y ⋙ ModuleCat.free (ULift.{1} R) ⟶ P) :
    yonedaAdd R X P (Functor.whiskerRight (uliftYoneda.{1}.map f) (ModuleCat.free (ULift.{1} R)) ≫ g) =
      P.map f.op (yonedaAdd R Y P g) := by
  change uliftYonedaEquiv ((((ModuleCat.adj (ULift.{1} R)).whiskerRight Scheme.{0}ᵒᵖ).homEquiv (uliftYoneda.{1}.obj X) P)
    (((Functor.whiskeringRight _ _ _).obj (ModuleCat.free (ULift.{1} R))).map (uliftYoneda.{1}.map f) ≫ g)) = _
  rw [Adjunction.homEquiv_naturality_left]
  exact (uliftYonedaEquiv_naturality (F := P ⋙ CategoryTheory.forget _) _ f.op).symm

theorem addEquiv₀_pull {X Y : Scheme.{0}} (f : X ⟶ Y) (x : H R 0 Y) :
    Abelian.Ext.addEquiv₀ (X := (freeOn R).obj X) (Y := coef R) (pull R 0 f x) =
      (freeOn R).map f ≫ Abelian.Ext.addEquiv₀ (X := (freeOn R).obj Y) (Y := coef R) x := by
  obtain ⟨φ, rfl⟩ := (Abelian.Ext.addEquiv₀ (X := (freeOn R).obj Y) (Y := coef R)).symm.surjective x
  change Abelian.Ext.addEquiv₀ ((Abelian.Ext.mk₀ ((freeOn R).map f)).comp (Abelian.Ext.addEquiv₀.symm φ) (zero_add 0)) = _
  rw [AddEquiv.apply_symm_apply, Abelian.Ext.addEquiv₀_symm_apply, Abelian.Ext.mk₀_comp_mk₀]
  exact Abelian.Ext.addEquiv₀.apply_symm_apply _

theorem e_pull {X Y : Scheme.{0}} (f : X ⟶ Y) (x : H R 0 Y) :
    e R X (pull R 0 f x) = (e R Y x).comp f.base.hom := by
  change AddEquiv.ulift ((((isoSheafify _ (sh R)).app (op X)).symm.toLinearEquiv)
      (yonedaAdd R X (coef R).obj ((sheafificationAdjunction _ _).homEquiv _ _
        (Abelian.Ext.addEquiv₀ (X := (freeOn R).obj X) (Y := coef R) (pull R 0 f x))))) =
    (AddEquiv.ulift ((((isoSheafify _ (sh R)).app (op Y)).symm.toLinearEquiv)
      (yonedaAdd R Y (coef R).obj ((sheafificationAdjunction _ _).homEquiv _ _
        (Abelian.Ext.addEquiv₀ (X := (freeOn R).obj Y) (Y := coef R) x))))).comp f.base.hom
  rw [addEquiv₀_pull]
  change AddEquiv.ulift ((((isoSheafify _ (sh R)).app (op X)).symm.toLinearEquiv)
      (yonedaAdd R X (coef R).obj ((sheafificationAdjunction _ _).homEquiv _ _
        ((presheafToSheaf _ _).map (Functor.whiskerRight (uliftYoneda.{1}.map f) (ModuleCat.free (ULift.{1} R))) ≫
          Abelian.Ext.addEquiv₀ (X := (freeOn R).obj Y) (Y := coef R) x)))) = _
  have hn := (sheafificationAdjunction Scheme.proetaleTopology.{0} (ModuleCat.{1} (ULift.{1} R))).homEquiv_naturality_left
    (Functor.whiskerRight (uliftYoneda.{1}.map f) (ModuleCat.free (ULift.{1} R)))
    (Abelian.Ext.addEquiv₀ (X := (freeOn R).obj Y) (Y := coef R) x)
  erw [hn, yonedaAdd_naturality_left]
  generalize yonedaAdd R Y (coef R).obj ((sheafificationAdjunction _ _).homEquiv _ _
        (Abelian.Ext.addEquiv₀ (X := (freeOn R).obj Y) (Y := coef R) x)) = z
  have := NatTrans.naturality_apply (isoSheafify _ (sh R)).inv f.op z
  change AddEquiv.ulift ((isoSheafify _ (sh R)).inv.app (op X) ((coef R).obj.map f.op z)) =
    (AddEquiv.ulift ((isoSheafify _ (sh R)).inv.app (op Y) z)).comp f.base.hom
  erw [this]
  rfl

theorem main :
    Presheaf.IsSheaf Scheme.proetaleTopology.{0} (coefPre R) ∧
      ∃ e : ∀ X : Scheme.{0}, H R 0 X ≃ₗ[R] C(X, R),
        ∀ {X Y : Scheme.{0}} (f : X ⟶ Y) (x : H R 0 Y), e X (pull R 0 f x) = (e Y x).comp f.base.hom :=
  ⟨sh R, e R, fun f x => e_pull R f x⟩

end GlobalTheory.Et.H0
