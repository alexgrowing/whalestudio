import Mathlib
import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.EtaleProperBaseChange
import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.A6supp

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex UpperTheory.Et

private theorem cPre_isSheaf (R : Type) [CommRing R] (T : Type) [AddCommGroup T] [Module R T] [TopologicalSpace T]
    [IsTopologicalAddGroup T] [ContinuousConstSMul R T] :
    Presheaf.IsSheaf Scheme.proetaleTopology.{0} (cPre R T) := by
  rw [Presheaf.isSheaf_iff_isSheaf_forget (s := forget (ModuleCat.{1} (ULift.{1} R))),
    isSheaf_iff_isSheaf_of_type]
  have h := Presieve.isSheaf_of_le _ Scheme.proetaleTopology_le_fpqcTopology
    ((isSheaf_iff_isSheaf_of_type _ _).1 (isSheaf_fpqcTopology_continuousMapPresheaf.{0, 0} T))
  have h' : Presieve.IsSheaf Scheme.proetaleTopology
      (continuousMapPresheaf.{0} T ⋙ uliftFunctor.{1}) :=
    (Presieve.isSheaf_comp_uliftFunctor_iff _).2 h
  exact Presieve.isSheaf_iso _
    (NatIso.ofComponents (fun U => Iso.refl _) (by intros; rfl) :
      continuousMapPresheaf.{0} T ⋙ uliftFunctor.{1} ≅ cPre R T ⋙ forget _) h'

theorem UpperTheory.continuousSections_bijective_additive_natural :
    ∀ (R : Type) [CommRing R] (T : Type) [AddCommGroup T] [Module R T] [TopologicalSpace T] [IsTopologicalAddGroup T] [ContinuousConstSMul R T] (U : Scheme.{0}),
    Function.Bijective (cSec R T (U := U)) ∧ (∀ a b : C(U, T), cSec R T (a + b) = cSec R T a + cSec R T b) ∧ (∀ (V : Scheme.{0}) (g : V ⟶ U) (a : C(U, T)), rs _ g (cSec R T a) = cSec R T (a.comp g.base.hom)) ∧
    ∀ (T' : Type) [AddCommGroup T'] [Module R T'] [TopologicalSpace T'] [IsTopologicalAddGroup T'] [ContinuousConstSMul R T'] (u : T →L[R] T') (a : C(U, T)), ap (cMap u).hom (cSec R T a) = cSec R T' ((⟨u, u.continuous⟩ : C(T, T')).comp a) := by
  intro R _ T _ _ _ _ _ U
  haveI : IsIso (toSheafify Scheme.proetaleTopology (cPre R T)) :=
    isIso_toSheafify _ (cPre_isSheaf R T)
  refine ⟨?_, ?_, ?_, ?_⟩
  · have hb := ConcreteCategory.bijective_of_isIso
      ((toSheafify Scheme.proetaleTopology (cPre R T)).app (op U))
    exact hb.comp Equiv.ulift.symm.bijective
  · intro a b
    exact map_add (ModuleCat.Hom.hom ((toSheafify Scheme.proetaleTopology (cPre R T)).app (op U)))
      (ULift.up a) (ULift.up b)
  · intro V g a
    exact (congrArg (fun f => ModuleCat.Hom.hom f (ULift.up a))
      ((toSheafify Scheme.proetaleTopology (cPre R T)).naturality g.op)).symm
  · intro T' _ _ _ _ _ u a
    exact congrArg (fun f => ModuleCat.Hom.hom (NatTrans.app f (op U)) (ULift.up a))
      (toSheafify_naturality Scheme.proetaleTopology (cPreMap u)).symm
