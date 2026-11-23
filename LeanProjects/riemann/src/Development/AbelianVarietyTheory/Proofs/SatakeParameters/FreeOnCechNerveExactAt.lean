import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsMatrixForm
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CechAcyclic
open CategoryTheory Limits AlgebraicGeometry Opposite Abelian Simplicial GlobalTheory.Et
universe v u

noncomputable section

namespace GlobalTheory.Et.FreeCech

variable {U V : Scheme.{0}} (π : V ⟶ U) (W : Scheme.{0})

def Img : Type 1 := {t : ULift.{1} (W ⟶ U) // ∃ s : W ⟶ V, s ≫ π = t.down}

def toImg : ULift.{1} (W ⟶ V) ⟶ Img π W :=
  TypeCat.ofHom fun s => ⟨⟨s.down ≫ π⟩, s.down, rfl⟩

def split : SplitEpi (toImg π W) where
  section_ := TypeCat.ofHom fun t => ⟨t.2.choose⟩
  id := by
    ext t
    exact Subtype.ext (ULift.ext _ _ t.2.choose_spec)

abbrev Pow (k : ℕ) : Scheme.{0} := widePullback.{0} U (fun _ : Fin (k + 1) => V) (fun _ => π)

def ptCone (k : ℕ) : Cone (WidePullbackShape.wideCospan (Img π W)
    (fun _ : Fin (k + 1) => ULift.{1} (W ⟶ V)) (fun _ => toImg π W)) :=
  WidePullbackShape.mkCone (X := ULift.{1} (W ⟶ Pow π k))
    (TypeCat.ofHom fun x => (⟨⟨x.down ≫ WidePullback.base _⟩, x.down ≫ WidePullback.π _ 0, by simp⟩ : Img π W))
    (fun j => TypeCat.ofHom fun x => (⟨x.down ≫ WidePullback.π _ j⟩ : ULift.{1} (W ⟶ V)))
    (fun j => by
      ext x
      exact Subtype.ext (ULift.ext _ _
        (show (x.down ≫ WidePullback.π _ j) ≫ π = x.down ≫ WidePullback.base _ by simp)))

def ptConeIsLimit (k : ℕ) : IsLimit (ptCone π W k) where
  lift c := TypeCat.ofHom fun x => (⟨WidePullback.lift (c.π.app none x).1.down
    (fun j => (c.π.app (some j) x).down)
    (fun j => congrArg (fun t : Img π W => t.1.down)
      (types_congr_hom (c.w (WidePullbackShape.Hom.term j)) x))⟩ : ULift.{1} (W ⟶ Pow π k))
  fac c j := by
    ext x
    cases j with
    | none => exact Subtype.ext (ULift.ext _ _ (WidePullback.lift_base ..))
    | some j => exact ULift.ext _ _ (WidePullback.lift_π ..)
  uniq c m hm := by
    ext x
    apply ULift.ext
    apply WidePullback.hom_ext
    · intro j
      exact (congrArg ULift.down (types_congr_hom (hm (some j)) x)).trans
        (WidePullback.lift_π (fun _ => π) _ (fun j => (c.π.app (some j) x).down) _ j).symm
    · exact (congrArg (fun t : Img π W => t.1.down) (types_congr_hom (hm none) x)).trans
        (WidePullback.lift_base ..).symm

end GlobalTheory.Et.FreeCech

namespace GlobalTheory.Et.FreeCech

variable {U V : Scheme.{0}} (π : V ⟶ U) (W : Scheme.{0})

abbrev pts : Scheme.{0} ⥤ Type 1 := uliftYoneda.{1} ⋙ (evaluation Scheme.{0}ᵒᵖ (Type 1)).obj (op W)

def cechIso : (Arrow.mk π).cechNerve ⋙ pts W ≅ (Arrow.mk (toImg π W)).cechNerve :=
  NatIso.ofComponents (fun n => (ptConeIsLimit π W n.unop.len).conePointUniqueUpToIso (limit.isLimit _))
    (fun {n m} f => by
      apply WidePullback.hom_ext
      · intro j
        have h1 := (ptConeIsLimit π W m.unop.len).conePointUniqueUpToIso_hom_comp (limit.isLimit _) (some j)
        have h2 := (ptConeIsLimit π W n.unop.len).conePointUniqueUpToIso_hom_comp (limit.isLimit _)
          (some (f.unop.toOrderHom j))
        simp only [Category.assoc, Arrow.cechNerve_map, WidePullback.lift_π]
        erw [h1, h2]
        ext x
        apply ULift.ext
        show x.down ≫ ((Arrow.mk π).cechNerve.map f) ≫ WidePullback.π _ j = x.down ≫ WidePullback.π _ _
        exact congrArg (fun g => x.down ≫ g) (WidePullback.lift_π (fun _ => π) _ _ _ j)
      · have h1 := (ptConeIsLimit π W m.unop.len).conePointUniqueUpToIso_hom_comp (limit.isLimit _) none
        have h2 := (ptConeIsLimit π W n.unop.len).conePointUniqueUpToIso_hom_comp (limit.isLimit _) none
        simp only [Category.assoc, Arrow.cechNerve_map, WidePullback.lift_base]
        erw [h1, h2]
        ext x
        apply Subtype.ext
        apply ULift.ext
        show x.down ≫ ((Arrow.mk π).cechNerve.map f) ≫ WidePullback.base _ = x.down ≫ WidePullback.base _
        exact congrArg (fun g => x.down ≫ g) (WidePullback.lift_base (fun _ => π) _ _ _))

end GlobalTheory.Et.FreeCech

namespace GlobalTheory.Et.FreeCech

variable {U V : Scheme.{0}} (π : V ⟶ U) (W : Scheme.{0})

theorem exactAt_pts (R : Type) [CommRing R] (k : ℕ) :
    ((AlgebraicTopology.alternatingFaceMapComplex (ModuleCat.{1} (ULift.{1} R))).obj
      (((Arrow.mk π).cechNerve ⋙ pts W) ⋙ ModuleCat.free (ULift.{1} R))).ExactAt (k + 1) := by
  let ed := (Arrow.AugmentedCechNerve.extraDegeneracy (Arrow.mk (toImg π W)) (split π W)).map
    (ModuleCat.free (ULift.{1} R))
  let h := ed.homotopyEquiv
  haveI := h.quasiIso_hom
  have h1 := (exactAt_iff_of_quasiIsoAt h.hom (k + 1)).2 (ChainComplex.exactAt_succ_single_obj _ _)
  exact h1.of_iso ((AlgebraicTopology.alternatingFaceMapComplex _).mapIso
    (Functor.isoWhiskerRight (cechIso π W) _)).symm

end GlobalTheory.Et.FreeCech

namespace GlobalTheory.Et

theorem freeOn_cechNerve_exactAt {R : Type} [CommRing R] {U V : Scheme.{0}} (π : V ⟶ U) (n : ℕ) :
    ((AlgebraicTopology.alternatingFaceMapComplex (Shv R)).obj
      ((Arrow.mk π).cechNerve ⋙ freeOn R)).ExactAt (n + 1) := by
  let P := (Arrow.mk π).cechNerve ⋙ uliftYoneda.{1} ⋙
    (Functor.whiskeringRight _ _ _).obj (ModuleCat.free (ULift.{1} R))
  let K := (AlgebraicTopology.alternatingFaceMapComplex _).obj P
  have hK : K.ExactAt (n + 1) := by
    rw [HomologicalComplex.exactAt_iff, ShortComplex.exact_iff_isZero_homology]
    refine Functor.isZero _ fun W => ?_
    refine IsZero.of_iso ?_ ((K.sc (n + 1)).mapHomologyIso ((evaluation _ _).obj W)).symm
    rw [← ShortComplex.exact_iff_isZero_homology]
    have h := FreeCech.exactAt_pts π (unop W) R n
    have e := Functor.congr_obj (AlgebraicTopology.map_alternatingFaceMapComplex
      ((evaluation Scheme.{0}ᵒᵖ (ModuleCat.{1} (ULift.{1} R))).obj W)) P
    have h' : ((((evaluation Scheme.{0}ᵒᵖ (ModuleCat.{1} (ULift.{1} R))).obj W).mapHomologicalComplex _).obj
        K).ExactAt (n + 1) := by
      rw [show K = (AlgebraicTopology.alternatingFaceMapComplex _).obj P from rfl]
      erw [e]
      exact h
    exact h'
  have e := Functor.congr_obj (AlgebraicTopology.map_alternatingFaceMapComplex
    (presheafToSheaf (Scheme.proetaleTopology.{0}) (ModuleCat.{1} (ULift.{1} R)))) P
  have h2 := hK.map (presheafToSheaf (Scheme.proetaleTopology.{0}) (ModuleCat.{1} (ULift.{1} R)))
  change (((presheafToSheaf _ _).mapHomologicalComplex _).obj K).ExactAt (n + 1) at h2
  erw [e] at h2
  exact h2

end GlobalTheory.Et
