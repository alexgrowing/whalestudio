import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RingCocone
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex Simplicial TensorProduct GlobalTheory.EtC

namespace GlobalTheory

lemma cechLev_π {f g : Arrow PSh} (F : f ⟶ g) (k : SimplexCategoryᵒᵖ) (j : Fin (k.unop.len + 1)) :
    ((evaluation _ PSh).obj k).map (Arrow.mapCechNerve F) ≫ WidePullback.π (fun _ => g.hom) j =
      WidePullback.π (fun _ => f.hom) j ≫ F.left := by
  simp only [evaluation_obj_map, Arrow.mapCechNerve_app]
  erw [WidePullback.lift_π]

lemma cechLev_base {f g : Arrow PSh} (F : f ⟶ g) (k : SimplexCategoryᵒᵖ) :
    ((evaluation _ PSh).obj k).map (Arrow.mapCechNerve F) ≫
        WidePullback.base (fun _ : Fin (k.unop.len + 1) => g.hom) =
      WidePullback.base (fun _ => f.hom) ≫ F.right := by
  simp only [evaluation_obj_map, Arrow.mapCechNerve_app]
  erw [WidePullback.lift_base]

theorem cech_level_limit (I : Type) [SmallCategory I] [IsCofiltered I] (A : I ⥤ Arrow PSh) (cA : Cone A)
    (hl : IsLimit (Arrow.leftFunc.mapCone cA)) (_hA : ∀ ⦃i j : I⦄ (f : i ⟶ j), IsIso (A.map f).right)
    (hR : ∀ i, IsIso (cA.π.app i).right) (k : SimplexCategoryᵒᵖ) :
    Nonempty (IsLimit (((evaluation _ PSh).obj k).mapCone (SimplicialObject.cechNerve.mapCone cA))) := by
  obtain ⟨i₀⟩ := IsCofiltered.nonempty (C := I)
  let L : ∀ (s : Cone ((A ⋙ SimplicialObject.cechNerve) ⋙ (evaluation _ PSh).obj k))
      (j : Fin (k.unop.len + 1)), s.pt ⟶ cA.pt.left := fun s j =>
    hl.lift
      { pt := s.pt
        π :=
          { app := fun i => s.π.app i ≫ WidePullback.π (fun _ => (A.obj i).hom) j
            naturality := by
              intro i i' f
              have h := s.w f
              simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.id_comp,
                Functor.comp_obj, Arrow.leftFunc_obj, Functor.comp_map, Arrow.leftFunc_map] at h ⊢
              rw [← h]
              exact (Category.assoc _ _ _).trans
                ((congrArg (s.π.app i ≫ ·) (cechLev_π (A.map f) k j)).trans (Category.assoc _ _ _).symm) } }
  have hLfac : ∀ s j i, L s j ≫ (cA.π.app i).left =
      s.π.app i ≫ WidePullback.π (fun _ => (A.obj i).hom) j := by
    intro s j i
    exact hl.fac _ i
  have hLbase : ∀ s j i, L s j ≫ cA.pt.hom ≫ (cA.π.app i).right =
      s.π.app i ≫ WidePullback.base (fun _ : Fin (k.unop.len + 1) => (A.obj i).hom) := by
    intro s j i
    have hw : (cA.π.app i).left ≫ (A.obj i).hom = cA.pt.hom ≫ (cA.π.app i).right := Arrow.w (cA.π.app i)
    rw [← hw, ← Category.assoc, hLfac]
    exact (Category.assoc _ _ _).trans (congrArg (s.π.app i ≫ ·) (WidePullback.π_arrow _ j))
  refine ⟨{ lift := fun s => WidePullback.lift (L s 0 ≫ cA.pt.hom) (L s) (fun j => by
              rw [← cancel_mono (cA.π.app i₀).right, Category.assoc, Category.assoc, hLbase, hLbase])
            fac := ?_
            uniq := ?_ }⟩
  · intro s i
    apply WidePullback.hom_ext
    · intro j
      refine (Category.assoc _ _ _).trans ?_
      refine (congrArg (WidePullback.lift (L s 0 ≫ cA.pt.hom) (L s) _ ≫ ·) (cechLev_π (cA.π.app i) k j)).trans ?_
      refine (Category.assoc _ _ _).symm.trans ?_
      refine (congrArg (· ≫ (cA.π.app i).left) (WidePullback.lift_π _ _ _ _ j)).trans ?_
      exact hLfac s j i
    · refine (Category.assoc _ _ _).trans ?_
      refine (congrArg (WidePullback.lift (L s 0 ≫ cA.pt.hom) (L s) _ ≫ ·) (cechLev_base (cA.π.app i) k)).trans ?_
      refine (Category.assoc _ _ _).symm.trans ?_
      refine (congrArg (· ≫ (cA.π.app i).right) (WidePullback.lift_base _ _ _ _)).trans ?_
      exact (Category.assoc _ _ _).trans (hLbase s 0 i)
  · intro s m hm
    have hmj : ∀ j, m ≫ WidePullback.π (fun _ => cA.pt.hom) j = L s j := by
      intro j
      apply hl.hom_ext
      intro i
      refine Eq.trans ?_ (hLfac s j i).symm
      refine Eq.trans ?_ (congrArg (· ≫ WidePullback.π (fun _ => (A.obj i).hom) j) (hm i))
      refine (Category.assoc _ _ _).trans ?_
      refine Eq.trans ?_ (Category.assoc _ _ _).symm
      exact congrArg (m ≫ ·) (cechLev_π (cA.π.app i) k j).symm
    apply WidePullback.hom_ext
    · intro j
      exact (hmj j).trans (WidePullback.lift_π _ _ _ _ j).symm
    · refine Eq.trans ?_ (WidePullback.lift_base _ _ _ _).symm
      refine Eq.trans ?_ (congrArg (· ≫ cA.pt.hom) (hmj 0))
      refine Eq.trans ?_ (Category.assoc _ _ _).symm
      exact congrArg (m ≫ ·) (WidePullback.π_arrow _ 0).symm

end GlobalTheory
