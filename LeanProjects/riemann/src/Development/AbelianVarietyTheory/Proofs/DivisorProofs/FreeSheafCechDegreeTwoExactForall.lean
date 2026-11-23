import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Pr13Snd
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FreeOnCechNerveExactAt
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.Et GlobalTheory.Et.CovChar.Trip

noncomputable section
namespace GlobalTheory.Et.CovChar.Trip.CechLevels
variable {X Y : Scheme.{0}} (f : Y ⟶ X)

abbrev L (n : ℕ) : Scheme.{0} := widePullback X (fun _ : Fin (n+1) => Y) (fun _ => f)

def e0 : L f 0 ≅ Y where
  hom := WidePullback.π _ 0
  inv := WidePullback.lift f (fun _ => 𝟙 Y) (by simp)
  hom_inv_id := by
    apply WidePullback.hom_ext
    · intro j; fin_cases j; simp [WidePullback.lift_π]
    · simp [WidePullback.lift_base, WidePullback.π_arrow]
  inv_hom_id := by simp [WidePullback.lift_π]

def e1 : L f 1 ≅ pullback f f where
  hom := pullback.lift (WidePullback.π _ 0) (WidePullback.π _ 1) (by simp)
  inv := WidePullback.lift (pullback.fst f f ≫ f) ![pullback.fst f f, pullback.snd f f]
    (by intro j; fin_cases j <;> simp [pullback.condition])
  hom_inv_id := by
    apply WidePullback.hom_ext
    · intro j; fin_cases j
      · simp only [Category.assoc, WidePullback.lift_π]; erw [pullback.lift_fst]; simp
      · simp only [Category.assoc, WidePullback.lift_π]; erw [pullback.lift_snd]; simp
    · simp only [Category.assoc, WidePullback.lift_base]; erw [pullback.lift_fst_assoc]; simp
  inv_hom_id := by
    apply pullback.hom_ext
    · simp only [Category.assoc]; erw [pullback.lift_fst]; simp [WidePullback.lift_π]
    · simp only [Category.assoc]; erw [pullback.lift_snd]; simp [WidePullback.lift_π]

def e2 : L f 2 ≅ Tr f where
  hom := pullback.lift (pullback.lift (WidePullback.π _ 0) (WidePullback.π _ 1) (by simp))
    (pullback.lift (WidePullback.π _ 1) (WidePullback.π _ 2) (by simp)) (by
      erw [pullback.lift_snd, pullback.lift_fst])
  inv := WidePullback.lift (pullback.fst _ _ ≫ pullback.fst f f ≫ f)
    ![pullback.fst _ _ ≫ pullback.fst f f, pullback.fst _ _ ≫ pullback.snd f f, pullback.snd _ _ ≫ pullback.snd f f]
    (by
      intro j; fin_cases j
      · simp
      · show (pullback.fst _ _ ≫ pullback.snd f f) ≫ f = _
        rw [Category.assoc, ← pullback.condition (f := f) (g := f)]
      · show (pullback.snd _ _ ≫ pullback.snd f f) ≫ f = _
        rw [Category.assoc, ← pullback.condition (f := f) (g := f),
          ← pullback.condition_assoc (f := pullback.snd f f) (g := pullback.fst f f),
          ← pullback.condition (f := f) (g := f)])
  hom_inv_id := by
    apply WidePullback.hom_ext
    · intro j; fin_cases j
      · simp only [Category.assoc, WidePullback.lift_π]; erw [pullback.lift_fst_assoc, pullback.lift_fst]; simp
      · simp only [Category.assoc, WidePullback.lift_π]; erw [pullback.lift_fst_assoc, pullback.lift_snd]; simp
      · simp only [Category.assoc, WidePullback.lift_π]; erw [pullback.lift_snd_assoc, pullback.lift_snd]; simp
    · simp only [Category.assoc, WidePullback.lift_base]; erw [pullback.lift_fst_assoc, pullback.lift_fst_assoc]; simp
  inv_hom_id := by
    apply pullback.hom_ext <;> apply pullback.hom_ext
    · simp only [Category.assoc]; erw [pullback.lift_fst_assoc, pullback.lift_fst]; simp [WidePullback.lift_π]
    · simp only [Category.assoc]; erw [pullback.lift_fst_assoc, pullback.lift_snd]; simp [WidePullback.lift_π]
    · simp only [Category.assoc]; erw [pullback.lift_snd_assoc, pullback.lift_fst]; simp [WidePullback.lift_π]; exact pullback.condition
    · simp only [Category.assoc]; erw [pullback.lift_snd_assoc, pullback.lift_snd]; simp [WidePullback.lift_π]

theorem face_π {n : ℕ} (i : Fin (n + 2)) (j : Fin (n + 1)) :
    (Arrow.mk f).cechNerve.δ i ≫ WidePullback.π (fun _ => f) j = WidePullback.π (fun _ => f) (i.succAbove j) := by
  simp only [SimplicialObject.δ, Arrow.cechNerve_map]
  erw [WidePullback.lift_π]
  rfl

theorem cech_nerve_face_one_zero : (Arrow.mk f).cechNerve.δ (0 : Fin 2) ≫ (e0 f).hom = (e1 f).hom ≫ pullback.snd f f := by
  erw [pullback.lift_snd]; exact face_π f 0 0
theorem cech_nerve_face_one_one : (Arrow.mk f).cechNerve.δ (1 : Fin 2) ≫ (e0 f).hom = (e1 f).hom ≫ pullback.fst f f := by
  erw [pullback.lift_fst]; exact face_π f 1 0

theorem cech_nerve_face_two_zero : (Arrow.mk f).cechNerve.δ (0 : Fin 3) ≫ (e1 f).hom = (e2 f).hom ≫ pullback.snd _ _ := by
  apply pullback.hom_ext
  · simp only [Category.assoc]; erw [pullback.lift_fst, pullback.lift_snd_assoc, pullback.lift_fst]; exact face_π f 0 0
  · simp only [Category.assoc]; erw [pullback.lift_snd, pullback.lift_snd_assoc, pullback.lift_snd]; exact face_π f 0 1
theorem cech_nerve_face_two_one : (Arrow.mk f).cechNerve.δ (1 : Fin 3) ≫ (e1 f).hom = (e2 f).hom ≫ pr13 f := by
  apply pullback.hom_ext
  · simp only [Category.assoc, pr13_fst]; erw [pullback.lift_fst, pullback.lift_fst_assoc, pullback.lift_fst]; exact face_π f 1 0
  · simp only [Category.assoc, pr13_snd]; erw [pullback.lift_snd, pullback.lift_snd_assoc, pullback.lift_snd]; exact face_π f 1 1
theorem cech_nerve_face_two_two : (Arrow.mk f).cechNerve.δ (2 : Fin 3) ≫ (e1 f).hom = (e2 f).hom ≫ pullback.fst _ _ := by
  apply pullback.hom_ext
  · simp only [Category.assoc]; erw [pullback.lift_fst, pullback.lift_fst_assoc, pullback.lift_fst]; exact face_π f 2 0
  · simp only [Category.assoc]; erw [pullback.lift_snd, pullback.lift_fst_assoc, pullback.lift_snd]; exact face_π f 2 1

end GlobalTheory.Et.CovChar.Trip.CechLevels

namespace GlobalTheory.Et.CovChar.Trip
open CechLevels in

theorem free_sheaf_cech_degree_two_exact (R : Type) [CommRing R] {X Y : Scheme.{0}} (f : Y ⟶ X) :
    (ShortComplex.mk (d2 f R) (d1 f R) (d2_comp f R)).Exact := by
  have h := freeOn_cechNerve_exactAt (R := R) f 0
  rw [HomologicalComplex.exactAt_iff' _ 2 1 0 (by simp) (by simp)] at h
  refine (ShortComplex.exact_iff_of_iso ?_).1 h
  refine ShortComplex.isoMk ((freeOn R).mapIso (e2 f)) ((freeOn R).mapIso (e1 f)) ((freeOn R).mapIso (e0 f)) ?_ ?_
  · have hd : ((AlgebraicTopology.alternatingFaceMapComplex (Shv R)).obj
        ((Arrow.mk f).cechNerve ⋙ freeOn R)).d 2 1 =
        (freeOn R).map ((Arrow.mk f).cechNerve.δ (0 : Fin 3)) - (freeOn R).map ((Arrow.mk f).cechNerve.δ (1 : Fin 3))
          + (freeOn R).map ((Arrow.mk f).cechNerve.δ (2 : Fin 3)) := by
      erw [AlgebraicTopology.AlternatingFaceMapComplex.obj_d_eq]
      simp [Fin.sum_univ_three, SimplicialObject.δ, sub_eq_add_neg]
    change _ = ((AlgebraicTopology.alternatingFaceMapComplex (Shv R)).obj
        ((Arrow.mk f).cechNerve ⋙ freeOn R)).d 2 1 ≫ _
    rw [hd]
    simp only [d2, Functor.mapIso_hom, Preadditive.comp_add, Preadditive.comp_sub, Preadditive.add_comp,
      Preadditive.sub_comp, ← Functor.map_comp, cech_nerve_face_two_zero, cech_nerve_face_two_one, cech_nerve_face_two_two]
    simp only [Functor.map_comp]
    erw [Preadditive.comp_add, Preadditive.comp_sub]
    rfl
  · have hd : ((AlgebraicTopology.alternatingFaceMapComplex (Shv R)).obj
        ((Arrow.mk f).cechNerve ⋙ freeOn R)).d 1 0 =
        (freeOn R).map ((Arrow.mk f).cechNerve.δ (0 : Fin 2)) - (freeOn R).map ((Arrow.mk f).cechNerve.δ (1 : Fin 2)) := by
      erw [AlgebraicTopology.AlternatingFaceMapComplex.obj_d_eq]
      simp [Fin.sum_univ_two, SimplicialObject.δ, sub_eq_add_neg]
    change _ = ((AlgebraicTopology.alternatingFaceMapComplex (Shv R)).obj
        ((Arrow.mk f).cechNerve ⋙ freeOn R)).d 1 0 ≫ _
    rw [hd]
    simp only [d1, Functor.mapIso_hom, Preadditive.comp_sub,
      Preadditive.sub_comp, ← Functor.map_comp, cech_nerve_face_one_zero, cech_nerve_face_one_one]
    simp only [Functor.map_comp]
    erw [Preadditive.comp_sub]
    rfl
end GlobalTheory.Et.CovChar.Trip

example : ∀ (R : Type) [CommRing R] {X Y : Scheme.{0}} (f : Y ⟶ X), (ShortComplex.mk (d2 f R) (d1 f R) (d2_comp f R)).Exact :=
  fun R _ _ _ f => GlobalTheory.Et.CovChar.Trip.free_sheaf_cech_degree_two_exact R f
