import Mathlib
import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProjectiveSpaceChart
import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProjectiveCohomology.TwistingSheaf
set_option maxSynthPendingDepth 1

namespace GroundTheory.Arith.SchemeCoh

open AlgebraicGeometry CategoryTheory Limits MvPolynomial HomogeneousLocalization

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

noncomputable section

namespace ProjSpace

lemma irrelevant_le_span_X (A : Type u) [CommRing A] (n : ℕ) :
    (HomogeneousIdeal.irrelevant (grading A n)).toIdeal ≤
      Ideal.span (Set.range (X : Fin (n + 1) → MvPolynomial (Fin (n + 1)) A)) := by
  intro p hp
  rw [← Set.image_univ, MvPolynomial.mem_ideal_span_X_image]
  intro m hm
  by_contra! h
  have hm0 : m = 0 := Finsupp.ext fun i => h i (Set.mem_univ i)
  subst hm0
  have h0 : GradedRing.proj (grading A n) 0 p = 0 := hp
  rw [GradedRing.proj_apply] at h0
  change ((MvPolynomial.decomposition.decompose' p 0 : homogeneousSubmodule (Fin (n + 1)) A 0) :
    MvPolynomial (Fin (n + 1)) A) = 0 at h0
  rw [MvPolynomial.decomposition.decompose'_apply, homogeneousComponent_zero, C_eq_zero] at h0
  exact (MvPolynomial.mem_support_iff.mp hm) h0

variable (A B : Type u) [CommRing A] [CommRing B] [Algebra A B] (n : ℕ)

def gradedMap : grading A n →+*ᵍ grading B n where
  toRingHom := MvPolynomial.map (algebraMap A B)
  map_mem {_ _} hx :=
    (mem_homogeneousSubmodule _ _).2 (((mem_homogeneousSubmodule _ _).1 hx).map _)

lemma gradedMap_apply (p : MvPolynomial (Fin (n + 1)) A) :
    gradedMap A B n p = MvPolynomial.map (algebraMap A B) p := rfl

@[simp] lemma gradedMap_X (j : Fin (n + 1)) : gradedMap A B n (X j) = X j := by
  simp [gradedMap_apply]

lemma irrelevant_le_map :
    HomogeneousIdeal.irrelevant (grading B n) ≤
      (HomogeneousIdeal.irrelevant (grading A n)).map (gradedMap A B n) := by
  rw [← toIdeal_le_toIdeal_iff, HomogeneousIdeal.toIdeal_map]
  refine (irrelevant_le_span_X B n).trans (Ideal.span_le.2 ?_)
  rintro _ ⟨j, rfl⟩
  rw [← gradedMap_X A B n j]
  exact Ideal.mem_map_of_mem _ (HomogeneousIdeal.mem_irrelevant_of_mem _ Nat.one_pos (X_mem j))

def baseChangeMap : projectiveSpace B n ⟶ projectiveSpace A n :=
  Proj.map (gradedMap A B n) (irrelevant_le_map A B n)

def stdAffineCover (A : Type u) [CommRing A] (n : ℕ) : (projectiveSpace A n).AffineOpenCover :=
  Proj.affineOpenCoverOfIrrelevantLESpan (grading A n)
    (fun j : Fin (n + 1) => (X j : MvPolynomial (Fin (n + 1)) A)) (fun j => X_mem j)
    (fun _ => Nat.one_pos) (irrelevant_le_span_X A n)

def chartAlgebraMap (A : Type u) [CommRing A] {n : ℕ} (s : MvPolynomial (Fin (n + 1)) A) :
    A →+* Away (grading A n) s :=
  (fromZeroRingHom (grading A n) _).comp (algebraMap A (grading A n 0))

def awayCongr {s t : MvPolynomial (Fin (n + 1)) B} (h : s = t) :
    Away (grading B n) s ≃+* Away (grading B n) t := by
  subst h
  exact RingEquiv.refl _

lemma awayCongr_mk {s t : MvPolynomial (Fin (n + 1)) B} (h : s = t) {d : ℕ}
    (hs : s ∈ grading B n d) (ht : t ∈ grading B n d) (m : ℕ) (x : MvPolynomial (Fin (n + 1)) B)
    (hx : x ∈ grading B n (m • d)) :
    awayCongr B n h (Away.mk (grading B n) hs m x hx) = Away.mk (grading B n) ht m x hx := by
  subst h
  rfl

lemma awayCongr_chartAlgebraMap {s t : MvPolynomial (Fin (n + 1)) B} (h : s = t) (b : B) :
    awayCongr B n h (chartAlgebraMap B s b) = chartAlgebraMap B t b := by
  subst h
  rfl

variable {A B n}

lemma map_chartAlgebraMap (j : Fin (n + 1)) (a : A) :
    Away.map (gradedMap A B n) (X j) (chartAlgebraMap A (X j) a) =
      chartAlgebraMap B (gradedMap A B n (X j)) (algebraMap A B a) := by
  apply HomogeneousLocalization.val_injective
  change Localization.mk _ _ = Localization.mk _ _
  congr 1
  · simp [gradedMap_apply, MvPolynomial.algebraMap_eq]
  · ext
    simp [gradedMap_apply]

lemma awayCongr_symm {s t : MvPolynomial (Fin (n + 1)) B} (h : s = t) :
    (awayCongr B n h).symm = awayCongr B n h.symm := by
  subst h
  rfl

lemma chartEquiv_symm_apply (j : Fin (n + 1)) (p : MvPolynomial {i // i ≠ j} A) :
    (chartEquiv A j).symm p = polyToChart A j p := rfl

lemma polyToChart_C (j : Fin (n + 1)) (a : A) :
    polyToChart A j (C a) = chartAlgebraMap A (X j) a := by
  simp [polyToChart, chartAlgebraMap]

lemma map_polyToChart (j : Fin (n + 1)) :
    (Away.map (gradedMap A B n) (X j)).comp (polyToChart A j) =
      ((awayCongr B n (gradedMap_X A B n j)).symm.toRingHom.comp (polyToChart B j)).comp
        (MvPolynomial.map (algebraMap A B)) := by
  apply MvPolynomial.ringHom_ext
  · intro a
    simp only [RingHom.comp_apply, map_C, polyToChart_C, map_chartAlgebraMap,
      RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, awayCongr_symm, awayCongr_chartAlgebraMap]
  · intro k
    simp only [RingHom.comp_apply, map_X, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
      awayCongr_symm, polyToChart, coe_eval₂Hom, eval₂_X, coordinate, Away.map_mk]
    rw [awayCongr_mk B n _ (X_mem j) (by rw [gradedMap_X]; exact X_mem j)]
    apply HomogeneousLocalization.val_injective
    simp [Away.val_mk]

lemma map_polyToChart_apply (j : Fin (n + 1)) (p : MvPolynomial {i // i ≠ j} A) :
    Away.map (gradedMap A B n) (X j) (polyToChart A j p) =
      (awayCongr B n (gradedMap_X A B n j)).symm (polyToChart B j (MvPolynomial.map (algebraMap A B) p)) :=
  congrArg (fun φ => φ p) (map_polyToChart (A := A) (B := B) j)

attribute [local instance] MvPolynomial.algebraMvPolynomial in

theorem isPushout_chart (j : Fin (n + 1)) :
    IsPushout (CommRingCat.ofHom (algebraMap A B)) (CommRingCat.ofHom (chartAlgebraMap A (X j)))
      (CommRingCat.ofHom (chartAlgebraMap B (gradedMap A B n (X j))))
      (CommRingCat.ofHom (Away.map (gradedMap A B n) (X j))) := by
  have h0 := CommRingCat.isPushout_of_isPushout A B (MvPolynomial {i // i ≠ j} A)
    (MvPolynomial {i // i ≠ j} B)
  refine h0.of_iso (Iso.refl _) (Iso.refl _) (chartEquiv A j).symm.toCommRingCatIso
    ((chartEquiv B j).symm.trans (awayCongr B n (gradedMap_X A B n j)).symm).toCommRingCatIso
    ?_ ?_ ?_ ?_
  · ext x
    rfl
  · ext x
    simp [chartEquiv_symm_apply, polyToChart_C]
  · ext x
    simp [chartEquiv_symm_apply, polyToChart_C, awayCongr_symm, awayCongr_chartAlgebraMap]
  · apply CommRingCat.hom_ext
    apply MvPolynomial.ringHom_ext <;> intro x <;>
      simp [chartEquiv_symm_apply, map_polyToChart_apply]

variable (A) in

lemma awayι_toSpecBase {s : MvPolynomial (Fin (n + 1)) A} {d : ℕ} (hs : s ∈ grading A n d)
    (hd : 0 < d) :
    Proj.awayι (grading A n) s hs hd ≫ toSpecBase A n =
      Spec.map (CommRingCat.ofHom (chartAlgebraMap A s)) := by
  rw [toSpecBase, ← Category.assoc, Proj.awayι_toSpecZero, ← Spec.map_comp]
  rfl

variable (A B n) in

theorem isPullback_baseChange :
    IsPullback (baseChangeMap A B n) (toSpecBase B n) (toSpecBase A n)
      (Spec.map (CommRingCat.ofHom (algebraMap A B))) := by
  refine Scheme.isPullback_of_openCover _ _ _ _ (stdAffineCover A n).openCover fun j => ?_
  have hQ : IsPullback (Spec.map (CommRingCat.ofHom (Away.map (gradedMap A B n) (X j))))
      (Proj.awayι (grading B n) (gradedMap A B n (X j)) ((gradedMap A B n).2 (X_mem j)) Nat.one_pos)
      (Proj.awayι (grading A n) (X j : MvPolynomial (Fin (n + 1)) A) (X_mem j) Nat.one_pos)
      (baseChangeMap A B n) :=
    IsOpenImmersion.isPullback _ _ _ _ (Proj.awayι_comp_map _ _ _ _ _)
      (by rw [Proj.opensRange_awayι, Proj.opensRange_awayι]; rfl)
  have hS := isPullback_SpecMap_of_isPushout _ _ _ _ (isPushout_chart (A := A) (B := B) (n := n) j)
  refine hS.flip.of_iso hQ.flip.isoPullback (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_
  · simp only [Iso.refl_hom]
    exact (hQ.flip.isoPullback_hom_snd).symm
  · simp only [Iso.refl_hom, Category.comp_id]
    change _ = hQ.flip.isoPullback.hom ≫ pullback.fst _ _ ≫ toSpecBase B n
    rw [hQ.flip.isoPullback_hom_fst_assoc, awayι_toSpecBase]
  · simp only [Iso.refl_hom, Category.comp_id]
    exact (awayι_toSpecBase A (X_mem j) Nat.one_pos).symm
  · simp

end ProjSpace

end

end GroundTheory.Arith.SchemeCoh
