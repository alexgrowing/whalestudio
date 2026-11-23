import Mathlib
import Development.ResolutionOfSingularities.Foundations.Blowup.BlowupBasic
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.BlowupSequenceRelations
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.AffineSpaceCoordinates
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.AffineResolutionRule
import Development.ResolutionOfSingularities.Foundations.BlowupUniversalProperty
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionOfSingularities
universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

def homOfSumCoords {n₁ n₂ n : Type u} (e : n₁ ⊕ n₂ ≃ n) (S : Scheme.{u}) {X : Scheme.{u}}
    (f : X ⟶ AffineSpace n₁ S) (g : X ⟶ AffineSpace n₂ S) :
    X ⟶ AffineSpace n S :=
  AffineSpace.homOfVector (f ≫ AffineSpace n₁ S ↘ S)
    (fun i =>
      Sum.elim (fun a => f.appTop (AffineSpace.coord S a))
        (fun b => g.appTop (AffineSpace.coord S b)) (e.symm i))

@[simp]
theorem homOfSumCoords_appTop_coord_inl {n₁ n₂ n : Type u} (e : n₁ ⊕ n₂ ≃ n) (S : Scheme.{u})
    {X : Scheme.{u}} (f : X ⟶ AffineSpace n₁ S) (g : X ⟶ AffineSpace n₂ S) (a : n₁) :
    (homOfSumCoords e S f g).appTop (AffineSpace.coord S (e (Sum.inl a))) =
      f.appTop (AffineSpace.coord S a) := by
  simp [homOfSumCoords]

@[simp]
theorem homOfSumCoords_appTop_coord_inr {n₁ n₂ n : Type u} (e : n₁ ⊕ n₂ ≃ n) (S : Scheme.{u})
    {X : Scheme.{u}} (f : X ⟶ AffineSpace n₁ S) (g : X ⟶ AffineSpace n₂ S) (b : n₂) :
    (homOfSumCoords e S f g).appTop (AffineSpace.coord S (e (Sum.inr b))) =
      g.appTop (AffineSpace.coord S b) := by
  simp [homOfSumCoords]

private theorem homOfSumCoords_comp_reindex_inl {n₁ n₂ n : Type u} (e : n₁ ⊕ n₂ ≃ n) (S : Scheme.{u})
    {X : Scheme.{u}} (f : X ⟶ AffineSpace n₁ S) (g : X ⟶ AffineSpace n₂ S) :
    homOfSumCoords e S f g ≫ AffineSpace.reindex (S := S) (fun a : n₁ => e (Sum.inl a)) = f := by
  refine AffineSpace.hom_ext ?_ (fun a => ?_)
  · simp [homOfSumCoords]
  · rw [AlgebraicGeometry.Scheme.Hom.comp_appTop, CommRingCat.comp_apply]
    simp

private theorem homOfSumCoords_comp_reindex_inr {n₁ n₂ n : Type u} (e : n₁ ⊕ n₂ ≃ n) (S : Scheme.{u})
    {X : Scheme.{u}} (f : X ⟶ AffineSpace n₁ S) (g : X ⟶ AffineSpace n₂ S)
    (hfg : f ≫ (AffineSpace n₁ S ↘ S) = g ≫ (AffineSpace n₂ S ↘ S)) :
    homOfSumCoords e S f g ≫ AffineSpace.reindex (S := S) (fun b : n₂ => e (Sum.inr b)) = g := by
  refine AffineSpace.hom_ext ?_ (fun b => ?_)
  · simpa [homOfSumCoords] using hfg
  · rw [AlgebraicGeometry.Scheme.Hom.comp_appTop, CommRingCat.comp_apply]
    simp

private theorem eq_homOfSumCoords_of_comp_reindex {n₁ n₂ n : Type u} (e : n₁ ⊕ n₂ ≃ n) (S : Scheme.{u})
    {X : Scheme.{u}} (f : X ⟶ AffineSpace n₁ S) (g : X ⟶ AffineSpace n₂ S)
    (m : X ⟶ AffineSpace n S)
    (h₁ : m ≫ AffineSpace.reindex (S := S) (fun a : n₁ => e (Sum.inl a)) = f)
    (h₂ : m ≫ AffineSpace.reindex (S := S) (fun b : n₂ => e (Sum.inr b)) = g) :
    m = homOfSumCoords e S f g := by
  refine AffineSpace.hom_ext ?_ (fun i => ?_)
  · have h : (m ≫ AffineSpace.reindex (S := S) (fun a : n₁ => e (Sum.inl a))) ≫
        (AffineSpace n₁ S ↘ S) = f ≫ (AffineSpace n₁ S ↘ S) := by rw [h₁]
    simpa [homOfSumCoords] using h
  · obtain ⟨j, rfl⟩ : ∃ j, e j = i := ⟨e.symm i, e.apply_symm_apply i⟩
    obtain (a | b) := j
    · have h : (m ≫ AffineSpace.reindex (S := S) (fun a : n₁ => e (Sum.inl a))).appTop
          (AffineSpace.coord S a) = f.appTop (AffineSpace.coord S a) := by rw [h₁]
      rw [AlgebraicGeometry.Scheme.Hom.comp_appTop, CommRingCat.comp_apply] at h
      simpa using h
    · have h : (m ≫ AffineSpace.reindex (S := S) (fun b : n₂ => e (Sum.inr b))).appTop
          (AffineSpace.coord S b) = g.appTop (AffineSpace.coord S b) := by rw [h₂]
      rw [AlgebraicGeometry.Scheme.Hom.comp_appTop, CommRingCat.comp_apply] at h
      simpa using h

theorem isPullback_reindex_of_sumEquiv {n₁ n₂ n : Type u} (e : n₁ ⊕ n₂ ≃ n) (S : Scheme.{u}) :
    IsPullback
      (AffineSpace.reindex (S := S) (fun a : n₁ => e (Sum.inl a)))
      (AffineSpace.reindex (S := S) (fun b : n₂ => e (Sum.inr b)))
      (AffineSpace n₁ S ↘ S) (AffineSpace n₂ S ↘ S) := by
  have hcomm : CommSq
      (AffineSpace.reindex (S := S) (fun a : n₁ => e (Sum.inl a)))
      (AffineSpace.reindex (S := S) (fun b : n₂ => e (Sum.inr b)))
      (AffineSpace n₁ S ↘ S) (AffineSpace n₂ S ↘ S) := ⟨by simp⟩
  have hcond : Limits.pullback.fst (AffineSpace n₁ S ↘ S) (AffineSpace n₂ S ↘ S) ≫
      (AffineSpace n₁ S ↘ S) =
      Limits.pullback.snd (AffineSpace n₁ S ↘ S) (AffineSpace n₂ S ↘ S) ≫
      (AffineSpace n₂ S ↘ S) := Limits.pullback.condition
  have hA : homOfSumCoords e S
      (Limits.pullback.fst (AffineSpace n₁ S ↘ S) (AffineSpace n₂ S ↘ S))
      (Limits.pullback.snd (AffineSpace n₁ S ↘ S) (AffineSpace n₂ S ↘ S)) ≫
      AffineSpace.reindex (S := S) (fun a : n₁ => e (Sum.inl a)) =
      Limits.pullback.fst (AffineSpace n₁ S ↘ S) (AffineSpace n₂ S ↘ S) :=
    homOfSumCoords_comp_reindex_inl e S _ _
  have hB : homOfSumCoords e S
      (Limits.pullback.fst (AffineSpace n₁ S ↘ S) (AffineSpace n₂ S ↘ S))
      (Limits.pullback.snd (AffineSpace n₁ S ↘ S) (AffineSpace n₂ S ↘ S)) ≫
      AffineSpace.reindex (S := S) (fun b : n₂ => e (Sum.inr b)) =
      Limits.pullback.snd (AffineSpace n₁ S ↘ S) (AffineSpace n₂ S ↘ S) :=
    homOfSumCoords_comp_reindex_inr e S _ _ hcond
  have hid : (𝟙 (AffineSpace n S)) = homOfSumCoords e S
      (AffineSpace.reindex (S := S) (fun a : n₁ => e (Sum.inl a)))
      (AffineSpace.reindex (S := S) (fun b : n₂ => e (Sum.inr b))) :=
    eq_homOfSumCoords_of_comp_reindex e S _ _ _ (Category.id_comp _) (Category.id_comp _)
  refine IsPullback.of_iso_pullback hcomm
    { hom := Limits.pullback.lift _ _ hcomm.w
      inv := homOfSumCoords e S
        (Limits.pullback.fst (AffineSpace n₁ S ↘ S) (AffineSpace n₂ S ↘ S))
        (Limits.pullback.snd (AffineSpace n₁ S ↘ S) (AffineSpace n₂ S ↘ S))
      hom_inv_id := ?_
      inv_hom_id := ?_ }
    (Limits.pullback.lift_fst _ _ _) (Limits.pullback.lift_snd _ _ _)
  · rw [hid]
    refine eq_homOfSumCoords_of_comp_reindex e S _ _ _ ?_ ?_
    · rw [Category.assoc, hA]
      exact Limits.pullback.lift_fst _ _ _
    · rw [Category.assoc, hB]
      exact Limits.pullback.lift_snd _ _ _
  · refine Limits.pullback.hom_ext ?_ ?_
    · rw [Category.assoc, Limits.pullback.lift_fst, Category.id_comp]
      exact hA
    · rw [Category.assoc, Limits.pullback.lift_snd, Category.id_comp]
      exact hB

def sumUliftEquivUliftSum (n m : ℕ) :
    (ULift.{u} (Fin n) ⊕ ULift.{u} (Fin m)) ≃ ULift.{u} (Fin n ⊕ Fin m) where
  toFun := Sum.elim (fun a => ULift.up (Sum.inl a.down)) (fun b => ULift.up (Sum.inr b.down))
  invFun := fun i =>
    Sum.elim (fun a => Sum.inl (ULift.up a)) (fun b => Sum.inr (ULift.up b)) i.down
  left_inv := by rintro (⟨a⟩ | ⟨b⟩) <;> rfl
  right_inv := by rintro ⟨a | b⟩ <;> rfl

@[simp]
theorem sumUliftEquivUliftSum_inl (n m : ℕ) (a : Fin n) :
    sumUliftEquivUliftSum.{u} n m (Sum.inl (ULift.up a)) = ULift.up (Sum.inl a) := rfl

@[simp]
theorem sumUliftEquivUliftSum_inr (n m : ℕ) (b : Fin m) :
    sumUliftEquivUliftSum.{u} n m (Sum.inr (ULift.up b)) = ULift.up (Sum.inr b) := rfl

@[simp]
theorem sumUliftEquivUliftSum_symm_inl (n m : ℕ) (a : Fin n) :
    (sumUliftEquivUliftSum.{u} n m).symm (ULift.up (Sum.inl a)) = Sum.inl (ULift.up a) := rfl

@[simp]
theorem sumUliftEquivUliftSum_symm_inr (n m : ℕ) (b : Fin m) :
    (sumUliftEquivUliftSum.{u} n m).symm (ULift.up (Sum.inr b)) = Sum.inr (ULift.up b) := rfl

def projRight (k : Type u) [Field k] (n m : ℕ) :
    affineSpaceIndexedBy k (ULift.{u} (Fin n ⊕ Fin m)) ⟶ affineSpaceIndexedBy k (ULift.{u} (Fin m)) :=
  AffineSpace.reindex (S := Spec (CommRingCat.of k))
    (fun j : ULift.{u} (Fin m) => (ULift.up (Sum.inr j.down) : ULift.{u} (Fin n ⊕ Fin m)))

def projLeft (k : Type u) [Field k] (n m : ℕ) :
    affineSpaceIndexedBy k (ULift.{u} (Fin n ⊕ Fin m)) ⟶ affineSpaceIndexedBy k (ULift.{u} (Fin n)) :=
  AffineSpace.reindex (S := Spec (CommRingCat.of k))
    (fun j : ULift.{u} (Fin n) => (ULift.up (Sum.inl j.down) : ULift.{u} (Fin n ⊕ Fin m)))

@[simp]
theorem projRight_comp_affineSpaceIndexedByToSpec (k : Type u) [Field k] (n m : ℕ) :
    projRight k n m ≫ affineSpaceIndexedByToSpec k (ULift.{u} (Fin m)) =
      affineSpaceIndexedByToSpec k (ULift.{u} (Fin n ⊕ Fin m)) := by
  simp [projRight]

@[simp]
theorem projRight_appTop_coord (k : Type u) [Field k] (n m : ℕ) (j : Fin m) :
    (projRight k n m).appTop
        (AffineSpace.coord (Spec (CommRingCat.of k)) (ULift.up j)) =
      AffineSpace.coord (Spec (CommRingCat.of k))
        (ULift.up (Sum.inr j) : ULift.{u} (Fin n ⊕ Fin m)) := by
  simp [projRight]

@[simp]
theorem projLeft_comp_affineSpaceIndexedByToSpec (k : Type u) [Field k] (n m : ℕ) :
    projLeft k n m ≫ affineSpaceIndexedByToSpec k (ULift.{u} (Fin n)) =
      affineSpaceIndexedByToSpec k (ULift.{u} (Fin n ⊕ Fin m)) := by
  simp [projLeft]

@[simp]
theorem projLeft_appTop_coord (k : Type u) [Field k] (n m : ℕ) (j : Fin n) :
    (projLeft k n m).appTop
        (AffineSpace.coord (Spec (CommRingCat.of k)) (ULift.up j)) =
      AffineSpace.coord (Spec (CommRingCat.of k))
        (ULift.up (Sum.inl j) : ULift.{u} (Fin n ⊕ Fin m)) := by
  simp [projLeft]

theorem isPullback_projLeft_projRight (k : Type u) [Field k] (n m : ℕ) :
    IsPullback (projLeft k n m) (projRight k n m)
      (affineSpaceIndexedByToSpec k (ULift.{u} (Fin n)))
      (affineSpaceIndexedByToSpec k (ULift.{u} (Fin m))) :=
  isPullback_reindex_of_sumEquiv (sumUliftEquivUliftSum.{u} n m) (Spec (CommRingCat.of k))

theorem smooth_projRight (hs : AffineSpaceIsSmooth.{u}) (k : Type u) [Field k] (n m : ℕ) :
    AlgebraicGeometry.Smooth (projRight k n m) :=
  MorphismProperty.of_isPullback (P := @AlgebraicGeometry.Smooth)
    (isPullback_projLeft_projRight k n m) (hs k n)

theorem smooth_projLeft (hs : AffineSpaceIsSmooth.{u}) (k : Type u) [Field k] (n m : ℕ) :
    AlgebraicGeometry.Smooth (projLeft k n m) := by
  have hsm : AlgebraicGeometry.Smooth (affineSpaceIndexedByToSpec k (ULift.{u} (Fin m))) := hs k m
  have hpb : IsPullback (projLeft k n m) (projRight k n m)
      (affineSpaceIndexedByToSpec k (ULift.{u} (Fin n)))
      (affineSpaceIndexedByToSpec k (ULift.{u} (Fin m))) :=
    isPullback_reindex_of_sumEquiv (sumUliftEquivUliftSum.{u} n m) (Spec (CommRingCat.of k))
  exact MorphismProperty.IsStableUnderBaseChange.of_isPullback hpb.flip hsm

def prodMapOnPreimage (k : Type u) [Field k] (n m c : ℕ)
    (U : (affineSpaceIndexedBy k (ULift.{u} (Fin n))).Opens)
    (φ : U.toScheme ⟶ affineSpaceIndexedBy k (ULift.{u} (Fin c))) :
    (projLeft k n m ⁻¹ᵁ U).toScheme ⟶ affineSpaceIndexedBy k (ULift.{u} (Fin c ⊕ Fin m)) :=
  AffineSpace.homOfVector
    ((projLeft k n m ⁻¹ᵁ U).ι ≫ affineSpaceIndexedByToSpec k (ULift.{u} (Fin n ⊕ Fin m)))
    (fun i =>
      Sum.elim
        (fun a : Fin c =>
          (AlgebraicGeometry.morphismRestrict (projLeft k n m) U ≫ φ).appTop
            (AffineSpace.coord (Spec (CommRingCat.of k)) (ULift.up a)))
        (fun b : Fin m =>
          ((projLeft k n m ⁻¹ᵁ U).ι).appTop
            (AffineSpace.coord (Spec (CommRingCat.of k))
              (ULift.up (Sum.inr b) : ULift.{u} (Fin n ⊕ Fin m))))
        i.down)

theorem prodMapOnPreimage_comp_affineSpaceIndexedByToSpec (k : Type u) [Field k] (n m c : ℕ)
    (U : (affineSpaceIndexedBy k (ULift.{u} (Fin n))).Opens)
    (φ : U.toScheme ⟶ affineSpaceIndexedBy k (ULift.{u} (Fin c))) :
    prodMapOnPreimage k n m c U φ ≫ affineSpaceIndexedByToSpec k (ULift.{u} (Fin c ⊕ Fin m)) =
      (projLeft k n m ⁻¹ᵁ U).ι ≫ affineSpaceIndexedByToSpec k (ULift.{u} (Fin n ⊕ Fin m)) := by
  simp [prodMapOnPreimage]

theorem prodMapOnPreimage_comp_projRight (k : Type u) [Field k] (n m c : ℕ)
    (U : (affineSpaceIndexedBy k (ULift.{u} (Fin n))).Opens)
    (φ : U.toScheme ⟶ affineSpaceIndexedBy k (ULift.{u} (Fin c))) :
    prodMapOnPreimage k n m c U φ ≫ projRight k c m =
      (projLeft k n m ⁻¹ᵁ U).ι ≫ projRight k n m := by
  refine AffineSpace.hom_ext ?_ ?_
  · rw [Category.assoc, projRight_comp_affineSpaceIndexedByToSpec, Category.assoc, projRight_comp_affineSpaceIndexedByToSpec, prodMapOnPreimage_comp_affineSpaceIndexedByToSpec]
  · rintro ⟨j⟩
    simp only [AlgebraicGeometry.Scheme.Hom.comp_appTop, CommRingCat.comp_apply]
    rw [projRight_appTop_coord, projRight_appTop_coord]
    simp [prodMapOnPreimage]

theorem morphismRestrict_projLeft_comp (k : Type u) [Field k] (n m c : ℕ)
    (U : (affineSpaceIndexedBy k (ULift.{u} (Fin n))).Opens)
    (φ : U.toScheme ⟶ affineSpaceIndexedBy k (ULift.{u} (Fin c)))
    (hφ : φ ≫ affineSpaceIndexedByToSpec k (ULift.{u} (Fin c)) =
      U.ι ≫ affineSpaceIndexedByToSpec k (ULift.{u} (Fin n))) :
    AlgebraicGeometry.morphismRestrict (projLeft k n m) U ≫ φ =
      prodMapOnPreimage k n m c U φ ≫ projLeft k c m := by
  refine AffineSpace.hom_ext ?_ ?_
  · have h1 : (AlgebraicGeometry.morphismRestrict (projLeft k n m) U ≫ φ) ≫
        affineSpaceIndexedByToSpec k (ULift.{u} (Fin c)) =
        (projLeft k n m ⁻¹ᵁ U).ι ≫ affineSpaceIndexedByToSpec k (ULift.{u} (Fin n ⊕ Fin m)) := by
      rw [Category.assoc, hφ, morphismRestrict_ι_assoc, projLeft_comp_affineSpaceIndexedByToSpec]
    have h2 : (prodMapOnPreimage k n m c U φ ≫ projLeft k c m) ≫
        affineSpaceIndexedByToSpec k (ULift.{u} (Fin c)) =
        (projLeft k n m ⁻¹ᵁ U).ι ≫ affineSpaceIndexedByToSpec k (ULift.{u} (Fin n ⊕ Fin m)) := by
      rw [Category.assoc, projLeft_comp_affineSpaceIndexedByToSpec, prodMapOnPreimage_comp_affineSpaceIndexedByToSpec]
    exact h1.trans h2.symm
  · rintro ⟨j⟩
    have h : (prodMapOnPreimage k n m c U φ ≫ projLeft k c m).appTop
        (AffineSpace.coord (Spec (CommRingCat.of k)) (ULift.up j)) =
        (AlgebraicGeometry.morphismRestrict (projLeft k n m) U ≫ φ).appTop
        (AffineSpace.coord (Spec (CommRingCat.of k)) (ULift.up j)) := by
      rw [AlgebraicGeometry.Scheme.Hom.comp_appTop, CommRingCat.comp_apply, projLeft_appTop_coord]
      simp [prodMapOnPreimage]
    exact h.symm

theorem isPullback_prodMapOnPreimage (k : Type u) [Field k] (n m c : ℕ)
    (U : (affineSpaceIndexedBy k (ULift.{u} (Fin n))).Opens)
    (φ : U.toScheme ⟶ affineSpaceIndexedBy k (ULift.{u} (Fin c)))
    (hφ : φ ≫ affineSpaceIndexedByToSpec k (ULift.{u} (Fin c)) =
      U.ι ≫ affineSpaceIndexedByToSpec k (ULift.{u} (Fin n))) :
    IsPullback (prodMapOnPreimage k n m c U φ)
      (AlgebraicGeometry.morphismRestrict (projLeft k n m) U)
      (projLeft k c m) φ := by
  have hsq1 : IsPullback (AlgebraicGeometry.morphismRestrict (projLeft k n m) U)
      (projLeft k n m ⁻¹ᵁ U).ι U.ι (projLeft k n m) :=
    AlgebraicGeometry.isPullback_morphismRestrict (projLeft k n m) U
  have hstar := hsq1.paste_vert (isPullback_projLeft_projRight k n m)
  have hstar' : IsPullback (AlgebraicGeometry.morphismRestrict (projLeft k n m) U)
      (prodMapOnPreimage k n m c U φ ≫ projRight k c m)
      (φ ≫ affineSpaceIndexedByToSpec k (ULift.{u} (Fin c)))
      (affineSpaceIndexedByToSpec k (ULift.{u} (Fin m))) := by
    rw [prodMapOnPreimage_comp_projRight, hφ]
    exact hstar
  exact (hstar'.of_bot (morphismRestrict_projLeft_comp k n m c U φ hφ)
    (isPullback_projLeft_projRight k c m)).flip

theorem smooth_prodMapOnPreimage (_hs : AffineSpaceIsSmooth.{u}) (k : Type u) [Field k] (n m c : ℕ)
    (U : (affineSpaceIndexedBy k (ULift.{u} (Fin n))).Opens)
    (φ : U.toScheme ⟶ affineSpaceIndexedBy k (ULift.{u} (Fin c)))
    [AlgebraicGeometry.Smooth φ]
    (hφ : φ ≫ affineSpaceIndexedByToSpec k (ULift.{u} (Fin c)) =
      U.ι ≫ affineSpaceIndexedByToSpec k (ULift.{u} (Fin n))) :
    AlgebraicGeometry.Smooth (prodMapOnPreimage k n m c U φ) := by
  have hsmooth : AlgebraicGeometry.Smooth φ := ‹AlgebraicGeometry.Smooth φ›
  exact MorphismProperty.of_isPullback (P := @AlgebraicGeometry.Smooth)
    (isPullback_prodMapOnPreimage k n m c U φ hφ).flip hsmooth

end FunctorialResolution.EmbeddedResolution

end
