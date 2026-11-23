import Mathlib
import Development.ResolutionOfSingularities.Foundations.Blowup.BlowupBasic
import Development.ResolutionOfSingularities.Foundations.Blowup.BlowupProperties
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.ClopenRestriction
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.AffineSpaceCoordinates
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.SmoothCoordinateCodimension
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.StrictNormalCrossings
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.AffineResolutionRule
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.AffineSpaceProduct
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.AffineSpaceLinearEmbeddings
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.PullbackBlowupSequenceComposition
import Development.ResolutionOfSingularities.EmbeddedResolution.AlgebraicPreliminaries.KernelFlatBaseChange
import Development.ResolutionOfSingularities.EmbeddedResolution.StrongResolution.SequenceIsomorphism
import Development.ResolutionOfSingularities.Foundations.BlowupUniversalProperty
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionOfSingularities
universe u

open CategoryTheory AlgebraicGeometry

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

def affineSpaceOrigin (k : Type u) [Field k] (m : ℕ) :
    Spec (CommRingCat.of k) ⟶ affineSpaceIndexedBy k (ULift.{u, 0} (Fin m)) :=
  AffineSpace.homOfVector (𝟙 (Spec (CommRingCat.of k))) (fun _ => 0)

@[simp]
theorem affineSpaceOrigin_comp_toSpec (k : Type u) [Field k] (m : ℕ) :
    affineSpaceOrigin k m ≫ affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin m)) =
      𝟙 (Spec (CommRingCat.of k)) := by
  unfold affineSpaceOrigin
  simp

@[simp]
theorem affineSpaceOrigin_comp_toSpec_assoc (k : Type u) [Field k] (m : ℕ) {Z : Scheme.{u}}
    (g : Spec (CommRingCat.of k) ⟶ Z) :
    affineSpaceOrigin k m ≫ affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin m)) ≫ g = g := by
  rw [← Category.assoc, affineSpaceOrigin_comp_toSpec, Category.id_comp]

theorem pullbackCoord_affineSpaceOrigin (k : Type u) [Field k] (m : ℕ)
    (i : ULift.{u, 0} (Fin m)) :
    pullbackCoord (affineSpaceOrigin k m) i = 0 := by
  simp [pullbackCoord_def, affineSpaceOrigin]

@[simp]
theorem affineSpaceOrigin_appTop_coord (k : Type u) [Field k] (m : ℕ)
    (i : ULift.{u, 0} (Fin m)) :
    (ConcreteCategory.hom (Scheme.Hom.appTop (affineSpaceOrigin k m)))
        (AffineSpace.coord (Spec (CommRingCat.of k)) i) = 0 := by
  simp [affineSpaceOrigin]

theorem eq_affineSpaceOrigin_of_pullbackCoord_eq_zero (k : Type u) [Field k] (m : ℕ)
    (f : Spec (CommRingCat.of k) ⟶ affineSpaceIndexedBy k (ULift.{u, 0} (Fin m)))
    (hf : f ≫ affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin m)) = 𝟙 (Spec (CommRingCat.of k)))
    (hcoord : ∀ i : ULift.{u, 0} (Fin m), pullbackCoord f i = 0) :
    f = affineSpaceOrigin k m := by
  refine AffineSpace.hom_ext ?_ ?_
  · simpa only [affineSpaceOrigin, AffineSpace.homOfVector_over] using hf
  · intro i
    simpa only [affineSpaceOrigin, AffineSpace.homOfVector_appTop_coord, pullbackCoord_def]
      using hcoord i

theorem isClosedImmersion_affineSpaceOrigin (k : Type u) [Field k] (m : ℕ) :
    IsClosedImmersion (affineSpaceOrigin k m) := by
  have hsurj : Function.Surjective
      (ConcreteCategory.hom (Scheme.Hom.appTop (affineSpaceOrigin k m))) := by
    intro x
    refine ⟨(ConcreteCategory.hom
        (Scheme.Hom.appTop (affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin m))))) x, ?_⟩
    have h1 : Scheme.Hom.appTop (affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin m))) ≫
        Scheme.Hom.appTop (affineSpaceOrigin k m) =
        Scheme.Hom.appTop (𝟙 (Spec (CommRingCat.of k))) := by
      rw [← Scheme.Hom.comp_appTop, affineSpaceOrigin_comp_toSpec]
    have h2 : (ConcreteCategory.hom (Scheme.Hom.appTop (affineSpaceOrigin k m)))
        ((ConcreteCategory.hom
          (Scheme.Hom.appTop (affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin m))))) x) =
        (ConcreteCategory.hom
          (Scheme.Hom.appTop (affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin m))) ≫
            Scheme.Hom.appTop (affineSpaceOrigin k m))) x := by
      simp
    rw [h2, h1]
    simp
  apply IsClosedImmersion.of_surjective_of_isAffine
  exact hsurj

instance instIsClosedImmersionAffineSpaceOrigin (k : Type u) [Field k] (m : ℕ) :
    IsClosedImmersion (affineSpaceOrigin k m) :=
  isClosedImmersion_affineSpaceOrigin k m

private theorem appTop_id (X : Scheme.{u}) :
    Scheme.Hom.appTop (𝟙 X) = 𝟙 (X.presheaf.obj (Opposite.op ⊤)) := by
  simp [Scheme.Hom.appTop]

private theorem appTop_hom_appTop_inv_apply {X Y : Scheme.{u}} (e : X ≅ Y)
    (x : ↑(X.presheaf.obj (Opposite.op ⊤))) :
    CommRingCat.Hom.hom (Scheme.Hom.appTop e.hom)
        (CommRingCat.Hom.hom (Scheme.Hom.appTop e.inv) x) = x := by
  have h : Scheme.Hom.appTop e.inv ≫ Scheme.Hom.appTop e.hom =
      𝟙 (X.presheaf.obj (Opposite.op ⊤)) := by
    rw [← Scheme.Hom.comp_appTop, e.hom_inv_id, appTop_id]
  have h2 := congrArg (fun φ => CommRingCat.Hom.hom φ x) h
  simpa using h2

private theorem nontrivial_globalSections_spec (k : Type u) [Field k] :
    Nontrivial ↑((Spec (CommRingCat.of k)).presheaf.obj (Opposite.op ⊤)) := by
  refine ⟨⟨1, 0, fun h => ?_⟩⟩
  have h3 := congrArg (fun z => CommRingCat.Hom.hom (Scheme.ΓSpecIso (CommRingCat.of k)).hom z) h
  simp only [map_one, map_zero] at h3
  have h4 : (1 : k) = 0 := h3
  exact one_ne_zero h4

private def mvPolynomialFinToAffineSpaceGlobalSections (k : Type u) [Field k] (m : ℕ) :
    MvPolynomial (ULift.{u, 0} (Fin m)) k →+*
      ↑((affineSpaceIndexedBy k (ULift.{u, 0} (Fin m))).presheaf.obj (Opposite.op ⊤)) :=
  RingHom.comp
    (CommRingCat.Hom.hom (Scheme.Hom.appTop
      (AffineSpace.SpecIso (ULift.{u, 0} (Fin m)) (CommRingCat.of k)).hom))
    (CommRingCat.Hom.hom (Scheme.ΓSpecIso
      (CommRingCat.of (MvPolynomial (ULift.{u, 0} (Fin m)) k))).inv)

private theorem mvPolynomialToSections_apply (k : Type u) [Field k] (m : ℕ)
    (x : MvPolynomial (ULift.{u, 0} (Fin m)) k) :
    mvPolynomialFinToAffineSpaceGlobalSections k m x =
      CommRingCat.Hom.hom (Scheme.Hom.appTop
        (AffineSpace.SpecIso (ULift.{u, 0} (Fin m)) (CommRingCat.of k)).hom)
        (CommRingCat.Hom.hom (Scheme.ΓSpecIso
          (CommRingCat.of (MvPolynomial (ULift.{u, 0} (Fin m)) k))).inv x) := rfl

private theorem mvPolynomialToSections_X (k : Type u) [Field k] (m : ℕ)
    (i : ULift.{u, 0} (Fin m)) :
    mvPolynomialFinToAffineSpaceGlobalSections k m (MvPolynomial.X i) =
      AffineSpace.coord (Spec (CommRingCat.of k)) i := by
  have hX : CommRingCat.Hom.hom (Scheme.Hom.appTop
        (AffineSpace.SpecIso (ULift.{u, 0} (Fin m)) (CommRingCat.of k)).inv)
        (AffineSpace.coord (Spec (CommRingCat.of k)) i) =
      CommRingCat.Hom.hom (Scheme.ΓSpecIso
        (CommRingCat.of (MvPolynomial (ULift.{u, 0} (Fin m)) k))).inv (MvPolynomial.X i) := by
    exact AffineSpace.SpecIso_inv_appTop_coord ..
  rw [mvPolynomialToSections_apply, ← hX]
  exact appTop_hom_appTop_inv_apply _ _

private theorem mvPolynomialToSections_surjective (k : Type u) [Field k] (m : ℕ) :
    Function.Surjective (mvPolynomialFinToAffineSpaceGlobalSections k m) := by
  intro x
  refine ⟨CommRingCat.Hom.hom (Scheme.ΓSpecIso
      (CommRingCat.of (MvPolynomial (ULift.{u, 0} (Fin m)) k))).hom
      (CommRingCat.Hom.hom (Scheme.Hom.appTop
        (AffineSpace.SpecIso (ULift.{u, 0} (Fin m)) (CommRingCat.of k)).inv) x), ?_⟩
  have hinv : CommRingCat.Hom.hom (Scheme.ΓSpecIso
        (CommRingCat.of (MvPolynomial (ULift.{u, 0} (Fin m)) k))).inv
      (CommRingCat.Hom.hom (Scheme.ΓSpecIso
        (CommRingCat.of (MvPolynomial (ULift.{u, 0} (Fin m)) k))).hom
        (CommRingCat.Hom.hom (Scheme.Hom.appTop
          (AffineSpace.SpecIso (ULift.{u, 0} (Fin m)) (CommRingCat.of k)).inv) x)) =
      CommRingCat.Hom.hom (Scheme.Hom.appTop
        (AffineSpace.SpecIso (ULift.{u, 0} (Fin m)) (CommRingCat.of k)).inv) x := by
    exact CommRingCat.inv_hom_apply ..
  rw [mvPolynomialToSections_apply, hinv, appTop_hom_appTop_inv_apply]

private theorem sub_C_constantCoeff_mem_span_X {σ : Type u} {A : Type u} [CommRing A]
    (p : MvPolynomial σ A) :
    p - MvPolynomial.C (MvPolynomial.constantCoeff p) ∈
      Ideal.span (Set.range (MvPolynomial.X : σ → MvPolynomial σ A)) := by
  induction p using MvPolynomial.induction_on
  · rename_i a
    simp only [MvPolynomial.constantCoeff_C, sub_self]
    exact Ideal.zero_mem _
  · rename_i q r hq hr
    have hadd : q + r - MvPolynomial.C (MvPolynomial.constantCoeff (q + r)) =
        (q - MvPolynomial.C (MvPolynomial.constantCoeff q)) +
          (r - MvPolynomial.C (MvPolynomial.constantCoeff r)) := by
      simp only [map_add]
      ring
    rw [hadd]
    exact Ideal.add_mem _ hq hr
  · rename_i q i hq
    have hmul : q * MvPolynomial.X i -
        MvPolynomial.C (MvPolynomial.constantCoeff (q * MvPolynomial.X i)) =
        q * MvPolynomial.X i := by
      simp
    rw [hmul]
    exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨i, rfl⟩)

private theorem ker_eq_span_range_X {σ : Type u} {K : Type u} [Field K] {T : Type u}
    [CommRing T] [Nontrivial T] (g : MvPolynomial σ K →+* T)
    (hg : ∀ i, g (MvPolynomial.X i) = 0) :
    RingHom.ker g = Ideal.span (Set.range (MvPolynomial.X : σ → MvPolynomial σ K)) := by
  have hspan : Ideal.span (Set.range (MvPolynomial.X : σ → MvPolynomial σ K)) ≤ RingHom.ker g := by
    rw [Ideal.span_le]
    rintro x ⟨i, rfl⟩
    simpa [RingHom.mem_ker] using hg i
  refine le_antisymm ?_ hspan
  intro p hp
  have hsub := sub_C_constantCoeff_mem_span_X (σ := σ) (A := K) p
  have h1 : g (p - MvPolynomial.C (MvPolynomial.constantCoeff p)) = 0 :=
    RingHom.mem_ker.mp (hspan hsub)
  have hp0 : g p = 0 := RingHom.mem_ker.mp hp
  have h0 : g (MvPolynomial.C (MvPolynomial.constantCoeff p)) = 0 := by
    rw [map_sub, hp0, zero_sub, neg_eq_zero] at h1
    exact h1
  have hc : MvPolynomial.constantCoeff p = 0 := by
    have hinj : Function.Injective (g.comp (MvPolynomial.C : K →+* MvPolynomial σ K)) :=
      RingHom.injective _
    apply hinj
    simpa using h0
  have hpe : p = p - MvPolynomial.C (MvPolynomial.constantCoeff p) := by
    rw [hc, map_zero, sub_zero]
  rw [hpe]
  exact hsub

private theorem ker_eq_span_image_of_surjective {A B C : Type u} [CommRing A] [CommRing B]
    [CommRing C] (ψ : A →+* B) (hsurj : Function.Surjective ψ) (g : B →+* C) (s : Set A)
    (h : RingHom.ker (g.comp ψ) = Ideal.span s) :
    RingHom.ker g = Ideal.span (ψ '' s) := by
  have h1 : Ideal.comap ψ (RingHom.ker g) = Ideal.span s := by
    rw [← h]
    ext x
    simp [RingHom.mem_ker, Ideal.mem_comap]
  have h2 : Ideal.map ψ (Ideal.comap ψ (RingHom.ker g)) = RingHom.ker g :=
    Ideal.map_comap_of_surjective ψ hsurj _
  rw [← h2, h1, Ideal.map_span]

private theorem ker_appTop_affineSpaceOrigin (k : Type u) [Field k] (m : ℕ) :
    RingHom.ker (CommRingCat.Hom.hom (Scheme.Hom.appTop (affineSpaceOrigin k m))) =
      Ideal.span (Set.range fun i : Fin m =>
        AffineSpace.coord (Spec (CommRingCat.of k)) (ULift.up.{u, 0} i)) := by
  have := nontrivial_globalSections_spec k
  have hcomp : RingHom.ker
      ((CommRingCat.Hom.hom (Scheme.Hom.appTop (affineSpaceOrigin k m))).comp
        (mvPolynomialFinToAffineSpaceGlobalSections k m)) =
      Ideal.span (Set.range
        (MvPolynomial.X : ULift.{u, 0} (Fin m) → MvPolynomial (ULift.{u, 0} (Fin m)) k)) := by
    refine ker_eq_span_range_X _ ?_
    intro i
    rw [RingHom.comp_apply, mvPolynomialToSections_X k m i]
    exact affineSpaceOrigin_appTop_coord k m i
  have main := ker_eq_span_image_of_surjective (mvPolynomialFinToAffineSpaceGlobalSections k m)
    (mvPolynomialToSections_surjective k m)
    (CommRingCat.Hom.hom (Scheme.Hom.appTop (affineSpaceOrigin k m))) _ hcomp
  rw [main]
  congr 1
  ext y
  constructor
  · rintro ⟨p, hp, rfl⟩
    obtain ⟨j, rfl⟩ := hp
    exact ⟨j.down, (mvPolynomialToSections_X k m j).symm⟩
  · rintro ⟨i, rfl⟩
    exact ⟨MvPolynomial.X (ULift.up.{u, 0} i), Set.mem_range_self _,
      mvPolynomialToSections_X k m (ULift.up.{u, 0} i)⟩

theorem ker_affineSpaceOrigin (k : Type u) [Field k] (m : ℕ) :
    Scheme.Hom.ker (affineSpaceOrigin k m) = coordSubspaceIdeal k m Finset.univ := by
  have : QuasiCompact (affineSpaceOrigin k m) := inferInstance
  have hker : RingHom.ker (CommRingCat.Hom.hom (Scheme.Hom.app (affineSpaceOrigin k m) ⊤)) =
      Ideal.span (Set.range fun i : Fin m =>
        AffineSpace.coord (Spec (CommRingCat.of k)) (ULift.up.{u, 0} i)) :=
    ker_appTop_affineSpaceOrigin k m
  refine Scheme.IdealSheafData.ext_of_isAffine ?_
  rw [coordSubspaceIdeal_eq_ofIdealTop_span_coord]
  simpa using hker

private theorem pullbackCoord_comp_eq_hom_appTop_apply {k : Type u} [Field k]
    {Y Z : Scheme.{u}} {n : Type u} (f : Y ⟶ Z) (g : Z ⟶ affineSpaceIndexedBy k n) (i : n) :
    pullbackCoord (f ≫ g) i =
      (ConcreteCategory.hom (Scheme.Hom.appTop f)) (pullbackCoord g i) := by
  rw [pullbackCoord_def, pullbackCoord_def, Scheme.Hom.comp_appTop]
  rfl

@[simp]
theorem affineSpaceInl_comp_projLeft (k : Type u) [Field k] (n m : ℕ) :
    affineSpaceInl k n m ≫ projLeft k n m = 𝟙 (affineSpaceIndexedBy k (ULift.{u, 0} (Fin n))) := by
  refine AffineSpace.hom_ext ?_ ?_
  · rw [Category.assoc, projLeft_comp_affineSpaceIndexedByToSpec, affineSpaceInl_comp_affineSpaceIndexedByToSpec, Category.id_comp]
  · rintro ⟨a⟩
    have h : pullbackCoord (affineSpaceInl k n m ≫ projLeft k n m) (ULift.up.{u, 0} a) =
        AffineSpace.coord (Spec (CommRingCat.of k)) (ULift.up.{u, 0} a) := by
      rw [pullbackCoord_comp_eq_hom_appTop_apply, pullbackCoord_def (projLeft k n m),
        projLeft_appTop_coord, ← pullbackCoord_def, pullbackCoord_affineSpaceInl_inl]
    rw [← pullbackCoord_def, h]
    simp

@[simp]
theorem affineSpaceInl_comp_projLeft_assoc (k : Type u) [Field k] (n m : ℕ) {Z : Scheme.{u}}
    (g : affineSpaceIndexedBy k (ULift.{u, 0} (Fin n)) ⟶ Z) :
    affineSpaceInl k n m ≫ projLeft k n m ≫ g = g := by
  rw [← Category.assoc, affineSpaceInl_comp_projLeft, Category.id_comp]

@[simp]
theorem affineSpaceInrEmbedding_comp_projRight (k : Type u) [Field k] (n m : ℕ) :
    affineSpaceInrEmbedding k n m ≫ projRight k n m = 𝟙 (affineSpaceIndexedBy k (ULift.{u, 0} (Fin m))) := by
  refine AffineSpace.hom_ext ?_ ?_
  · rw [Category.assoc, projRight_comp_affineSpaceIndexedByToSpec, affineSpaceInrEmbedding_comp_affineSpaceIndexedByToSpec, Category.id_comp]
  · rintro ⟨b⟩
    have h : pullbackCoord (affineSpaceInrEmbedding k n m ≫ projRight k n m) (ULift.up.{u, 0} b) =
        AffineSpace.coord (Spec (CommRingCat.of k)) (ULift.up.{u, 0} b) := by
      rw [pullbackCoord_comp_eq_hom_appTop_apply, pullbackCoord_def (projRight k n m),
        projRight_appTop_coord, ← pullbackCoord_def, pullbackCoord_affineSpaceInrEmbedding_inr]
    rw [← pullbackCoord_def, h]
    simp

@[simp]
theorem affineSpaceInrEmbedding_comp_projRight_assoc (k : Type u) [Field k] (n m : ℕ) {Z : Scheme.{u}}
    (g : affineSpaceIndexedBy k (ULift.{u, 0} (Fin m)) ⟶ Z) :
    affineSpaceInrEmbedding k n m ≫ projRight k n m ≫ g = g := by
  rw [← Category.assoc, affineSpaceInrEmbedding_comp_projRight, Category.id_comp]

theorem affineSpaceInl_comp_projRight (k : Type u) [Field k] (n m : ℕ) :
    affineSpaceInl k n m ≫ projRight k n m =
      affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin n)) ≫ affineSpaceOrigin k m := by
  refine AffineSpace.hom_ext ?_ ?_
  · rw [Category.assoc, projRight_comp_affineSpaceIndexedByToSpec, affineSpaceInl_comp_affineSpaceIndexedByToSpec, Category.assoc,
      affineSpaceOrigin_comp_toSpec, Category.comp_id]
  · rintro ⟨b⟩
    have h : pullbackCoord (affineSpaceInl k n m ≫ projRight k n m) (ULift.up.{u, 0} b) = 0 := by
      rw [pullbackCoord_comp_eq_hom_appTop_apply, pullbackCoord_def (projRight k n m),
        projRight_appTop_coord, ← pullbackCoord_def, pullbackCoord_affineSpaceInl_inr]
    have h2 : pullbackCoord
        (affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin n)) ≫ affineSpaceOrigin k m)
        (ULift.up.{u, 0} b) = 0 := by
      rw [pullbackCoord_comp_eq_hom_appTop_apply, pullbackCoord_affineSpaceOrigin, map_zero]
    rw [← pullbackCoord_def, ← pullbackCoord_def, h, h2]

theorem affineSpaceInrEmbedding_comp_projLeft (k : Type u) [Field k] (n m : ℕ) :
    affineSpaceInrEmbedding k n m ≫ projLeft k n m =
      affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin m)) ≫ affineSpaceOrigin k n := by
  refine AffineSpace.hom_ext ?_ ?_
  · rw [Category.assoc, projLeft_comp_affineSpaceIndexedByToSpec, affineSpaceInrEmbedding_comp_affineSpaceIndexedByToSpec, Category.assoc,
      affineSpaceOrigin_comp_toSpec, Category.comp_id]
  · rintro ⟨a⟩
    have h : pullbackCoord (affineSpaceInrEmbedding k n m ≫ projLeft k n m) (ULift.up.{u, 0} a) = 0 := by
      rw [pullbackCoord_comp_eq_hom_appTop_apply, pullbackCoord_def (projLeft k n m),
        projLeft_appTop_coord, ← pullbackCoord_def, pullbackCoord_affineSpaceInrEmbedding_inl]
    have h2 : pullbackCoord (affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin m)) ≫
        affineSpaceOrigin k n) (ULift.up.{u, 0} a) = 0 := by
      rw [pullbackCoord_comp_eq_hom_appTop_apply, pullbackCoord_affineSpaceOrigin]
      simp
    rw [← pullbackCoord_def, ← pullbackCoord_def, h, h2]

theorem ker_affineSpaceInl_eq_comap (hsm : AffineSpaceIsSmooth.{u}) (k : Type u) [Field k] (n m : ℕ) :
    Scheme.Hom.ker (affineSpaceInl k n m) =
      (Scheme.Hom.ker (affineSpaceOrigin k m)).comap (projRight k n m) := by
  have hsmooth : AlgebraicGeometry.Smooth (projRight k n m) := smooth_projRight hsm k n m
  have hflat : AlgebraicGeometry.Flat (projRight k n m) := inferInstance
  have hbig : IsPullback (affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin n)))
      (affineSpaceInl k n m ≫ projLeft k n m)
      (affineSpaceOrigin k m ≫ affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin m)))
      (affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin n))) := by
    rw [affineSpaceInl_comp_projLeft, affineSpaceOrigin_comp_toSpec]
    exact IsPullback.id_vert _
  have hsq : IsPullback (affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin n))) (affineSpaceInl k n m)
      (affineSpaceOrigin k m) (projRight k n m) :=
    IsPullback.of_bot hbig (affineSpaceInl_comp_projRight k n m).symm
      (isPullback_projLeft_projRight k n m).flip
  have : QuasiCompact (affineSpaceOrigin k m) := inferInstance
  have : QuasiCompact (affineSpaceInl k n m) := quasiCompact_of_isPullback hsq
  exact ker_eq_comap_ker_of_isPullback_of_flat hsq

private theorem isPullback_affineSpaceInrEmbedding_projLeft (k : Type u) [Field k] (n m : ℕ) :
    IsPullback (affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin m))) (affineSpaceInrEmbedding k n m)
      (affineSpaceOrigin k n) (projLeft k n m) := by
  have h0 : IsPullback (𝟙 (affineSpaceIndexedBy k (ULift.{u, 0} (Fin m))))
      (affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin m)))
      (affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin m)))
      (𝟙 (Spec (CommRingCat.of k))) :=
    IsPullback.of_horiz_isIso ⟨by simp⟩
  have s : IsPullback (affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin m)))
      (affineSpaceInrEmbedding k n m ≫ projRight k n m)
      (affineSpaceOrigin k n ≫ affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin n)))
      (affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin m))) := by
    rw [affineSpaceInrEmbedding_comp_projRight, affineSpaceOrigin_comp_toSpec]
    exact h0.flip
  exact IsPullback.of_bot s (affineSpaceInrEmbedding_comp_projLeft k n m).symm
    (isPullback_projLeft_projRight k n m)

theorem ker_affineSpaceInrEmbedding_eq_comap (hsm : AffineSpaceIsSmooth.{u}) (k : Type u) [Field k] (n m : ℕ) :
    Scheme.Hom.ker (affineSpaceInrEmbedding k n m) =
      (Scheme.Hom.ker (affineSpaceOrigin k n)).comap (projLeft k n m) := by
  have hsmooth : AlgebraicGeometry.Smooth (projLeft k n m) := smooth_projLeft hsm k n m
  have hflat : AlgebraicGeometry.Flat (projLeft k n m) := inferInstance
  have hq1 : AlgebraicGeometry.QuasiCompact (affineSpaceOrigin k n) := inferInstance
  have hq2 : AlgebraicGeometry.QuasiCompact (affineSpaceInrEmbedding k n m) := inferInstance
  exact ker_eq_comap_ker_of_isPullback_of_flat (isPullback_affineSpaceInrEmbedding_projLeft k n m)

theorem hasSmoothCoordCodim_affineSpaceInl (hsm : AffineSpaceIsSmooth.{u}) (k : Type u) [Field k]
    (n m : ℕ) :
    HasSmoothCoordCodim (affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin n ⊕ Fin m)))
      (affineSpaceInl k n m) m := by
  have hsp : AlgebraicGeometry.Smooth (projRight k n m) := smooth_projRight hsm k n m
  intro x
  refine ⟨⊤, ?_, (⊤ : (affineSpaceIndexedBy k (ULift.{u, 0} (Fin n ⊕ Fin m))).Opens).ι ≫
      projRight k n m, ?_, ?_, ?_⟩
  · trivial
  · infer_instance
  · rw [Category.assoc, projRight_comp_affineSpaceIndexedByToSpec]
  · rw [restrictIdeal_eq_comap_ι, ker_affineSpaceInl_eq_comap hsm, ker_affineSpaceOrigin,
      Scheme.IdealSheafData.comap_comp]

theorem hasSmoothCoordCodim_affineSpaceInrEmbedding (hsm : AffineSpaceIsSmooth.{u}) (k : Type u) [Field k]
    (n m : ℕ) :
    HasSmoothCoordCodim (affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin n ⊕ Fin m)))
      (affineSpaceInrEmbedding k n m) n := by
  have hsmooth : AlgebraicGeometry.Smooth (projLeft k n m) := smooth_projLeft hsm k n m
  intro x
  refine ⟨⊤, by simp, (⊤ : (affineSpaceIndexedBy k (ULift.{u, 0} (Fin n ⊕ Fin m))).Opens).ι ≫
      projLeft k n m, inferInstance, ?_, ?_⟩
  · rw [Category.assoc, projLeft_comp_affineSpaceIndexedByToSpec]
  · rw [restrictIdeal_eq_comap_ι, ker_affineSpaceInrEmbedding_eq_comap hsm k n m, ker_affineSpaceOrigin k n]
    simp [Scheme.IdealSheafData.comap_comp]

end FunctorialResolution.EmbeddedResolution

end
