import Mathlib
import Development.ResolutionOfSingularities.Foundations.Blowup.BlowupBasic
import Development.ResolutionOfSingularities.Foundations.Blowup.BlowupExistence
import Development.ResolutionOfSingularities.Foundations.Blowup.BlowupProperties
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.ClopenRestriction
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.AffineSpaceCoordinates
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.SmoothCoordinateCodimension
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.SmoothCoordinateCodimensionPullback
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.StrictNormalCrossings
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.AffineResolutionRule
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.AffineSpaceOrigin
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.AffineSpaceZeroSection
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.AffineSpaceProduct
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.AffineSpaceChartPresentation
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.AffineSpaceLinearEmbeddings
import Development.ResolutionOfSingularities.Foundations.Schemes.IdealSheafData
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReductionProperties
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MonomialCase.CenterInvariant
import Development.ResolutionOfSingularities.Foundations.BlowupUniversalProperty
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionOfSingularities
universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

abbrev affineSpaceTimesLine (k : Type u) [Field k] (M : ℕ) : Scheme.{u} :=
  affineSpaceIndexedBy k (ULift.{u, 0} (Fin M ⊕ Fin 1))

def lastCoordinate (k : Type u) [Field k] (M : ℕ) :
    ↑((affineSpaceTimesLine k M).presheaf.obj (Opposite.op ⊤)) :=
  AffineSpace.coord (Spec (CommRingCat.of k)) (⟨Sum.inr 0⟩ : ULift.{u, 0} (Fin M ⊕ Fin 1))

@[simp]
theorem lastCoordinate_eq (k : Type u) [Field k] (M : ℕ) :
    lastCoordinate k M =
      AffineSpace.coord (Spec (CommRingCat.of k)) (⟨Sum.inr 0⟩ : ULift.{u, 0} (Fin M ⊕ Fin 1)) :=
  rfl

theorem lastCoordinate_eq_coord (k : Type u) [Field k] (M : ℕ) (j : Fin 1) :
    lastCoordinate k M =
      AffineSpace.coord (Spec (CommRingCat.of k)) (⟨Sum.inr j⟩ : ULift.{u, 0} (Fin M ⊕ Fin 1)) := by
  rw [Subsingleton.elim j (0 : Fin 1)]
  rfl

theorem lastCoordinate_appTop_comp_affineSpaceInl (k : Type u) [Field k] (M : ℕ) {A : Scheme.{u}}
    (f : A ⟶ affineSpaceIndexedBy k (ULift.{u, 0} (Fin M))) :
    (ConcreteCategory.hom (Scheme.Hom.appTop (f ≫ affineSpaceInl k M 1))) (lastCoordinate k M) = 0 := by
  have h1 := pullbackCoord_affineSpaceInl_inr k M 1 (0 : Fin 1)
  rw [pullbackCoord_def] at h1
  rw [Scheme.Hom.comp_appTop, CommRingCat.comp_apply, lastCoordinate_eq, h1, map_zero]

def pullbackAlongProjection (k : Type u) [Field k] (M : ℕ)
    (G : ↑((affineSpaceIndexedBy k (ULift.{u, 0} (Fin M))).presheaf.obj (Opposite.op ⊤))) :
    ↑((affineSpaceTimesLine k M).presheaf.obj (Opposite.op ⊤)) :=
  (ConcreteCategory.hom (Scheme.Hom.appTop (projLeft k M 1))) G

def pullbackBasicOpen (k : Type u) [Field k] (M : ℕ)
    (G : ↑((affineSpaceIndexedBy k (ULift.{u, 0} (Fin M))).presheaf.obj (Opposite.op ⊤))) :
    (affineSpaceTimesLine k M).Opens :=
  (affineSpaceTimesLine k M).basicOpen (pullbackAlongProjection k M G)

private theorem isUnit_appTop_ι_basicOpen {X : Scheme.{u}}
    (f : ↑(X.presheaf.obj (Opposite.op ⊤))) :
    IsUnit ((ConcreteCategory.hom (Scheme.Hom.appTop (X.basicOpen f).ι)) f) := by
  have h1 : (↑(X.basicOpen f) : Scheme.{u}).basicOpen
        ((ConcreteCategory.hom (Scheme.Hom.appTop (X.basicOpen f).ι)) f) =
      (X.basicOpen f).ι ⁻¹ᵁ X.basicOpen f := (Scheme.preimage_basicOpen ..).symm
  have h2 : (X.basicOpen f).ι ⁻¹ᵁ X.basicOpen f = ⊤ :=
    Opens.ext (Set.eq_univ_of_forall fun x => x.2)
  have hbo := h1.trans h2
  refine RingedSpace.isUnit_of_isUnit_germ
    ((↑(X.basicOpen f) : Scheme.{u}).toLocallyRingedSpace.toRingedSpace) ⊤ _ ?_
  intro x hx
  refine ((↑(X.basicOpen f) : Scheme.{u}).mem_basicOpen
    ((ConcreteCategory.hom (Scheme.Hom.appTop (X.basicOpen f).ι)) f) x hx).mp ?_
  rw [hbo]
  exact Opens.mem_top _

theorem isUnit_appTop_ι_pullbackAlongProjection (k : Type u) [Field k] (M : ℕ)
    (G : ↑((affineSpaceIndexedBy k (ULift.{u, 0} (Fin M))).presheaf.obj (Opposite.op ⊤))) :
    IsUnit ((ConcreteCategory.hom (Scheme.Hom.appTop (pullbackBasicOpen k M G).ι)) (pullbackAlongProjection k M G)) :=
  isUnit_appTop_ι_basicOpen (pullbackAlongProjection k M G)

def unitOnPullbackBasicOpen (k : Type u) [Field k] (M : ℕ)
    (G : ↑((affineSpaceIndexedBy k (ULift.{u, 0} (Fin M))).presheaf.obj (Opposite.op ⊤))) :
    (↑((↑(pullbackBasicOpen k M G) : Scheme.{u}).presheaf.obj (Opposite.op ⊤)))ˣ :=
  (isUnit_appTop_ι_pullbackAlongProjection k M G).unit

@[simp]
theorem unitOnPullbackBasicOpen_val (k : Type u) [Field k] (M : ℕ)
    (G : ↑((affineSpaceIndexedBy k (ULift.{u, 0} (Fin M))).presheaf.obj (Opposite.op ⊤))) :
    (unitOnPullbackBasicOpen k M G).val =
      (ConcreteCategory.hom (Scheme.Hom.appTop (pullbackBasicOpen k M G).ι)) (pullbackAlongProjection k M G) :=
  IsUnit.unit_spec _

private theorem appTop_comp_projLeft_coord (k : Type u) [Field k] (M : ℕ) {T : Scheme.{u}}
    (t : T ⟶ affineSpaceIndexedBy k (ULift.{u, 0} (Fin M ⊕ Fin 1))) (j : Fin M) :
    (ConcreteCategory.hom (Scheme.Hom.appTop (t ≫ projLeft k M 1)))
        (AffineSpace.coord (Spec (CommRingCat.of k)) (⟨j⟩ : ULift.{u, 0} (Fin M))) =
      (ConcreteCategory.hom (Scheme.Hom.appTop t))
        (AffineSpace.coord (Spec (CommRingCat.of k))
          (⟨Sum.inl j⟩ : ULift.{u, 0} (Fin M ⊕ Fin 1))) := by
  rw [Scheme.Hom.comp_appTop, CommRingCat.comp_apply, projLeft_appTop_coord]

private theorem exists_replaceLastCoord (k : Type u) [Field k] (M : ℕ)
    (G : ↑((affineSpaceIndexedBy k (ULift.{u, 0} (Fin M))).presheaf.obj (Opposite.op ⊤)))
    (s : ↑((↑(pullbackBasicOpen k M G) : Scheme.{u}).presheaf.obj (Opposite.op ⊤))) :
    ∃ f : (↑(pullbackBasicOpen k M G) : Scheme.{u}) ⟶ affineSpaceTimesLine k M,
      f ≫ affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin M ⊕ Fin 1)) =
          (pullbackBasicOpen k M G).ι ≫ affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin M ⊕ Fin 1)) ∧
      (∀ a : Fin M,
          pullbackCoord f ⟨Sum.inl a⟩ = pullbackCoord (pullbackBasicOpen k M G).ι ⟨Sum.inl a⟩) ∧
      (ConcreteCategory.hom (Scheme.Hom.appTop f)) (lastCoordinate k M) = s ∧
      f ≫ projLeft k M 1 = (pullbackBasicOpen k M G).ι ≫ projLeft k M 1 := by
  obtain ⟨f, hover, hcoord⟩ :
      ∃ f : (↑(pullbackBasicOpen k M G) : Scheme.{u}) ⟶ affineSpaceTimesLine k M,
        f ≫ affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin M ⊕ Fin 1)) =
            (pullbackBasicOpen k M G).ι ≫ affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin M ⊕ Fin 1)) ∧
          ∀ i : ULift.{u, 0} (Fin M ⊕ Fin 1),
            (ConcreteCategory.hom (Scheme.Hom.appTop f))
                (AffineSpace.coord (Spec (CommRingCat.of k)) i) =
              Sum.elim
                (fun a : Fin M =>
                  pullbackCoord (pullbackBasicOpen k M G).ι (⟨Sum.inl a⟩ : ULift.{u, 0} (Fin M ⊕ Fin 1)))
                (fun _ : Fin 1 => s) i.down := by
    refine ⟨AffineSpace.homOfVector
        ((pullbackBasicOpen k M G).ι ≫ affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin M ⊕ Fin 1)))
        (fun i : ULift.{u, 0} (Fin M ⊕ Fin 1) =>
          Sum.elim
            (fun a : Fin M =>
              pullbackCoord (pullbackBasicOpen k M G).ι (⟨Sum.inl a⟩ : ULift.{u, 0} (Fin M ⊕ Fin 1)))
            (fun _ : Fin 1 => s) i.down), ?_, ?_⟩
    · apply AffineSpace.homOfVector_over
    · intro i
      rw [AffineSpace.homOfVector_appTop_coord]
  refine ⟨f, hover, ?_, ?_, ?_⟩
  · intro a
    exact (pullbackCoord_def f (⟨Sum.inl a⟩ : ULift.{u, 0} (Fin M ⊕ Fin 1))).trans
      (hcoord (⟨Sum.inl a⟩ : ULift.{u, 0} (Fin M ⊕ Fin 1)))
  · exact hcoord (⟨Sum.inr 0⟩ : ULift.{u, 0} (Fin M ⊕ Fin 1))
  · refine AffineSpace.hom_ext ?_ ?_
    · have h1 : (f ≫ projLeft k M 1) ≫ affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin M)) =
          ((pullbackBasicOpen k M G).ι ≫ projLeft k M 1) ≫
            affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin M)) := by
        rw [Category.assoc, Category.assoc, projLeft_comp_affineSpaceIndexedByToSpec, hover]
      exact h1
    · intro i
      obtain ⟨j⟩ := i
      exact (appTop_comp_projLeft_coord k M f j).trans
        ((hcoord (⟨Sum.inl j⟩ : ULift.{u, 0} (Fin M ⊕ Fin 1))).trans
          ((pullbackCoord_def (pullbackBasicOpen k M G).ι
              (⟨Sum.inl j⟩ : ULift.{u, 0} (Fin M ⊕ Fin 1))).trans
            (appTop_comp_projLeft_coord k M (pullbackBasicOpen k M G).ι j).symm))

def replaceLastCoord (k : Type u) [Field k] (M : ℕ)
    (G : ↑((affineSpaceIndexedBy k (ULift.{u, 0} (Fin M))).presheaf.obj (Opposite.op ⊤)))
    (s : ↑((↑(pullbackBasicOpen k M G) : Scheme.{u}).presheaf.obj (Opposite.op ⊤))) :
    (↑(pullbackBasicOpen k M G) : Scheme.{u}) ⟶ affineSpaceTimesLine k M :=
  (exists_replaceLastCoord k M G s).choose

theorem replaceLastCoord_comp_affineSpaceIndexedByToSpec (k : Type u) [Field k] (M : ℕ)
    (G : ↑((affineSpaceIndexedBy k (ULift.{u, 0} (Fin M))).presheaf.obj (Opposite.op ⊤)))
    (s : ↑((↑(pullbackBasicOpen k M G) : Scheme.{u}).presheaf.obj (Opposite.op ⊤))) :
    replaceLastCoord k M G s ≫ affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin M ⊕ Fin 1)) =
      (pullbackBasicOpen k M G).ι ≫ affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin M ⊕ Fin 1)) :=
  (exists_replaceLastCoord k M G s).choose_spec.1

theorem pullbackCoord_replaceLastCoord_inl (k : Type u) [Field k] (M : ℕ)
    (G : ↑((affineSpaceIndexedBy k (ULift.{u, 0} (Fin M))).presheaf.obj (Opposite.op ⊤)))
    (s : ↑((↑(pullbackBasicOpen k M G) : Scheme.{u}).presheaf.obj (Opposite.op ⊤))) (a : Fin M) :
    pullbackCoord (replaceLastCoord k M G s) ⟨Sum.inl a⟩ =
      pullbackCoord (pullbackBasicOpen k M G).ι ⟨Sum.inl a⟩ :=
  (exists_replaceLastCoord k M G s).choose_spec.2.1 a

theorem replaceLastCoord_appTop_lastCoordinate (k : Type u) [Field k] (M : ℕ)
    (G : ↑((affineSpaceIndexedBy k (ULift.{u, 0} (Fin M))).presheaf.obj (Opposite.op ⊤)))
    (s : ↑((↑(pullbackBasicOpen k M G) : Scheme.{u}).presheaf.obj (Opposite.op ⊤))) :
    (ConcreteCategory.hom (Scheme.Hom.appTop (replaceLastCoord k M G s))) (lastCoordinate k M) = s :=
  (exists_replaceLastCoord k M G s).choose_spec.2.2.1

@[simp]
theorem replaceLastCoord_comp_projLeft (k : Type u) [Field k] (M : ℕ)
    (G : ↑((affineSpaceIndexedBy k (ULift.{u, 0} (Fin M))).presheaf.obj (Opposite.op ⊤)))
    (s : ↑((↑(pullbackBasicOpen k M G) : Scheme.{u}).presheaf.obj (Opposite.op ⊤))) :
    replaceLastCoord k M G s ≫ projLeft k M 1 = (pullbackBasicOpen k M G).ι ≫ projLeft k M 1 :=
  (exists_replaceLastCoord k M G s).choose_spec.2.2.2

@[simp]
theorem replaceLastCoord_comp_projLeft_assoc (k : Type u) [Field k] (M : ℕ)
    (G : ↑((affineSpaceIndexedBy k (ULift.{u, 0} (Fin M))).presheaf.obj (Opposite.op ⊤)))
    (s : ↑((↑(pullbackBasicOpen k M G) : Scheme.{u}).presheaf.obj (Opposite.op ⊤))) {Z : Scheme.{u}}
    (g : affineSpaceIndexedBy k (ULift.{u, 0} (Fin M)) ⟶ Z) :
    replaceLastCoord k M G s ≫ projLeft k M 1 ≫ g = (pullbackBasicOpen k M G).ι ≫ projLeft k M 1 ≫ g := by
  rw [← Category.assoc, replaceLastCoord_comp_projLeft, Category.assoc]

private theorem mem_pullbackBasicOpen_iff (k : Type u) [Field k] (M : ℕ)
    (G : ↑((affineSpaceIndexedBy k (ULift.{u, 0} (Fin M))).presheaf.obj (Opposite.op ⊤)))
    (y : ↥(affineSpaceTimesLine k M)) :
    y ∈ pullbackBasicOpen k M G ↔
      (projLeft k M 1).base y ∈ (affineSpaceIndexedBy k (ULift.{u, 0} (Fin M))).basicOpen G :=
  Iff.symm (iff_of_eq (congrArg (fun U : (affineSpaceTimesLine k M).Opens => y ∈ U)
    (Scheme.preimage_basicOpen (projLeft k M 1) G)))

private theorem exists_comp_ι_eq_replaceLastCoord (k : Type u) [Field k] (M : ℕ)
    (G : ↑((affineSpaceIndexedBy k (ULift.{u, 0} (Fin M))).presheaf.obj (Opposite.op ⊤)))
    (s : ↑((↑(pullbackBasicOpen k M G) : Scheme.{u}).presheaf.obj (Opposite.op ⊤))) :
    ∃ g : (↑(pullbackBasicOpen k M G) : Scheme.{u}) ⟶ (↑(pullbackBasicOpen k M G) : Scheme.{u}),
      g ≫ (pullbackBasicOpen k M G).ι = replaceLastCoord k M G s := by
  have hrange : Set.range (replaceLastCoord k M G s).base ⊆
      Set.range (pullbackBasicOpen k M G).ι.base := by
    rintro _ ⟨x, rfl⟩
    have h1 : (projLeft k M 1).base ((replaceLastCoord k M G s).base x) =
        (projLeft k M 1).base ((pullbackBasicOpen k M G).ι.base x) :=
      congrArg (fun f : (↑(pullbackBasicOpen k M G) : Scheme.{u}) ⟶
          affineSpaceIndexedBy k (ULift.{u, 0} (Fin M)) => f.base x)
        (replaceLastCoord_comp_projLeft k M G s)
    have hx : (pullbackBasicOpen k M G).ι.base x ∈ pullbackBasicOpen k M G := by
      have h0 : (pullbackBasicOpen k M G).ι.base x ∈ Set.range (pullbackBasicOpen k M G).ι.base :=
        Set.mem_range_self x
      rw [Scheme.Opens.range_ι] at h0
      exact h0
    have h2 := (mem_pullbackBasicOpen_iff k M G ((pullbackBasicOpen k M G).ι.base x)).1 hx
    rw [Scheme.Opens.range_ι]
    refine (mem_pullbackBasicOpen_iff k M G ((replaceLastCoord k M G s).base x)).2 ?_
    rw [h1]
    exact h2
  exact ⟨IsOpenImmersion.lift (pullbackBasicOpen k M G).ι (replaceLastCoord k M G s) hrange,
    IsOpenImmersion.lift_fac (pullbackBasicOpen k M G).ι (replaceLastCoord k M G s) hrange⟩

def shiftLastCoord (k : Type u) [Field k] (M : ℕ)
    (G : ↑((affineSpaceIndexedBy k (ULift.{u, 0} (Fin M))).presheaf.obj (Opposite.op ⊤)))
    (s : ↑((↑(pullbackBasicOpen k M G) : Scheme.{u}).presheaf.obj (Opposite.op ⊤))) :
    (↑(pullbackBasicOpen k M G) : Scheme.{u}) ⟶ (↑(pullbackBasicOpen k M G) : Scheme.{u}) :=
  (exists_comp_ι_eq_replaceLastCoord k M G s).choose

@[simp]
theorem shiftLastCoord_comp_ι (k : Type u) [Field k] (M : ℕ)
    (G : ↑((affineSpaceIndexedBy k (ULift.{u, 0} (Fin M))).presheaf.obj (Opposite.op ⊤)))
    (s : ↑((↑(pullbackBasicOpen k M G) : Scheme.{u}).presheaf.obj (Opposite.op ⊤))) :
    shiftLastCoord k M G s ≫ (pullbackBasicOpen k M G).ι = replaceLastCoord k M G s :=
  (exists_comp_ι_eq_replaceLastCoord k M G s).choose_spec

@[simp]
theorem shiftLastCoord_comp_ι_assoc (k : Type u) [Field k] (M : ℕ)
    (G : ↑((affineSpaceIndexedBy k (ULift.{u, 0} (Fin M))).presheaf.obj (Opposite.op ⊤)))
    (s : ↑((↑(pullbackBasicOpen k M G) : Scheme.{u}).presheaf.obj (Opposite.op ⊤))) {Z : Scheme.{u}}
    (g : affineSpaceTimesLine k M ⟶ Z) :
    shiftLastCoord k M G s ≫ (pullbackBasicOpen k M G).ι ≫ g = replaceLastCoord k M G s ≫ g := by
  rw [← Category.assoc, shiftLastCoord_comp_ι]

private theorem appTop_surjective_of_isAffine {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsAffine Y] [IsClosedImmersion f] :
    Function.Surjective (ConcreteCategory.hom (Scheme.Hom.appTop f)) :=
  (IsClosedImmersion.isAffine_surjective_of_isAffine ..).2

private theorem exists_appTop_eq_of_isClosedImmersion (k : Type u) [Field k] (M : ℕ) {A : Scheme.{u}}
    (ρ : A ⟶ affineSpaceIndexedBy k (ULift.{u, 0} (Fin M))) [IsClosedImmersion ρ]
    (F : ↑(A.presheaf.obj (Opposite.op ⊤))) :
    ∃ G : ↑((affineSpaceIndexedBy k (ULift.{u, 0} (Fin M))).presheaf.obj (Opposite.op ⊤)),
      (ConcreteCategory.hom (Scheme.Hom.appTop ρ)) G = F :=
  appTop_surjective_of_isAffine ρ F

def globalSectionLift (k : Type u) [Field k] (M : ℕ) {A : Scheme.{u}}
    (ρ : A ⟶ affineSpaceIndexedBy k (ULift.{u, 0} (Fin M))) [IsClosedImmersion ρ]
    (F : ↑(A.presheaf.obj (Opposite.op ⊤))) :
    ↑((affineSpaceIndexedBy k (ULift.{u, 0} (Fin M))).presheaf.obj (Opposite.op ⊤)) :=
  (exists_appTop_eq_of_isClosedImmersion k M ρ F).choose

@[simp]
theorem appTop_globalSectionLift (k : Type u) [Field k] (M : ℕ) {A : Scheme.{u}}
    (ρ : A ⟶ affineSpaceIndexedBy k (ULift.{u, 0} (Fin M))) [IsClosedImmersion ρ]
    (F : ↑(A.presheaf.obj (Opposite.op ⊤))) :
    (ConcreteCategory.hom (Scheme.Hom.appTop ρ)) (globalSectionLift k M ρ F) = F :=
  (exists_appTop_eq_of_isClosedImmersion k M ρ F).choose_spec

private theorem pullbackAlongProjection_eq (k : Type u) [Field k] (M : ℕ)
    (G : ↑((affineSpaceIndexedBy k (ULift.{u, 0} (Fin M))).presheaf.obj (Opposite.op ⊤))) :
    pullbackAlongProjection k M G = (ConcreteCategory.hom (Scheme.Hom.appTop (projLeft k M 1))) G :=
  rfl

private theorem replaceLastCoord_appTop_pullbackAlongProjection (k : Type u) [Field k] (M : ℕ)
    (G : ↑((affineSpaceIndexedBy k (ULift.{u, 0} (Fin M))).presheaf.obj (Opposite.op ⊤)))
    (s : ↑((↑(pullbackBasicOpen k M G) : Scheme.{u}).presheaf.obj (Opposite.op ⊤))) :
    (ConcreteCategory.hom (Scheme.Hom.appTop (replaceLastCoord k M G s))) (pullbackAlongProjection k M G) =
      (ConcreteCategory.hom (Scheme.Hom.appTop (pullbackBasicOpen k M G).ι)) (pullbackAlongProjection k M G) := by
  rw [pullbackAlongProjection_eq, ← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop,
    ← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, replaceLastCoord_comp_projLeft]

private theorem shiftLastCoord_appTop_unitOnPullbackBasicOpen_val (k : Type u) [Field k] (M : ℕ)
    (G : ↑((affineSpaceIndexedBy k (ULift.{u, 0} (Fin M))).presheaf.obj (Opposite.op ⊤)))
    (s : ↑((↑(pullbackBasicOpen k M G) : Scheme.{u}).presheaf.obj (Opposite.op ⊤))) :
    (ConcreteCategory.hom (Scheme.Hom.appTop (shiftLastCoord k M G s))) ((unitOnPullbackBasicOpen k M G).val) =
      (unitOnPullbackBasicOpen k M G).val := by
  rw [unitOnPullbackBasicOpen_val, ← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, shiftLastCoord_comp_ι,
    replaceLastCoord_appTop_pullbackAlongProjection]

private theorem shiftLastCoord_appTop_unitOnPullbackBasicOpen_inv_val (k : Type u) [Field k] (M : ℕ)
    (G : ↑((affineSpaceIndexedBy k (ULift.{u, 0} (Fin M))).presheaf.obj (Opposite.op ⊤)))
    (s : ↑((↑(pullbackBasicOpen k M G) : Scheme.{u}).presheaf.obj (Opposite.op ⊤))) :
    (ConcreteCategory.hom (Scheme.Hom.appTop (shiftLastCoord k M G s))) (((unitOnPullbackBasicOpen k M G)⁻¹).val) =
      ((unitOnPullbackBasicOpen k M G)⁻¹).val := by
  have h1 : (ConcreteCategory.hom (Scheme.Hom.appTop (shiftLastCoord k M G s)))
      (((unitOnPullbackBasicOpen k M G)⁻¹).val) * (unitOnPullbackBasicOpen k M G).val = 1 := by
    rw [← shiftLastCoord_appTop_unitOnPullbackBasicOpen_val k M G s, ← map_mul, Units.inv_mul, map_one]
  exact (Units.inv_eq_of_mul_eq_one_left h1).symm

private theorem shiftLastCoord_comp_shiftLastCoord (k : Type u) [Field k] (M : ℕ)
    (G : ↑((affineSpaceIndexedBy k (ULift.{u, 0} (Fin M))).presheaf.obj (Opposite.op ⊤)))
    (s t : ↑((↑(pullbackBasicOpen k M G) : Scheme.{u}).presheaf.obj (Opposite.op ⊤)))
    (ht : (ConcreteCategory.hom (Scheme.Hom.appTop (shiftLastCoord k M G s))) t =
      (ConcreteCategory.hom (Scheme.Hom.appTop (pullbackBasicOpen k M G).ι)) (lastCoordinate k M)) :
    shiftLastCoord k M G s ≫ shiftLastCoord k M G t = 𝟙 _ := by
  rw [← cancel_mono (pullbackBasicOpen k M G).ι, Category.assoc, shiftLastCoord_comp_ι, Category.id_comp]
  refine AffineSpace.hom_ext ?_ ?_
  · have h1 : (shiftLastCoord k M G s ≫ replaceLastCoord k M G t) ≫
        affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin M ⊕ Fin 1)) =
        (pullbackBasicOpen k M G).ι ≫ affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin M ⊕ Fin 1)) := by
      rw [Category.assoc, replaceLastCoord_comp_affineSpaceIndexedByToSpec, ← Category.assoc, shiftLastCoord_comp_ι,
        replaceLastCoord_comp_affineSpaceIndexedByToSpec]
    exact h1
  · intro i
    obtain ⟨j⟩ := i
    cases j with
    | inl a =>
      rw [Scheme.Hom.comp_appTop, CommRingCat.comp_apply,
        ← pullbackCoord_def (replaceLastCoord k M G t)
          (⟨Sum.inl a⟩ : ULift.{u, 0} (Fin M ⊕ Fin 1)),
        pullbackCoord_replaceLastCoord_inl,
        pullbackCoord_def (pullbackBasicOpen k M G).ι (⟨Sum.inl a⟩ : ULift.{u, 0} (Fin M ⊕ Fin 1)),
        ← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, shiftLastCoord_comp_ι,
        ← pullbackCoord_def (replaceLastCoord k M G s)
          (⟨Sum.inl a⟩ : ULift.{u, 0} (Fin M ⊕ Fin 1)),
        pullbackCoord_replaceLastCoord_inl,
        pullbackCoord_def (pullbackBasicOpen k M G).ι (⟨Sum.inl a⟩ : ULift.{u, 0} (Fin M ⊕ Fin 1))]
    | inr b =>
      rw [← lastCoordinate_eq_coord k M b, Scheme.Hom.comp_appTop, CommRingCat.comp_apply,
        replaceLastCoord_appTop_lastCoordinate, ht]

private theorem isIso_shiftLastCoord_lastCoordinate_add_inv (k : Type u) [Field k] (M : ℕ)
    (G : ↑((affineSpaceIndexedBy k (ULift.{u, 0} (Fin M))).presheaf.obj (Opposite.op ⊤))) :
    IsIso (shiftLastCoord k M G
      ((ConcreteCategory.hom (Scheme.Hom.appTop (pullbackBasicOpen k M G).ι)) (lastCoordinate k M) +
        ((unitOnPullbackBasicOpen k M G)⁻¹).val)) := by
  refine ⟨⟨shiftLastCoord k M G
      ((ConcreteCategory.hom (Scheme.Hom.appTop (pullbackBasicOpen k M G).ι)) (lastCoordinate k M) -
        ((unitOnPullbackBasicOpen k M G)⁻¹).val), ?_, ?_⟩⟩
  · apply shiftLastCoord_comp_shiftLastCoord
    rw [map_sub, shiftLastCoord_appTop_unitOnPullbackBasicOpen_inv_val, ← CommRingCat.comp_apply,
      ← Scheme.Hom.comp_appTop, shiftLastCoord_comp_ι, replaceLastCoord_appTop_lastCoordinate]
    ring
  · apply shiftLastCoord_comp_shiftLastCoord
    rw [map_add, shiftLastCoord_appTop_unitOnPullbackBasicOpen_inv_val, ← CommRingCat.comp_apply,
      ← Scheme.Hom.comp_appTop, shiftLastCoord_comp_ι, replaceLastCoord_appTop_lastCoordinate]
    ring

private theorem exists_isClosedImmersion_pullbackBasicOpen (k : Type u) [Field k] (M : ℕ) {A : Scheme.{u}}
    (ρ : A ⟶ affineSpaceIndexedBy k (ULift.{u, 0} (Fin M))) [IsClosedImmersion ρ]
    (G : ↑((affineSpaceIndexedBy k (ULift.{u, 0} (Fin M))).presheaf.obj (Opposite.op ⊤)))
    (V : A.Opens)
    (hV : V = (Opens.map (ρ ≫ affineSpaceInl k M 1).base).obj (pullbackBasicOpen k M G)) :
    ∃ e : (↑V : Scheme.{u}) ⟶ (↑(pullbackBasicOpen k M G) : Scheme.{u}),
      IsClosedImmersion e ∧
      e ≫ (pullbackBasicOpen k M G).ι ≫ projLeft k M 1 = V.ι ≫ ρ ∧
      (ConcreteCategory.hom (Scheme.Hom.appTop (e ≫ (pullbackBasicOpen k M G).ι)))
          (lastCoordinate k M * pullbackAlongProjection k M G) = 1 := by
  subst hV
  have hci : IsClosedImmersion ((ρ ≫ affineSpaceInl k M 1) ∣_ pullbackBasicOpen k M G) := by
    have hco : IsClosedImmersion (ρ ≫ affineSpaceInl k M 1) := inferInstance
    infer_instance
  have hiso := isIso_shiftLastCoord_lastCoordinate_add_inv k M G
  refine ⟨((ρ ≫ affineSpaceInl k M 1) ∣_ pullbackBasicOpen k M G) ≫
      shiftLastCoord k M G ((ConcreteCategory.hom (Scheme.Hom.appTop (pullbackBasicOpen k M G).ι))
        (lastCoordinate k M) + ((unitOnPullbackBasicOpen k M G)⁻¹).val), ?_, ?_, ?_⟩
  · exact (MorphismProperty.cancel_right_of_respectsIso (P := @IsClosedImmersion) _ _).mpr hci
  · rw [Category.assoc, shiftLastCoord_comp_ι_assoc, replaceLastCoord_comp_projLeft, ← Category.assoc,
      morphismRestrict_ι, Category.assoc, Category.assoc, affineSpaceInl_comp_projLeft,
      Category.comp_id]
  · have h0 : (ConcreteCategory.hom (Scheme.Hom.appTop
        ((ρ ≫ affineSpaceInl k M 1) ∣_ pullbackBasicOpen k M G)))
        ((ConcreteCategory.hom (Scheme.Hom.appTop (pullbackBasicOpen k M G).ι)) (lastCoordinate k M)) = 0 := by
      rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, morphismRestrict_ι,
        ← Category.assoc]
      exact lastCoordinate_appTop_comp_affineSpaceInl k M _
    rw [Category.assoc, shiftLastCoord_comp_ι, Scheme.Hom.comp_appTop, CommRingCat.comp_apply, map_mul,
      replaceLastCoord_appTop_lastCoordinate, replaceLastCoord_appTop_pullbackAlongProjection, ← unitOnPullbackBasicOpen_val, map_mul,
      map_add, h0, zero_add, ← map_mul, Units.inv_mul, map_one]

private theorem exists_isClosedImmersion_basicOpen_pullbackBasicOpen (k : Type u) [Field k] (M : ℕ) {A : Scheme.{u}}
    (ρ : A ⟶ affineSpaceIndexedBy k (ULift.{u, 0} (Fin M))) [IsClosedImmersion ρ]
    (F : ↑(A.presheaf.obj (Opposite.op ⊤))) :
    ∃ e : (↑(A.basicOpen F) : Scheme.{u}) ⟶
        (↑(pullbackBasicOpen k M (globalSectionLift k M ρ F)) : Scheme.{u}),
      IsClosedImmersion e ∧
      e ≫ (pullbackBasicOpen k M (globalSectionLift k M ρ F)).ι ≫ projLeft k M 1 = (A.basicOpen F).ι ≫ ρ ∧
      (ConcreteCategory.hom
          (Scheme.Hom.appTop (e ≫ (pullbackBasicOpen k M (globalSectionLift k M ρ F)).ι)))
          (lastCoordinate k M * pullbackAlongProjection k M (globalSectionLift k M ρ F)) = 1 := by
  refine exists_isClosedImmersion_pullbackBasicOpen k M ρ (globalSectionLift k M ρ F) (A.basicOpen F) ?_
  have hF : (ConcreteCategory.hom (Scheme.Hom.appTop (ρ ≫ affineSpaceInl k M 1)))
      (pullbackAlongProjection k M (globalSectionLift k M ρ F)) = F := by
    rw [pullbackAlongProjection_eq, ← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, Category.assoc,
      affineSpaceInl_comp_projLeft, Category.comp_id, appTop_globalSectionLift]
  exact (congrArg (fun r : ↑(A.presheaf.obj (Opposite.op ⊤)) => A.basicOpen r) hF).symm.trans
    (Scheme.preimage_basicOpen (ρ ≫ affineSpaceInl k M 1)
      (pullbackAlongProjection k M (globalSectionLift k M ρ F))).symm

def basicOpenToPullbackBasicOpen (k : Type u) [Field k] (M : ℕ) {A : Scheme.{u}}
    (ρ : A ⟶ affineSpaceIndexedBy k (ULift.{u, 0} (Fin M))) [IsClosedImmersion ρ]
    (F : ↑(A.presheaf.obj (Opposite.op ⊤))) :
    (↑(A.basicOpen F) : Scheme.{u}) ⟶ (↑(pullbackBasicOpen k M (globalSectionLift k M ρ F)) : Scheme.{u}) :=
  (exists_isClosedImmersion_basicOpen_pullbackBasicOpen k M ρ F).choose

theorem isClosedImmersion_basicOpenToPullbackBasicOpen (k : Type u) [Field k] (M : ℕ) {A : Scheme.{u}}
    (ρ : A ⟶ affineSpaceIndexedBy k (ULift.{u, 0} (Fin M))) [IsClosedImmersion ρ]
    (F : ↑(A.presheaf.obj (Opposite.op ⊤))) :
    IsClosedImmersion (basicOpenToPullbackBasicOpen k M ρ F) :=
  (exists_isClosedImmersion_basicOpen_pullbackBasicOpen k M ρ F).choose_spec.1

instance instIsClosedImmersionPadLocalEmb (k : Type u) [Field k] (M : ℕ) {A : Scheme.{u}}
    (ρ : A ⟶ affineSpaceIndexedBy k (ULift.{u, 0} (Fin M))) [IsClosedImmersion ρ]
    (F : ↑(A.presheaf.obj (Opposite.op ⊤))) :
    IsClosedImmersion (basicOpenToPullbackBasicOpen k M ρ F) :=
  isClosedImmersion_basicOpenToPullbackBasicOpen k M ρ F

theorem basicOpenToPullbackBasicOpen_comp_projLeft (k : Type u) [Field k] (M : ℕ) {A : Scheme.{u}}
    (ρ : A ⟶ affineSpaceIndexedBy k (ULift.{u, 0} (Fin M))) [IsClosedImmersion ρ]
    (F : ↑(A.presheaf.obj (Opposite.op ⊤))) :
    basicOpenToPullbackBasicOpen k M ρ F ≫ (pullbackBasicOpen k M (globalSectionLift k M ρ F)).ι ≫ projLeft k M 1 =
      (A.basicOpen F).ι ≫ ρ :=
  (exists_isClosedImmersion_basicOpen_pullbackBasicOpen k M ρ F).choose_spec.2.1

def basicOpenEmbedding (k : Type u) [Field k] (M : ℕ) {A : Scheme.{u}}
    (ρ : A ⟶ affineSpaceIndexedBy k (ULift.{u, 0} (Fin M))) [IsClosedImmersion ρ]
    (F : ↑(A.presheaf.obj (Opposite.op ⊤))) :
    (↑(A.basicOpen F) : Scheme.{u}) ⟶ affineSpaceTimesLine k M :=
  basicOpenToPullbackBasicOpen k M ρ F ≫ (pullbackBasicOpen k M (globalSectionLift k M ρ F)).ι

theorem appTop_basicOpenEmbedding_lastCoordinate_mul (k : Type u) [Field k] (M : ℕ) {A : Scheme.{u}}
    (ρ : A ⟶ affineSpaceIndexedBy k (ULift.{u, 0} (Fin M))) [IsClosedImmersion ρ]
    (F : ↑(A.presheaf.obj (Opposite.op ⊤))) :
    (ConcreteCategory.hom (Scheme.Hom.appTop (basicOpenEmbedding k M ρ F)))
        (lastCoordinate k M * pullbackAlongProjection k M (globalSectionLift k M ρ F)) = 1 :=
  (exists_isClosedImmersion_basicOpen_pullbackBasicOpen k M ρ F).choose_spec.2.2

private theorem isUnit_map_of_not_isUnit_map_mul_sub_one {R S : Type u} [CommRing R] [CommRing S]
    [IsLocalRing S] (φ : R →+* S) (a b : R) (h : ¬ IsUnit (φ (a * b - 1))) : IsUnit (φ b) := by
  rw [map_sub, map_mul, map_one] at h
  rcases IsLocalRing.isUnit_or_isUnit_one_sub_self (φ a * φ b) with h1 | h1
  · exact isUnit_of_mul_isUnit_right h1
  · refine absurd ?_ h
    have h2 := h1.neg
    rwa [neg_sub] at h2

private theorem false_of_isUnit_map_zero {R S : Type u} [CommRing R] [CommRing S]
    [Nontrivial S] (φ : R →+* S) (h : IsUnit (φ (0 : R))) : False := by
  rw [map_zero] at h
  exact not_isUnit_zero h

private theorem isClosed_image_of_isInducing {X Y : Type u} [TopologicalSpace X]
    [TopologicalSpace Y] (g : Y → X) (hg : Topology.IsInducing g) (S : Set X) (C : Set Y)
    (hSimage : S = g '' C) (hC : IsClosed C) (W : Set X) (hW : IsClosed W) (h1 : S ⊆ W)
    (h2 : W ⊆ Set.range g) :
    IsClosed S := by
  obtain ⟨D, hD, hpreimage⟩ := hg.isClosed_iff.1 hC
  have himg : g '' C = D ∩ Set.range g := by
    rw [← hpreimage, Set.image_preimage_eq_inter_range]
  have hEq : S = D ∩ W := by
    refine Set.Subset.antisymm (Set.subset_inter ?_ h1) ?_
    · rw [hSimage, himg]
      exact fun x hx => hx.1
    · intro x hx
      rw [hSimage, himg]
      exact ⟨hx.1, h2 hx.2⟩
  rw [hEq]
  exact hD.inter hW

theorem isClosedImmersion_basicOpenEmbedding (k : Type u) [Field k] (M : ℕ) {A : Scheme.{u}}
    (ρ : A ⟶ affineSpaceIndexedBy k (ULift.{u, 0} (Fin M))) [IsClosedImmersion ρ]
    (F : ↑(A.presheaf.obj (Opposite.op ⊤))) :
    IsClosedImmersion (basicOpenEmbedding k M ρ F) := by
  have hpre : IsPreimmersion (basicOpenEmbedding k M ρ F) := by
    show IsPreimmersion (basicOpenToPullbackBasicOpen k M ρ F ≫ (pullbackBasicOpen k M (globalSectionLift k M ρ F)).ι)
    infer_instance
  have h0 : (ConcreteCategory.hom (Scheme.Hom.appTop (basicOpenEmbedding k M ρ F)))
      (lastCoordinate k M * pullbackAlongProjection k M (globalSectionLift k M ρ F) - 1) = 0 := by
    rw [map_sub, map_one, appTop_basicOpenEmbedding_lastCoordinate_mul, sub_self]
  have hind : Topology.IsInducing (pullbackBasicOpen k M (globalSectionLift k M ρ F)).ι.base :=
    (pullbackBasicOpen k M (globalSectionLift k M ρ F)).ι.isOpenEmbedding.toIsEmbedding.toIsInducing
  have hC : IsClosed (Set.range (basicOpenToPullbackBasicOpen k M ρ F).base) :=
    (Scheme.Hom.isClosedEmbedding (basicOpenToPullbackBasicOpen k M ρ F)).isClosed_range
  have heq : Set.range (basicOpenEmbedding k M ρ F).base =
      (pullbackBasicOpen k M (globalSectionLift k M ρ F)).ι.base '' Set.range (basicOpenToPullbackBasicOpen k M ρ F).base := by
    ext z
    constructor
    · rintro ⟨y, rfl⟩
      exact ⟨(basicOpenToPullbackBasicOpen k M ρ F).base y, ⟨y, rfl⟩, rfl⟩
    · rintro ⟨w, ⟨y, rfl⟩, rfl⟩
      exact ⟨y, rfl⟩
  have hW : IsClosed ((((affineSpaceTimesLine k M).basicOpen
      (lastCoordinate k M * pullbackAlongProjection k M (globalSectionLift k M ρ F) - 1) : (affineSpaceTimesLine k M).Opens) :
        Set ↥(affineSpaceTimesLine k M))ᶜ) :=
    ((affineSpaceTimesLine k M).basicOpen
      (lastCoordinate k M * pullbackAlongProjection k M (globalSectionLift k M ρ F) - 1)).isOpen.isClosed_compl
  have h1 : Set.range (basicOpenEmbedding k M ρ F).base ⊆
      ((((affineSpaceTimesLine k M).basicOpen
        (lastCoordinate k M * pullbackAlongProjection k M (globalSectionLift k M ρ F) - 1) : (affineSpaceTimesLine k M).Opens) :
          Set ↥(affineSpaceTimesLine k M))ᶜ) := by
    rintro z ⟨y, rfl⟩
    intro hz
    have hz' : y ∈ (basicOpenEmbedding k M ρ F) ⁻¹ᵁ ((affineSpaceTimesLine k M).basicOpen
        (lastCoordinate k M * pullbackAlongProjection k M (globalSectionLift k M ρ F) - 1)) := hz
    rw [Scheme.preimage_basicOpen] at hz'
    have hy : y ∈ (↑(A.basicOpen F) : Scheme.{u}).basicOpen
        ((ConcreteCategory.hom (Scheme.Hom.appTop (basicOpenEmbedding k M ρ F)))
          (lastCoordinate k M * pullbackAlongProjection k M (globalSectionLift k M ρ F) - 1)) := hz'
    rw [h0] at hy
    exact false_of_isUnit_map_zero _
      (((↑(A.basicOpen F) : Scheme.{u}).mem_basicOpen _ y (Opens.mem_top y)).mp hy)
  have h2 : ((((affineSpaceTimesLine k M).basicOpen
      (lastCoordinate k M * pullbackAlongProjection k M (globalSectionLift k M ρ F) - 1) : (affineSpaceTimesLine k M).Opens) :
        Set ↥(affineSpaceTimesLine k M))ᶜ) ⊆ Set.range (pullbackBasicOpen k M (globalSectionLift k M ρ F)).ι.base := by
    intro x hx
    have hx' : x ∉ (affineSpaceTimesLine k M).basicOpen
        (lastCoordinate k M * pullbackAlongProjection k M (globalSectionLift k M ρ F) - 1) := hx
    rw [(affineSpaceTimesLine k M).mem_basicOpen _ x (Opens.mem_top x)] at hx'
    have hmem : x ∈ (affineSpaceTimesLine k M).basicOpen (pullbackAlongProjection k M (globalSectionLift k M ρ F)) := by
      rw [(affineSpaceTimesLine k M).mem_basicOpen _ x (Opens.mem_top x)]
      exact isUnit_map_of_not_isUnit_map_mul_sub_one _ (lastCoordinate k M)
        (pullbackAlongProjection k M (globalSectionLift k M ρ F)) hx'
    rw [Scheme.Opens.range_ι]
    exact hmem
  apply IsClosedImmersion.of_isPreimmersion
  exact isClosed_image_of_isInducing _ hind _ _ heq hC _ hW h1 h2

instance instIsClosedImmersionLocalizationEmb (k : Type u) [Field k] (M : ℕ) {A : Scheme.{u}}
    (ρ : A ⟶ affineSpaceIndexedBy k (ULift.{u, 0} (Fin M))) [IsClosedImmersion ρ]
    (F : ↑(A.presheaf.obj (Opposite.op ⊤))) :
    IsClosedImmersion (basicOpenEmbedding k M ρ F) :=
  isClosedImmersion_basicOpenEmbedding k M ρ F

theorem basicOpenEmbedding_comp_affineSpaceIndexedByToSpec (k : Type u) [Field k] (M : ℕ) {A : Scheme.{u}}
    (ρ : A ⟶ affineSpaceIndexedBy k (ULift.{u, 0} (Fin M))) [IsClosedImmersion ρ]
    (F : ↑(A.presheaf.obj (Opposite.op ⊤))) (p : A ⟶ Spec (CommRingCat.of k))
    (hp : ρ ≫ affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin M)) = p) :
    basicOpenEmbedding k M ρ F ≫ affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin M ⊕ Fin 1)) =
      (A.basicOpen F).ι ≫ p := by
  have h1 := basicOpenToPullbackBasicOpen_comp_projLeft k M ρ F
  have h2 : basicOpenToPullbackBasicOpen k M ρ F ≫ (pullbackBasicOpen k M (globalSectionLift k M ρ F)).ι ≫ projLeft k M 1 ≫
        affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin M)) =
      (A.basicOpen F).ι ≫ ρ ≫ affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin M)) := by
    rw [← Category.assoc ((pullbackBasicOpen k M (globalSectionLift k M ρ F)).ι) (projLeft k M 1),
      ← Category.assoc (basicOpenToPullbackBasicOpen k M ρ F), h1, Category.assoc]
  show (basicOpenToPullbackBasicOpen k M ρ F ≫ (pullbackBasicOpen k M (globalSectionLift k M ρ F)).ι) ≫
      affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin M ⊕ Fin 1)) = (A.basicOpen F).ι ≫ p
  rw [Category.assoc, ← projLeft_comp_affineSpaceIndexedByToSpec k M 1, h2, hp]

private theorem hasSmoothCoordCodim_comp_opens_ι {k : Type u} [Field k] {X Y : Scheme.{u}}
    (s : Y ⟶ Spec (CommRingCat.of k)) (O : Y.Opens) (g : X ⟶ (↑O : Scheme.{u})) {c : ℕ}
    (hcg : IsClosedImmersion g) (hcgo : IsClosedImmersion (g ≫ O.ι))
    (h : HasSmoothCoordCodim (O.ι ≫ s) g c) :
    HasSmoothCoordCodim s (g ≫ O.ι) c := by
  have := hcg
  have := hcgo
  rw [hasSmoothCoordCodim_iff]
  intro x
  obtain ⟨U, hxU, q, hq, hqs, hideal⟩ := (hasSmoothCoordCodim_iff (O.ι ≫ s) g c).1 h x
  obtain ⟨W, ψ, hψiso, hψ, hmem⟩ :
      ∃ (W : Y.Opens) (ψ : (↑W : Scheme.{u}) ⟶ (↑U : Scheme.{u})),
        IsIso ψ ∧ ψ ≫ (U.ι ≫ O.ι) = W.ι ∧ (g ≫ O.ι).base x ∈ W := by
    have hrange : Set.range (U.ι ≫ O.ι).base =
        Set.range (Scheme.Hom.opensRange (U.ι ≫ O.ι)).ι.base := by
      rw [Scheme.Opens.range_ι]
      rfl
    refine ⟨Scheme.Hom.opensRange (U.ι ≫ O.ι),
      (IsOpenImmersion.isoOfRangeEq (U.ι ≫ O.ι)
        (Scheme.Hom.opensRange (U.ι ≫ O.ι)).ι hrange).inv, inferInstance,
      IsOpenImmersion.isoOfRangeEq_inv_fac _ _ hrange, ?_⟩
    have hxr : g.base x ∈ Set.range U.ι.base := by
      rw [Scheme.Opens.range_ι]
      exact hxU
    obtain ⟨y, hy⟩ := hxr
    exact ⟨y, congrArg (⇑O.ι) hy⟩
  have := hψiso
  refine ⟨W, hmem, ψ ≫ q, ?_, ?_, ?_⟩
  · have : Smooth q := hq
    infer_instance
  · rw [Category.assoc, hqs, ← hψ]
    simp only [Category.assoc]
  · rw [restrictIdeal_eq_comap_ι] at hideal
    rw [restrictIdeal_eq_comap_ι, ← hψ, Scheme.IdealSheafData.comap_comp,
      Scheme.IdealSheafData.comap_comp, Blowup.comap_ker_comp_of_isOpenImmersion g O.ι, hideal,
      Scheme.IdealSheafData.comap_comp]

private noncomputable def lastCoordinateAddInvUnit (k : Type u) [Field k] (M : ℕ)
    (G : ↑((affineSpaceIndexedBy k (ULift.{u, 0} (Fin M))).presheaf.obj (Opposite.op ⊤))) :
    ↑((↑(pullbackBasicOpen k M G) : Scheme.{u}).presheaf.obj (Opposite.op ⊤)) :=
  (ConcreteCategory.hom (Scheme.Hom.appTop (pullbackBasicOpen k M G).ι)) (lastCoordinate k M) +
    ((unitOnPullbackBasicOpen k M G)⁻¹).val

private theorem shiftLastCoordSection_eq (k : Type u) [Field k] (M : ℕ)
    (G : ↑((affineSpaceIndexedBy k (ULift.{u, 0} (Fin M))).presheaf.obj (Opposite.op ⊤))) :
    lastCoordinateAddInvUnit k M G =
      (ConcreteCategory.hom (Scheme.Hom.appTop (pullbackBasicOpen k M G).ι)) (lastCoordinate k M) +
        ((unitOnPullbackBasicOpen k M G)⁻¹).val :=
  rfl

private theorem isIso_shiftLastCoord_shiftLastCoordSection (k : Type u) [Field k] (M : ℕ)
    (G : ↑((affineSpaceIndexedBy k (ULift.{u, 0} (Fin M))).presheaf.obj (Opposite.op ⊤))) :
    IsIso (shiftLastCoord k M G (lastCoordinateAddInvUnit k M G)) :=
  isIso_shiftLastCoord_lastCoordinate_add_inv k M G

private theorem hasSmoothCoordCodim_comp_pullbackBasicOpen_ι (hsm : AffineSpaceIsSmooth.{u}) (k : Type u)
    [Field k] (M c : ℕ) {A : Scheme.{u}} (ρ : A ⟶ affineSpaceIndexedBy k (ULift.{u, 0} (Fin M)))
    [IsClosedImmersion ρ]
    (G : ↑((affineSpaceIndexedBy k (ULift.{u, 0} (Fin M))).presheaf.obj (Opposite.op ⊤)))
    (V : A.Opens)
    (hV : V = (Opens.map (ρ ≫ affineSpaceInl k M 1).base).obj (pullbackBasicOpen k M G))
    (e : (↑V : Scheme.{u}) ⟶ (↑(pullbackBasicOpen k M G) : Scheme.{u}))
    (hce : IsClosedImmersion e)
    (hceo : IsClosedImmersion (e ≫ (pullbackBasicOpen k M G).ι))
    (hproj : e ≫ (pullbackBasicOpen k M G).ι ≫ projLeft k M 1 = V.ι ≫ ρ)
    (hrel : (ConcreteCategory.hom (Scheme.Hom.appTop (e ≫ (pullbackBasicOpen k M G).ι)))
      (lastCoordinate k M * pullbackAlongProjection k M G) = 1)
    (h : HasSmoothCoordCodim (affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin M))) ρ c) :
    HasSmoothCoordCodim (affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin M ⊕ Fin 1)))
      (e ≫ (pullbackBasicOpen k M G).ι) (c + 1) := by
  subst hV
  have := hce
  have : IsIso (shiftLastCoord k M G (lastCoordinateAddInvUnit k M G)) := isIso_shiftLastCoord_shiftLastCoordSection k M G
  have hE : ((ρ ≫ affineSpaceInl k M 1) ∣_ pullbackBasicOpen k M G) ≫
      (asIso (shiftLastCoord k M G (lastCoordinateAddInvUnit k M G))).hom = e := by
    show ((ρ ≫ affineSpaceInl k M 1) ∣_ pullbackBasicOpen k M G) ≫ shiftLastCoord k M G (lastCoordinateAddInvUnit k M G) = e
    rw [← cancel_mono (pullbackBasicOpen k M G).ι, Category.assoc, shiftLastCoord_comp_ι]
    have hstr : (e ≫ (pullbackBasicOpen k M G).ι) ≫
          affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin M ⊕ Fin 1)) =
        (((ρ ≫ affineSpaceInl k M 1) ∣_ pullbackBasicOpen k M G) ≫
            replaceLastCoord k M G (lastCoordinateAddInvUnit k M G)) ≫
          affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin M ⊕ Fin 1)) := by
      rw [Category.assoc, Category.assoc, replaceLastCoord_comp_affineSpaceIndexedByToSpec,
        ← Category.assoc ((ρ ≫ affineSpaceInl k M 1) ∣_ pullbackBasicOpen k M G), morphismRestrict_ι,
        ← projLeft_comp_affineSpaceIndexedByToSpec k M 1, ← Category.assoc (pullbackBasicOpen k M G).ι, ← Category.assoc e, hproj]
      simp only [Category.assoc]
      rw [affineSpaceInl_comp_projLeft_assoc]
    refine AffineSpace.hom_ext ?_ ?_
    · exact hstr.symm
    · intro i
      obtain ⟨j⟩ := i
      cases j with
      | inl a =>
        have hl : (ConcreteCategory.hom (Scheme.Hom.appTop (e ≫ (pullbackBasicOpen k M G).ι)))
              (AffineSpace.coord (Spec (CommRingCat.of k))
                (⟨Sum.inl a⟩ : ULift.{u, 0} (Fin M ⊕ Fin 1))) =
            (ConcreteCategory.hom (Scheme.Hom.appTop
              (e ≫ (pullbackBasicOpen k M G).ι ≫ projLeft k M 1)))
              (AffineSpace.coord (Spec (CommRingCat.of k)) (⟨a⟩ : ULift.{u, 0} (Fin M))) := by
          rw [← projLeft_appTop_coord k M 1 a, ← CommRingCat.comp_apply,
            ← Scheme.Hom.comp_appTop, Category.assoc]
        have hr : (ConcreteCategory.hom (Scheme.Hom.appTop
              (((ρ ≫ affineSpaceInl k M 1) ∣_ pullbackBasicOpen k M G) ≫
                replaceLastCoord k M G (lastCoordinateAddInvUnit k M G))))
              (AffineSpace.coord (Spec (CommRingCat.of k))
                (⟨Sum.inl a⟩ : ULift.{u, 0} (Fin M ⊕ Fin 1))) =
            (ConcreteCategory.hom (Scheme.Hom.appTop
              (e ≫ (pullbackBasicOpen k M G).ι ≫ projLeft k M 1)))
              (AffineSpace.coord (Spec (CommRingCat.of k)) (⟨a⟩ : ULift.{u, 0} (Fin M))) := by
          rw [hproj, Scheme.Hom.comp_appTop, CommRingCat.comp_apply,
            ← pullbackCoord_def (replaceLastCoord k M G (lastCoordinateAddInvUnit k M G))
              (⟨Sum.inl a⟩ : ULift.{u, 0} (Fin M ⊕ Fin 1)),
            pullbackCoord_replaceLastCoord_inl, pullbackCoord_def, ← CommRingCat.comp_apply,
            ← Scheme.Hom.comp_appTop, morphismRestrict_ι, ← Category.assoc,
            Scheme.Hom.comp_appTop, CommRingCat.comp_apply,
            ← pullbackCoord_def (affineSpaceInl k M 1)
              (⟨Sum.inl a⟩ : ULift.{u, 0} (Fin M ⊕ Fin 1)),
            pullbackCoord_affineSpaceInl_inl]
        exact hr.trans hl.symm
      | inr b =>
        have hu : (ConcreteCategory.hom (Scheme.Hom.appTop (e ≫ (pullbackBasicOpen k M G).ι)))
              (lastCoordinate k M) *
            (ConcreteCategory.hom (Scheme.Hom.appTop (e ≫ (pullbackBasicOpen k M G).ι)))
              (pullbackAlongProjection k M G) = 1 := by
          rw [← map_mul]
          exact hrel
        have hX : (ConcreteCategory.hom (Scheme.Hom.appTop (e ≫ (pullbackBasicOpen k M G).ι)))
              (pullbackAlongProjection k M G) =
            (ConcreteCategory.hom (Scheme.Hom.appTop
              ((ρ ≫ affineSpaceInl k M 1) ∣_ pullbackBasicOpen k M G))) ((unitOnPullbackBasicOpen k M G).val) := by
          rw [unitOnPullbackBasicOpen_val, ← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop,
            morphismRestrict_ι, pullbackAlongProjection_eq, ← CommRingCat.comp_apply,
            ← Scheme.Hom.comp_appTop, ← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop,
            Category.assoc, Category.assoc, Category.assoc, affineSpaceInl_comp_projLeft,
            Category.comp_id, hproj]
        have hw : (ConcreteCategory.hom (Scheme.Hom.appTop
              ((ρ ≫ affineSpaceInl k M 1) ∣_ pullbackBasicOpen k M G))) (((unitOnPullbackBasicOpen k M G)⁻¹).val) *
            (ConcreteCategory.hom (Scheme.Hom.appTop
              ((ρ ≫ affineSpaceInl k M 1) ∣_ pullbackBasicOpen k M G))) ((unitOnPullbackBasicOpen k M G).val) = 1 := by
          rw [← map_mul, Units.inv_mul, map_one]
        have hRP : (ConcreteCategory.hom (Scheme.Hom.appTop
              (((ρ ≫ affineSpaceInl k M 1) ∣_ pullbackBasicOpen k M G) ≫
                replaceLastCoord k M G (lastCoordinateAddInvUnit k M G)))) (lastCoordinate k M) =
            (ConcreteCategory.hom (Scheme.Hom.appTop
              ((ρ ≫ affineSpaceInl k M 1) ∣_ pullbackBasicOpen k M G))) (((unitOnPullbackBasicOpen k M G)⁻¹).val) := by
          rw [Scheme.Hom.comp_appTop, CommRingCat.comp_apply, replaceLastCoord_appTop_lastCoordinate,
            shiftLastCoordSection_eq, map_add, ← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop,
            morphismRestrict_ι, ← Category.assoc, lastCoordinate_appTop_comp_affineSpaceInl, zero_add]
        rw [hX] at hu
        rw [← lastCoordinate_eq_coord k M b, hRP]
        exact (inv_unique ((mul_comm _ _).trans hu) ((mul_comm _ _).trans hw)).symm
  have H1 : HasSmoothCoordCodim (affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin M ⊕ Fin 1)))
      (ρ ≫ affineSpaceInl k M 1) (c + 1) := HasSmoothCoordCodim.comp_affineSpaceInl hsm k ρ 1 h
  have H2 := H1.resLE_open (pullbackBasicOpen k M G)
  have hres : Scheme.Hom.resLE (ρ ≫ affineSpaceInl k M 1) (pullbackBasicOpen k M G)
      ((Opens.map (ρ ≫ affineSpaceInl k M 1).base).obj (pullbackBasicOpen k M G)) le_rfl =
      ((ρ ≫ affineSpaceInl k M 1) ∣_ pullbackBasicOpen k M G) := by
    rw [← cancel_mono (pullbackBasicOpen k M G).ι, Scheme.Hom.resLE_comp_ι, morphismRestrict_ι]
  rw [hres] at H2
  have hφ : (asIso (shiftLastCoord k M G (lastCoordinateAddInvUnit k M G))).hom ≫
        ((pullbackBasicOpen k M G).ι ≫ affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin M ⊕ Fin 1))) =
      (pullbackBasicOpen k M G).ι ≫ affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin M ⊕ Fin 1)) := by
    show shiftLastCoord k M G (lastCoordinateAddInvUnit k M G) ≫
        ((pullbackBasicOpen k M G).ι ≫ affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin M ⊕ Fin 1))) = _
    rw [shiftLastCoord_comp_ι_assoc, replaceLastCoord_comp_affineSpaceIndexedByToSpec]
  have H3 := H2.comp_iso_hom (asIso (shiftLastCoord k M G (lastCoordinateAddInvUnit k M G)))
    ((pullbackBasicOpen k M G).ι ≫ affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin M ⊕ Fin 1))) hφ
  rw [hE] at H3
  exact hasSmoothCoordCodim_comp_opens_ι (affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin M ⊕ Fin 1)))
    (pullbackBasicOpen k M G) e hce hceo H3

theorem hasSmoothCoordCodim_basicOpenEmbedding (hsm : AffineSpaceIsSmooth.{u}) (k : Type u) [Field k]
    (M c : ℕ) {A : Scheme.{u}} (ρ : A ⟶ affineSpaceIndexedBy k (ULift.{u, 0} (Fin M)))
    [IsClosedImmersion ρ] (F : ↑(A.presheaf.obj (Opposite.op ⊤)))
    (h : HasSmoothCoordCodim (affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin M))) ρ c) :
    HasSmoothCoordCodim (affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin (M + 1))))
      (basicOpenEmbedding k M ρ F ≫
        (affineSpaceIsoOfEquiv (uliftFinSumEquiv.{u} M 1) (Spec (CommRingCat.of k))).hom) (c + 1) := by
  have hF : (ConcreteCategory.hom (Scheme.Hom.appTop (ρ ≫ affineSpaceInl k M 1)))
      (pullbackAlongProjection k M (globalSectionLift k M ρ F)) = F := by
    rw [pullbackAlongProjection_eq, ← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, Category.assoc,
      affineSpaceInl_comp_projLeft, Category.comp_id, appTop_globalSectionLift]
  have hV : A.basicOpen F =
      (Opens.map (ρ ≫ affineSpaceInl k M 1).base).obj (pullbackBasicOpen k M (globalSectionLift k M ρ F)) :=
    (congrArg (fun r : ↑(A.presheaf.obj (Opposite.op ⊤)) => A.basicOpen r) hF).symm.trans
      (Scheme.preimage_basicOpen (ρ ≫ affineSpaceInl k M 1)
        (pullbackAlongProjection k M (globalSectionLift k M ρ F))).symm
  have key : HasSmoothCoordCodim (affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin M ⊕ Fin 1)))
      (basicOpenEmbedding k M ρ F) (c + 1) :=
    hasSmoothCoordCodim_comp_pullbackBasicOpen_ι hsm k M c ρ (globalSectionLift k M ρ F) (A.basicOpen F) hV
      (basicOpenToPullbackBasicOpen k M ρ F)
      (isClosedImmersion_basicOpenToPullbackBasicOpen k M ρ F) (isClosedImmersion_basicOpenEmbedding k M ρ F)
      (basicOpenToPullbackBasicOpen_comp_projLeft k M ρ F) (appTop_basicOpenEmbedding_lastCoordinate_mul k M ρ F) h
  exact key.comp_iso_hom (affineSpaceIsoOfEquiv (uliftFinSumEquiv.{u} M 1) (Spec (CommRingCat.of k)))
    (affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin (M + 1))))
    (affineSpaceIsoOfEquiv_hom_comp_toSpec k (uliftFinSumEquiv.{u} M 1))

end FunctorialResolution.EmbeddedResolution

end
