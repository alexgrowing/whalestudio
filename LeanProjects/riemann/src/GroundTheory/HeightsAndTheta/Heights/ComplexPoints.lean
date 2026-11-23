import Mathlib
import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProjectiveCohomology.TwistingSheaf
import GroundTheory.HeightsAndTheta.Heights.ComplexProjective
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open AlgebraicGeometry CategoryTheory MvPolynomial GroundTheory.Arith.SchemeCoh
open scoped LinearAlgebra.Projectivization

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

noncomputable section

structure ProjScheme (A : Type u) [CommRing A] (N : ℕ) where

  X : Scheme.{u}

  ι : X ⟶ projectiveSpace A N

  isClosedImmersion : IsClosedImmersion ι

attribute [instance] ProjScheme.isClosedImmersion

namespace ProjScheme

variable {A : Type u} [CommRing A] {N : ℕ}

def self (A : Type u) [CommRing A] (N : ℕ) : ProjScheme A N where
  X := projectiveSpace A N
  ι := 𝟙 _
  isClosedImmersion := inferInstance

variable (X : ProjScheme A N)

def ideal : HomogeneousIdeal (ProjSpace.grading A N) :=
  ProjectiveSpectrum.vanishingIdeal (Set.range X.ι.base)

lemma isClosed_range : IsClosed (Set.range X.ι.base) :=
  X.ι.isClosedEmbedding.isClosed_range

def complexPoints (ρ : A →+* ℂ) : Set (CP N) :=
  {v | projPoint ρ v ∈ Set.range X.ι.base}

lemma le_of_homogeneous (I : HomogeneousIdeal (ProjSpace.grading A N)) (x : projectiveSpace A N)
    (h : ∀ d, ∀ f ∈ ProjSpace.grading A N d, f ∈ I → f ∈ x.asHomogeneousIdeal) :
    (I : Set (MvPolynomial (Fin (N + 1)) A)) ⊆ x.asHomogeneousIdeal := by
  classical
  intro f hf
  rw [← DirectSum.sum_support_decompose (ProjSpace.grading A N) f]
  refine Ideal.sum_mem _ fun d _ => ?_
  exact h d _ (SetLike.coe_mem _) (I.isHomogeneous d hf)

theorem mem_complexPoints_iff (ρ : A →+* ℂ) (v : CP N) :
    v ∈ X.complexPoints ρ ↔ ∀ d, ∀ f ∈ ProjSpace.grading A N d, f ∈ X.ideal →
      f ∈ (projPoint ρ v).asHomogeneousIdeal := by
  have e : (Set.range X.ι.base : Set (ProjectiveSpectrum (ProjSpace.grading A N))) =
      ProjectiveSpectrum.zeroLocus _ (X.ideal : Set (MvPolynomial (Fin (N + 1)) A)) := by
    rw [ideal, ProjectiveSpectrum.zeroLocus_vanishingIdeal_eq_closure]
    exact X.isClosed_range.closure_eq.symm
  change projPoint ρ v ∈ (Set.range X.ι.base : Set (ProjectiveSpectrum (ProjSpace.grading A N))) ↔ _
  rw [e]
  change (X.ideal : Set (MvPolynomial (Fin (N + 1)) A)) ⊆ (projPoint ρ v).asHomogeneousIdeal ↔ _
  constructor
  · intro h d f _ hf
    exact h hf
  · intro h
    exact le_of_homogeneous _ _ h

theorem mk_mem_complexPoints_iff (ρ : A →+* ℂ) (w : Fin (N + 1) → ℂ) (hw : w ≠ 0) :
    Projectivization.mk ℂ w hw ∈ X.complexPoints ρ ↔
      ∀ d, ∀ f ∈ ProjSpace.grading A N d, f ∈ X.ideal → evalAt ρ w f = 0 := by
  rw [mem_complexPoints_iff]
  exact forall_congr' fun d => forall₂_congr fun f hf => imp_congr_right fun _ =>
    mem_projPoint ρ w hw hf

theorem isClosed_complexPoints (ρ : A →+* ℂ) : IsClosed (X.complexPoints ρ) := by
  have : X.complexPoints ρ = ⋂ d, ⋂ f ∈ {f | f ∈ ProjSpace.grading A N d ∧ f ∈ X.ideal},
      {v : CP N | f ∈ (projPoint ρ v).asHomogeneousIdeal} := by
    ext v
    simp only [mem_complexPoints_iff, Set.mem_iInter, Set.mem_ofPred_eq, and_imp]
  rw [this]
  exact isClosed_iInter fun d => isClosed_biInter fun f hf => isClosed_setOf_mem_projPoint ρ hf.1

theorem isCompact_complexPoints (ρ : A →+* ℂ) : IsCompact (X.complexPoints ρ) :=
  (X.isClosed_complexPoints ρ).isCompact

instance (ρ : A →+* ℂ) : CompactSpace (X.complexPoints ρ) :=
  isCompact_iff_compactSpace.mp (X.isCompact_complexPoints ρ)

lemma conj_mem_complexPoints {ρ : A →+* ℂ} {v : CP N} (hv : v ∈ X.complexPoints ρ) :
    CP.conj v ∈ X.complexPoints ((starRingEnd ℂ).comp ρ) := by
  change projPoint ((starRingEnd ℂ).comp ρ) (CP.conj v) ∈ Set.range X.ι.base
  rw [projPoint_conj]
  exact hv

def conjPoint (ρ : A →+* ℂ) (x : X.complexPoints ρ) :
    X.complexPoints ((starRingEnd ℂ).comp ρ) :=
  ⟨CP.conj x.1, X.conj_mem_complexPoints x.2⟩

lemma continuous_conjPoint (ρ : A →+* ℂ) : Continuous (X.conjPoint ρ) :=
  (CP.continuous_conj.comp continuous_subtype_val).subtype_mk _

lemma conjPoint_conjPoint (ρ : A →+* ℂ) (x : X.complexPoints ρ) :
    ((X.conjPoint ((starRingEnd ℂ).comp ρ) (X.conjPoint ρ x)) : CP N) = x := CP.conj_conj x.1

theorem complexPoints_self (ρ : A →+* ℂ) : (self A N).complexPoints ρ = Set.univ := by
  ext v
  simp only [complexPoints, Set.mem_ofPred_eq, Set.mem_univ, iff_true]
  exact ⟨projPoint ρ v, rfl⟩

end ProjScheme

end

end GroundTheory.Heights₂.Heights
