import Mathlib

open CategoryTheory AlgebraicGeometry IsLocalRing

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec

attribute [local instance] MvPolynomial.gradedAlgebra

abbrev degreeGrading (R : Type) [CommRing R] (N : ℕ) :
    ℕ → Submodule R (MvPolynomial (Fin (N + 1)) R) :=
  MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R

def projSpace (R : Type) [CommRing R] (N : ℕ) : Scheme.{0} :=
  Proj (degreeGrading R N)

def projSpaceToSpec (R : Type) [CommRing R] (N : ℕ) : projSpace R N ⟶ Spec (CommRingCat.of R) :=
  Proj.toSpecZero (degreeGrading R N) ≫
    Spec.map (CommRingCat.ofHom (algebraMap R (degreeGrading R N 0)))

def IsProjectiveOver (R : Type) [CommRing R] {X : Scheme.{0}} (f : X ⟶ Spec (CommRingCat.of R)) :
    Prop :=
  ∃ (N : ℕ) (i : X ⟶ projSpace R N), IsClosedImmersion i ∧ i ≫ projSpaceToSpec R N = f

def IsQuasiProjectiveOver (R : Type) [CommRing R] {X : Scheme.{0}}
    (f : X ⟶ Spec (CommRingCat.of R)) : Prop :=
  ∃ (N : ℕ) (i : X ⟶ projSpace R N),
    IsImmersion i ∧ QuasiCompact i ∧ i ≫ projSpaceToSpec R N = f

def IsNormalScheme (X : Scheme.{0}) : Prop :=
  ∀ x : X, IsDomain (X.presheaf.stalk x) ∧ IsIntegrallyClosed (X.presheaf.stalk x)

def IsIndEtale {A S : Type} [CommRing A] [CommRing S] (φ : A →+* S) : Prop :=
  MorphismProperty.ind.{0} (RingHom.toMorphismProperty @RingHom.Etale) (CommRingCat.ofHom φ)

def IsStrictHenselisation {A S : Type} [CommRing A] [IsLocalRing A] [CommRing S] [IsLocalRing S]
    (φ : A →+* S) : Prop :=
  HenselianLocalRing S ∧ IsSepClosed (ResidueField S) ∧ IsLocalHom φ ∧ IsIndEtale φ

def IsCompletedStrictHenselisation {A R : Type} [CommRing A] [IsLocalRing A] [CommRing R]
    (φ : A →+* R) : Prop :=
  ∃ (S : Type) (_ : CommRing S) (_ : IsLocalRing S) (ψ : A →+* S),
    IsStrictHenselisation ψ ∧
      ∃ e : AdicCompletion (maximalIdeal S) S ≃+* R,
        ∀ a : A, e (algebraMap S (AdicCompletion (maximalIdeal S) S) (ψ a)) = φ a

theorem isStrictHenselisation_real_complex : IsStrictHenselisation (algebraMap ℝ ℂ) := by
  refine ⟨inferInstance, ?_, inferInstance, ?_⟩
  · have e : ℂ ≃+* ResidueField ℂ := RingEquiv.ofBijective (residue ℂ)
      ⟨(residue ℂ).injective, residue_surjective⟩
    haveI : IsAlgClosed (ResidueField ℂ) := IsAlgClosed.of_ringEquiv ℂ _ e
    infer_instance
  · refine MorphismProperty.le_ind _ _ ?_
    change (algebraMap ℝ ℂ).Etale
    rw [RingHom.etale_algebraMap]
    haveI : Algebra.FormallyEtale ℝ ℂ := Algebra.FormallyEtale.of_isSeparable ℝ ℂ
    haveI : Algebra.FinitePresentation ℝ ℂ :=
      (Algebra.FinitePresentation.of_finiteType).1 inferInstance
    exact ⟨inferInstance, inferInstance⟩

end GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec
