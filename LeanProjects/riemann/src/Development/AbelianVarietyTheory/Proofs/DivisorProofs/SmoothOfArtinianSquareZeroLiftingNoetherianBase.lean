import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDefiniteDatumGoodObj
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsSmoothOfDefectZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InjectiveCotangentComplexBaseChangeOfFormsExtendStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDerivationExtendingKernelFormOfLiftingStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftRingHomAffineOpenOfArtinianSchemeLiftStatement

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.SmoothCrit

theorem smooth_of_lift (A R : Type) [CommRing A] [IsNoetherianRing A] [CommRing R] (g : A →+* R) (hg : g.FiniteType)
    (H : (∀ (C C₀ : Type) [CommRing C] [IsLocalRing C] [IsArtinianRing C] [CommRing C₀] (π : C →+* C₀), Function.Surjective π → RingHom.ker π ^ 2 = ⊥ → ∀ (β : A →+* C) (φ₀ : R →+* C₀), φ₀.comp (g) = π.comp β → ∃ φ : R →+* C, π.comp φ = φ₀ ∧ φ.comp (g) = β)) : g.Smooth := by
  algebraize [g]
  have : Algebra.FinitePresentation A R := Algebra.FinitePresentation.of_finiteType.mp hg
  obtain ⟨n, f, hf⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.mp (inferInstance : Algebra.FiniteType A R)
  letI := f.toRingHom.toAlgebra
  haveI : IsScalarTower A (MvPolynomial (Fin n) A) R := IsScalarTower.of_algebraMap_eq fun a => (f.commutes a).symm
  have hs : Function.Surjective (algebraMap (MvPolynomial (Fin n) A) R) := hf
  have hmax : ∀ (m : Ideal R) [m.IsMaximal], Algebra.IsSmoothAt A m := by
    intro m _
    letI : Field (R ⧸ m) := Ideal.Quotient.field m
    have key := GlobalTheory.T.injective_cotangentComplexBaseChange_of_forms_extend' A (MvPolynomial (Fin n) A) R (R ⧸ m) fun ℓ => GlobalTheory.T.exists_derivation_extending_kernel_form_of_lifting A (MvPolynomial (Fin n) A) R (R ⧸ m) hs Ideal.Quotient.mk_surjective H ℓ
    exact (GlobalTheory.SS.DefectZero.isSmoothAt_iff_injective A (MvPolynomial (Fin n) A) R (R ⧸ m) hs m
      (Ideal.mk_ker).symm).mpr key
  have hU : Algebra.smoothLocus A R = Set.univ := by
    refine Set.eq_univ_iff_forall.mpr fun q => ?_
    obtain ⟨m, hm, hqm⟩ := Ideal.exists_le_maximal q.asIdeal q.2.ne_top
    have hm' : (⟨m, hm.isPrime⟩ : PrimeSpectrum R) ∈ Algebra.smoothLocus A R := @hmax m hm
    exact ((PrimeSpectrum.le_iff_specializes q ⟨m, hm.isPrime⟩).mp hqm).mem_open Algebra.isOpen_smoothLocus hm'
  exact ⟨Algebra.smoothLocus_eq_univ_iff.mp hU, inferInstance⟩

theorem smooth_of_artinian_lift : ∀ (B : Type) [CommRing B] [IsNoetherianRing B] (X : Scheme.{0}) (s : X ⟶ Sp B), LocallyOfFiniteType s → (∀ (C C₀ : Type) [CommRing C] [IsLocalRing C] [IsArtinianRing C] [CommRing C₀] (π : C →+* C₀), Function.Surjective π → RingHom.ker π ^ 2 = ⊥ → ∀ (t : Sp C ⟶ Sp B) (x₀ : Sp C₀ ⟶ X), x₀ ≫ s = spMap π ≫ t → ∃ x : Sp C ⟶ X, spMap π ≫ x = x₀ ∧ x ≫ s = t) → Smooth s := by
  intro B _ _ X s hs H
  constructor
  intro U hU V hV e
  haveI : IsNoetherianRing Γ(Sp B, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  exact smooth_of_lift _ _ _ (HasRingHomProperty.appLE @LocallyOfFiniteType s hs ⟨U, hU⟩ ⟨V, hV⟩ e) (GlobalTheory.T.lift_ringHom_affine_open_of_artinian_scheme_lift B X s H U hU V hV e)

end GlobalTheory.SmoothCrit
