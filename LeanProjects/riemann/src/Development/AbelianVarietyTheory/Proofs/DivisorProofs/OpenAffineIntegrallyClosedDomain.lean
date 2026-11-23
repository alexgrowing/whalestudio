import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitChartAt
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsDiscreteValuationRingAndFiniteResidueFieldValu
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbProj
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DensityStatementHolds
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.IsIntegralCoeffZeroMulOfAevalInv
import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.IsOpenOfMemIrreducibleComponentsOfFinite

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete
open GlobalTheory.FlatModel

namespace GlobalTheory.FlatModel

theorem chart_normal_domain_testPoints : ∀ (F : Type) [Field F] [NumberField F] (V : ValuationSubring F) (p : ℕ) [Fact p.Prime], (p : F) ∈ V.nonunits → ∀ (X : Scheme.{0}) (s : X ⟶ Sp V) (Xw : X.Opens), IsIntegral X → ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme X → Flat s → LocallyOfFiniteType s → Xw ≤ X.basicOpen (p : Γ(X, ⊤)) → (Xw : Set X).Nonempty → ∀ (A : Type) [CommRing A] (w : Sp A ⟶ X), IsOpenImmersion w → Nonempty (Sp A) → ∃ (_ : IsDomain A) (_ : IsIntegrallyClosed A) (_ : Algebra V A) (_ : Algebra.FiniteType V A), Function.Injective (algebraMap V A) ∧ ∃ e : A, e ≠ 0 ∧ ∀ (T : CDVR) (kO : T.V →+* 𝓞_ℂ_[p]) (φ : A →+* T.V), T.FinRes → Function.Injective kO → φ e ≠ 0 → IsTest p Xw (spMap (kO.comp φ) ≫ w) := by
  intro F _ _ V p _ hp X s Xw hX hN hflat hlft hXw hne A _ w hw hA
  haveI : IsIntegral (Sp A) := isIntegral_of_isOpenImmersion w
  haveI : IsDomain A := (affine_isIntegral_iff (CommRingCat.of A)).1 inferInstance
  haveI : GlobalTheory.IsNormalScheme X := GlobalTheory.IsNormalScheme.of_pred hN
  haveI : GlobalTheory.IsNormalScheme (Sp A) := GlobalTheory.IsNormalScheme.of_isOpenImmersion w
  have hic : IsIntegrallyClosed A :=
    (GlobalTheory.IsNormalScheme.spec_iff_of_isDomain (CommRingCat.of A)).1 inferInstance
  let f : V →+* A := (Spec.preimage (w ≫ s)).hom
  letI : Algebra V A := f.toAlgebra
  haveI hft : Algebra.FiniteType V A := by
    have h : LocallyOfFiniteType (w ≫ s) := inferInstance
    rw [← Spec.map_preimage (w ≫ s)] at h
    exact (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).1 h
  have hinj : Function.Injective (algebraMap V A) := by
    have h : Flat (w ≫ s) := inferInstance
    rw [← Spec.map_preimage (w ≫ s)] at h
    haveI : Module.Flat V A := (HasRingHomProperty.Spec_iff (P := @Flat)).1 h
    rw [injective_iff_map_eq_zero]
    intro a ha
    by_contra h0
    have hreg := Module.Flat.isSMulRegular_of_nonZeroDivisors (M := A) (mem_nonZeroDivisors_of_ne_zero h0)
    have h1 : a • (1 : A) = a • (0 : A) := by rw [Algebra.smul_def, _root_.mul_one, ha, smul_zero]
    exact one_ne_zero (hreg h1)
  obtain ⟨y⟩ := hA
  have hopen : IsOpen (Set.range w) := w.isOpenEmbedding.isOpen_range
  obtain ⟨_, ⟨z, rfl⟩, hz⟩ := nonempty_preirreducible_inter hopen Xw.isOpen ⟨_, y, rfl⟩ hne
  have hzO : z ∈ w ⁻¹ᵁ Xw := hz
  obtain ⟨_, ⟨e, rfl⟩, hze, hsub⟩ := PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open
    hzO (w ⁻¹ᵁ Xw).isOpen
  have he : e ≠ 0 := by
    rintro rfl
    exact (PrimeSpectrum.mem_basicOpen _ _).1 hze (Ideal.zero_mem _)
  refine ⟨inferInstance, hic, this, hft, hinj, e, he, ?_⟩
  intro T kO φ hT hkO hφe
  refine ⟨⟨T, kO, spMap φ ≫ w, hT, hkO, sp_sp _ _ _⟩, ?_⟩
  rintro _ ⟨u, rfl⟩
  have hu : u = (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum ℂ_[p]) := by
    apply PrimeSpectrum.ext
    haveI := (u : PrimeSpectrum ℂ_[p]).isPrime
    exact Ideal.eq_bot_of_prime _
  subst hu
  have hinj2 : Function.Injective ((algebraMap 𝓞_ℂ_[p] ℂ_[p]).comp kO) := Subtype.val_injective.comp hkO
  rw [← sp_sp φ kO w, sp_sp kO (algebraMap 𝓞_ℂ_[p] ℂ_[p]) (spMap φ ≫ w), bot_map hinj2 (spMap φ ≫ w)]
  have hq : (spMap φ) (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum T.V) ∈ PrimeSpectrum.basicOpen e := by
    show e ∉ Ideal.comap φ ⊥
    simpa using hφe
  exact hsub hq

end GlobalTheory.FlatModel

end
