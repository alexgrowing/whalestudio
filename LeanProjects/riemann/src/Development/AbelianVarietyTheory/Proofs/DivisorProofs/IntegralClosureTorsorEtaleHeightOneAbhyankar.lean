import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComapMaximalIdealEqOrigin
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsDomainAndIsIntegrallyClosedAtPrimeOfSmoothOfCo
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeightOnePrimeOverConstantIdeal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeightOneContractionOfEtalePrime
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericFibreBaseChangeInjective

open IsLocalRing Polynomial
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.KeyOriginBC

theorem comap_map_C_mapRingHom {A A₁ : Type} [CommRing A] [CommRing A₁] (f : A →+* A₁) (p₁ : Ideal A₁) :
    (p₁.map (Polynomial.C : A₁ →+* A₁[X])).comap (Polynomial.mapRingHom f) =
      (p₁.comap f).map (Polynomial.C : A →+* A[X]) := by
  ext g
  simp only [Ideal.mem_comap, Ideal.mem_map_C_iff, Polynomial.coe_mapRingHom, Polynomial.coeff_map]

theorem atPrime_isDomain_injective (A : Type) [CommRing A] [IsDomain A] [IsNoetherianRing A]
    [IsIntegrallyClosed A]
    (EA : Type) [CommRing EA] [Algebra (Polynomial A) EA] [Algebra A EA]
    [IsScalarTower A (Polynomial A) EA] [Algebra.Etale (Polynomial A) EA]
    (QA : Ideal EA) [QA.IsPrime] :
    IsDomain (Localization.AtPrime QA) ∧
      Function.Injective (algebraMap A (Localization.AtPrime QA)) := by
  obtain ⟨hd, -⟩ := GlobalTheory.isDomain_and_isIntegrallyClosed_atPrime_of_etale (Polynomial A) QA
    (Localization.AtPrime QA)
  refine ⟨hd, ?_⟩
  haveI := hd
  haveI : Module.Flat (Polynomial A) (Localization.AtPrime QA) :=
    Module.Flat.trans (Polynomial A) EA (Localization.AtPrime QA)
  have h1 : Function.Injective (algebraMap (Polynomial A) (Localization.AtPrime QA)) :=
    FaithfulSMul.algebraMap_injective (Polynomial A) (Localization.AtPrime QA)
  have h2 : algebraMap A (Localization.AtPrime QA) =
      (algebraMap (Polynomial A) (Localization.AtPrime QA)).comp (algebraMap A (Polynomial A)) :=
    IsScalarTower.algebraMap_eq _ _ _
  rw [h2]
  exact h1.comp Polynomial.C_injective

theorem closureEtaleAt_of_mem_height_le_one : ∀ (T O : Type) [CommRing T] [CommRing O] [IsLocalRing O] [Algebra T O] [Algebra T[X] O]
    [IsScalarTower T T[X] O]
    (A A₁ : Type) [CommRing A] [IsDomain A] [IsLocalRing A] [IsNoetherianRing A] [IsIntegrallyClosed A]
    [Algebra.EssFiniteType ℤ A] [CommRing A₁] [IsDomain A₁] [IsLocalRing A₁] [IsNoetherianRing A₁]
    [IsIntegrallyClosed A₁] [Algebra.EssFiniteType ℤ A₁] (f : A →+* A₁) (i : A →+* T)
    (i₁ : A₁ →+* T) (hf : Function.Injective f)
    (EA : Type) [CommRing EA] [Algebra A[X] EA] [Algebra A EA] [IsScalarTower A A[X] EA]
    [Algebra.Etale A[X] EA]
    (QA : Ideal EA) [QA.IsPrime] (jA : Localization.AtPrime QA →+* O) (hcomp : i₁.comp f = i)
    (hj : jA.comp (algebraMap A[X] (Localization.AtPrime QA)) =
      (algebraMap T[X] O).comp (Polynomial.mapRingHom i))
    (DA : Type) [CommRing DA] [Algebra (GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA)) DA] (q : ℕ)
    (actA : Multiplicative (ZMod q) →* (DA ≃ₐ[GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA)] DA)),
    0 < q → IsUnit (q : A) →
    GlobalTheory.KeyOriginCut.IsZTorsor (GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA)) DA q actA →
    ∀ a : A, a ≠ 0 →
    (∀ (p₁ : Ideal A₁) [p₁.IsPrime], p₁.height = 1 → f a ∈ p₁ →
        (p₁.comap f).height = 1 ∧
        ∃ π : A, Irreducible (algebraMap A (Localization.AtPrime (p₁.comap f)) π) ∧
          ∃ y : A₁, y ^ q = f π) →
    ∀ (P₁ : Ideal (GlobalTheory.KeyOriginBC.Loc₁ f i i₁ EA QA jA hcomp hj)) [P₁.IsPrime], P₁.height ≤ 1 → algebraMap A₁ (GlobalTheory.KeyOriginBC.Loc₁ f i i₁ EA QA jA hcomp hj) (f a) ∈ P₁ →
      GlobalTheory.KeyOriginEnlarge.ClosureEtaleAt A₁ (GlobalTheory.KeyOriginBC.Loc₁ f i i₁ EA QA jA hcomp hj) (GlobalTheory.KeyOriginBC.BC (GlobalTheory.KeyOriginBC.fibBC f i i₁ EA QA jA hcomp hj hf) DA) P₁ := by
  intro T O _ _ _ _ _ _ A A₁ _ _ _ _ _ _ _ _ _ _ _ _ f i i₁ hf EA _ _ _ _ _ QA _ jA hcomp hj DA _ _ q actA
    hq hqu htor a ha hhyp P₁ _ hP₁ hfa
  obtain ⟨hRd, hRi⟩ := atPrime_isDomain_injective A EA QA
  obtain ⟨hR₁d, hR₁i⟩ := atPrime_isDomain_injective A₁ (Ext f EA) (ideal₁ f i i₁ EA QA jA hcomp hj)
  have hfa0 : f a ≠ 0 := fun h => ha (hf (by rw [h, map_zero]))
  obtain ⟨hp₁h, hX₁⟩ := GlobalTheory.T.height_one_contraction_of_etale_prime A₁ (Ext f EA) (ideal₁ f i i₁ EA QA jA hcomp hj) P₁ (f a)
    hfa0 hfa hP₁
  obtain ⟨hph, π, hπ, y, hy⟩ := hhyp _ hp₁h (by rw [Ideal.mem_comap]; exact hfa)
  obtain ⟨⟨_, hdvr₁⟩, -⟩ := GlobalTheory.T.height_one_prime_over_constant_ideal A₁ (Ext f EA) (ideal₁ f i i₁ EA QA jA hcomp hj) P₁ _
    hp₁h hX₁
  have hsq : (locBC f i i₁ EA QA jA hcomp hj).comp (algebraMap A[X] (Localization.AtPrime QA)) =
      (algebraMap A₁[X] (Loc₁ f i i₁ EA QA jA hcomp hj)).comp (Polynomial.mapRingHom f) := by
    apply RingHom.ext; intro p
    rw [RingHom.comp_apply, IsScalarTower.algebraMap_apply A[X] EA (Localization.AtPrime QA),
      locBC_algebraMap, RingHom.comp_apply, IsScalarTower.algebraMap_apply A₁[X] (Ext f EA)]
    congr 1
    rw [inclE_apply, Algebra.TensorProduct.algebraMap_apply]
    rw [← Algebra.TensorProduct.tmul_one_eq_one_tmul]
    rfl
  have hPX : (P₁.comap (locBC f i i₁ EA QA jA hcomp hj)).comap
      (algebraMap A[X] (Localization.AtPrime QA)) =
      ((P₁.comap (algebraMap A₁ (Loc₁ f i i₁ EA QA jA hcomp hj))).comap f).map
        (Polynomial.C : A →+* A[X]) := by
    rw [Ideal.comap_comap, hsq, ← Ideal.comap_comap, hX₁, comap_map_C_mapRingHom]
  obtain ⟨⟨_, hdvr⟩, hirr⟩ := GlobalTheory.T.height_one_prime_over_constant_ideal A EA QA (P₁.comap (locBC f i i₁ EA QA jA hcomp hj)) _
    hph hPX
  have hsqA : (locBC f i i₁ EA QA jA hcomp hj).comp (algebraMap A (Localization.AtPrime QA)) =
      (algebraMap A₁ (Loc₁ f i i₁ EA QA jA hcomp hj)).comp f := by
    apply RingHom.ext; intro x
    exact locBC_algebraMap_base f i i₁ EA QA jA hcomp hj x
  have hsqF : (fibBC f i i₁ EA QA jA hcomp hj hf).comp
      (algebraMap (Localization.AtPrime QA) (GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA))) =
      (algebraMap (Loc₁ f i i₁ EA QA jA hcomp hj)
        (GlobalTheory.LocAcyc.GenFib A₁ (Loc₁ f i i₁ EA QA jA hcomp hj))).comp
        (locBC f i i₁ EA QA jA hcomp hj) := by
    apply RingHom.ext; intro x
    exact fibBC_algebraMap f i i₁ EA QA jA hcomp hj hf x
  exact GlobalTheory.T.generic_fibre_base_change_injective A (Localization.AtPrime QA) hRi A₁ (Loc₁ f i i₁ EA QA jA hcomp hj) hR₁i
    f hf _ hsqA _ hsqF DA q actA hq hqu htor P₁ hdvr₁ hdvr π (hirr π hπ)
    (algebraMap A₁ _ y) (by rw [← map_pow, hy, ← RingHom.comp_apply, ← hsqA, RingHom.comp_apply])

end GlobalTheory.KeyOriginBC
