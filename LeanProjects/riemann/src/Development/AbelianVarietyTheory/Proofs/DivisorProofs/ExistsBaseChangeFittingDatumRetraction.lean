import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsorsTrivial
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OriginIdeal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClosureFiniteEtale
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PointAtZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericFibreCompatibility
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KeyOriginRetractionLocalisesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ZmodTorsorBaseChangeTransportPointStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBaseChangeRetractStatement
open IsLocalRing Polynomial

noncomputable section

namespace GlobalTheory.KeyOriginEnlarge

theorem exists_baseChange_fits : ∀ (T O : Type) [CommRing T] [IsDomain T] [IsLocalRing T] [CommRing O] [IsLocalRing O] [Algebra T O]
    [Algebra (Polynomial T) O] [IsScalarTower T (Polynomial T) O]
    (P : Ideal (Polynomial T)) [P.IsPrime] (φ : Localization.AtPrime P →+* O),
    φ.comp (algebraMap (Polynomial T) _) = algebraMap (Polynomial T) O →
    GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec.IsStrictHenselisation φ → P = GlobalTheory.KeyOriginCut.originIdeal T →
    ∀ (q : ℕ), 0 < q →
    ∀ (A : Type) [CommRing A] [IsDomain A] [IsLocalRing A] [IsNoetherianRing A] [IsIntegrallyClosed A]
      [Algebra.EssFiniteType ℤ A] (i : A →+* T)
      (EA : Type) [CommRing EA] [Algebra (Polynomial A) EA] [Algebra A EA]
      [IsScalarTower A (Polynomial A) EA] [Algebra.Etale (Polynomial A) EA]
      (QA : Ideal EA) [QA.IsPrime] (jA : Localization.AtPrime QA →+* O)
      (ψA : GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA) →+* GlobalTheory.LocAcyc.GenFib T O)
      (DA : Type) [CommRing DA] [Algebra (GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA)) DA]
      (actA : Multiplicative (ZMod q) →* (DA ≃ₐ[GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA)] DA)),
    GlobalTheory.KeyOriginEnlarge.Fits T O q A i EA QA jA ψA DA actA →
    ∀ ρ : Localization.AtPrime QA →+* A, GlobalTheory.KeyOriginEnlarge.Retracts T O A i EA QA jA ρ →
    ∀ (A₁ : Type) [CommRing A₁] [IsDomain A₁] [IsLocalRing A₁] [IsNoetherianRing A₁] [IsIntegrallyClosed A₁]
      [Algebra.EssFiniteType ℤ A₁] (j : A →+* A₁) (i₁ : A₁ →+* T),
      Function.Injective j → Function.Injective i₁ → IsLocalHom i₁ → i₁.comp j = i →
    ∃ (EA₁ : Type) (_ : CommRing EA₁) (_ : Algebra (Polynomial A₁) EA₁) (_ : Algebra A₁ EA₁)
      (_ : IsScalarTower A₁ (Polynomial A₁) EA₁) (_ : Algebra.Etale (Polynomial A₁) EA₁)
      (QA₁ : Ideal EA₁) (_ : QA₁.IsPrime) (jA₁ : Localization.AtPrime QA₁ →+* O)
      (ψA₁ : GlobalTheory.LocAcyc.GenFib A₁ (Localization.AtPrime QA₁) →+* GlobalTheory.LocAcyc.GenFib T O)
      (DA₁ : Type) (_ : CommRing DA₁) (_ : Algebra (GlobalTheory.LocAcyc.GenFib A₁ (Localization.AtPrime QA₁)) DA₁)
      (actA₁ : Multiplicative (ZMod q) →* (DA₁ ≃ₐ[GlobalTheory.LocAcyc.GenFib A₁ (Localization.AtPrime QA₁)] DA₁))
      (ρ₁ : Localization.AtPrime QA₁ →+* A₁),
      GlobalTheory.KeyOriginEnlarge.Fits T O q A₁ i₁ EA₁ QA₁ jA₁ ψA₁ DA₁ actA₁ ∧
      GlobalTheory.KeyOriginEnlarge.Retracts T O A₁ i₁ EA₁ QA₁ jA₁ ρ₁ ∧
      ∃ (β : GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA) →+* GlobalTheory.LocAcyc.GenFib A₁ (Localization.AtPrime QA₁))
        (h : DA →+* DA₁),
        ψA₁.comp β = ψA ∧
        h.comp (algebraMap (GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA)) DA) =
          (algebraMap (GlobalTheory.LocAcyc.GenFib A₁ (Localization.AtPrime QA₁)) DA₁).comp β ∧
        ∀ σ : DA →+* FractionRing A₁,
          (σ.comp (algebraMap (GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA)) DA)).comp
              (algebraMap (Localization.AtPrime QA) (GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA))) =
            (algebraMap A₁ (FractionRing A₁)).comp (j.comp ρ) →
          ∃ σ₁ : DA₁ →+* FractionRing A₁,
            (σ₁.comp (algebraMap (GlobalTheory.LocAcyc.GenFib A₁ (Localization.AtPrime QA₁)) DA₁)).comp
                (algebraMap (Localization.AtPrime QA₁) (GlobalTheory.LocAcyc.GenFib A₁ (Localization.AtPrime QA₁))) =
              (algebraMap A₁ (FractionRing A₁)).comp ρ₁ := by
  intro T O _ _ _ _ _ _ _ _ P _ φ hφ hSH hP q hq A _ _ _ _ _ _ i EA _ _ _ _ _ QA _ jA ψA DA _ _ actA hFits ρ hRet
    A₁ _ _ _ _ _ _ j i₁ hj hi₁ hi₁l hij
  haveI hφl : IsLocalHom φ := hSH.2.2.1
  have hX : algebraMap (Polynomial T) O Polynomial.X ∈ maximalIdeal O := by
    rw [← hφ, RingHom.comp_apply]
    apply map_nonunit φ
    refine (IsLocalization.AtPrime.to_map_mem_maximal_iff (Localization.AtPrime P) P _).2 ?_
    rw [hP]; exact Ideal.mem_sup_right (Ideal.mem_span_singleton_self _)
  have hTO : IsLocalHom (algebraMap T O) := by
    refine ⟨fun a ha => ?_⟩
    by_contra hna
    have h1 : Polynomial.C a ∈ P := by
      rw [hP]; exact Ideal.mem_sup_left (Ideal.mem_map_of_mem _ ((IsLocalRing.mem_maximalIdeal _).2 hna))
    refine (IsLocalization.AtPrime.isUnit_to_map_iff (Localization.AtPrime P) P (Polynomial.C a)).1
      (isUnit_of_map_unit φ _ ?_) h1
    rw [← RingHom.comp_apply, hφ]
    rw [IsScalarTower.algebraMap_apply T (Polynomial T) O] at ha
    exact ha
  obtain ⟨hi, hil, hqu, hQA, hjA, hψA, htors⟩ := hFits
  obtain ⟨EA₁, _, _, _, _, _, QA₁, _, jA₁, γ₀, γ, ρ', hQA₁, hjA₁, hjγ, hγ₀, hγA, hρ'γ, hρ'id, hρ'X, hρ'c, hρ'k⟩ :=
    GlobalTheory.T.exists_baseChange_retract_alt T O hTO hX A i EA QA jA ρ hQA hjA hRet A₁ j i₁ hi₁ hi₁l hij
  obtain ⟨ρ₁, hRet₁, hρ₁⟩ := GlobalTheory.T.keyOrigin_retraction_localises T O A₁ EA₁ i₁ hi₁l hTO QA₁ jA₁ ρ' hX hρ'id hρ'X hρ'c hρ'k
  have hjA₁c : jA₁.comp (algebraMap A₁ (Localization.AtPrime QA₁)) = (algebraMap T O).comp i₁ := by
    ext a
    have e1 : algebraMap A₁ (Localization.AtPrime QA₁) a =
        algebraMap (Polynomial A₁) (Localization.AtPrime QA₁) (Polynomial.C a) := by
      rw [IsScalarTower.algebraMap_apply A₁ EA₁ (Localization.AtPrime QA₁),
        IsScalarTower.algebraMap_apply A₁ (Polynomial A₁) EA₁,
        IsScalarTower.algebraMap_apply (Polynomial A₁) EA₁ (Localization.AtPrime QA₁)]
      rfl
    rw [RingHom.comp_apply, e1, ← RingHom.comp_apply, hjA₁, RingHom.comp_apply, Polynomial.coe_mapRingHom,
      Polynomial.map_C, RingHom.comp_apply, IsScalarTower.algebraMap_apply T (Polynomial T) O]
    rfl
  obtain ⟨ψA₁, β, hψA₁, hψβ, hβ⟩ := GlobalTheory.T.generic_fibre_compatibility T O A A₁ _ _ j i₁ hj hi₁ jA jA₁ γ ψA hjA₁c hγA hjγ hψA
  have hργ : ρ₁.comp γ = j.comp ρ := by
    apply IsLocalization.ringHom_ext QA.primeCompl
    rw [RingHom.comp_assoc, hγ₀, ← RingHom.comp_assoc, hρ₁, hρ'γ, RingHom.comp_assoc]
  obtain ⟨DA₁, _, _, actA₁, h, htors₁, hh, hpt⟩ :=
    GlobalTheory.T.zmodTorsor_baseChange_transport_point A A₁ _ _ j γ ρ ρ₁ β hβ hRet₁.1 hργ q hq DA actA htors
  refine ⟨EA₁, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, QA₁, inferInstance,
    jA₁, ψA₁, DA₁, inferInstance, inferInstance, actA₁, ρ₁, ⟨hi₁, hi₁l, ?_, hQA₁, hjA₁, hψA₁, htors₁⟩, hRet₁,
    β, h, hψβ, hh, hpt⟩
  have := hqu.map j
  simpa using this

end GlobalTheory.KeyOriginEnlarge
