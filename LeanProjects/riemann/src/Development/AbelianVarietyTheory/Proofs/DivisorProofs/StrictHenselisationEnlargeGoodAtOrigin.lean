import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsorsTrivial
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OriginIdeal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClosureFiniteEtale
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PointAtZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EnlargeStrictHenselisationRetractModStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EnlargeBaseSeparablePointIntegralClosureStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleEnlargeByUniformiserRootsStatement

open IsLocalRing Polynomial

namespace GlobalTheory.KeyOriginEnlarge

theorem enlarge_good : ∀ (T O : Type) [CommRing T] [IsDomain T] [IsLocalRing T] [CommRing O] [IsLocalRing O] [Algebra T O]
    [Algebra (Polynomial T) O] [IsScalarTower T (Polynomial T) O], GlobalTheory.LocAcyc.AbsIntClosed T →
    ∀ (P : Ideal (Polynomial T)) [P.IsPrime] (φ : Localization.AtPrime P →+* O),
    φ.comp (algebraMap (Polynomial T) _) = algebraMap (Polynomial T) O →
    GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec.IsStrictHenselisation φ → P = GlobalTheory.KeyOriginCut.originIdeal T →
    ∀ (q : ℕ), 0 < q → IsUnit (q : T) →
    ∀ (A : Type) [CommRing A] [IsDomain A] [IsLocalRing A] [IsNoetherianRing A] [IsIntegrallyClosed A] [Algebra.EssFiniteType ℤ A]
      (i : A →+* T), Function.Injective i → IsLocalHom i → IsUnit (q : A) →
    ∀ (EA : Type) [CommRing EA] [Algebra (Polynomial A) EA] [Algebra A EA]
      [IsScalarTower A (Polynomial A) EA] [Algebra.Etale (Polynomial A) EA]
      (QA : Ideal EA) [QA.IsPrime],
      QA.comap (algebraMap (Polynomial A) EA) = GlobalTheory.KeyOriginCut.originIdeal A →
    ∀ (jA : Localization.AtPrime QA →+* O),
      jA.comp (algebraMap (Polynomial A) (Localization.AtPrime QA)) =
        (algebraMap (Polynomial T) O).comp (Polynomial.mapRingHom i) →
    ∀ (ψA : GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA) →+* GlobalTheory.LocAcyc.GenFib T O),
      ψA.comp (algebraMap (Localization.AtPrime QA) (GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA))) =
        (algebraMap O (GlobalTheory.LocAcyc.GenFib T O)).comp jA →
    ∀ (DA : Type) [CommRing DA] [Algebra (GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA)) DA]
      (actA : Multiplicative (ZMod q) →* (DA ≃ₐ[GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA)] DA)),
      GlobalTheory.KeyOriginCut.IsZTorsor (GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA)) DA q actA →
    ∃ (A' : Type) (_ : CommRing A') (_ : IsDomain A') (_ : IsLocalRing A') (_ : IsNoetherianRing A')
      (_ : IsIntegrallyClosed A') (_ : Algebra.EssFiniteType ℤ A')
      (EA' : Type) (_ : CommRing EA') (_ : Algebra (Polynomial A') EA') (_ : Algebra A' EA')
      (_ : IsScalarTower A' (Polynomial A') EA') (_ : Algebra.Etale (Polynomial A') EA')
      (QA' : Ideal EA') (_ : QA'.IsPrime),
      QA'.comap (algebraMap (Polynomial A') EA') = GlobalTheory.KeyOriginCut.originIdeal A' ∧ IsUnit (q : A') ∧
      ∃ (ρ' : Localization.AtPrime QA' →+* A'),
        ρ'.comp (algebraMap A' (Localization.AtPrime QA')) = RingHom.id A' ∧
        RingHom.ker ρ' = Ideal.span {algebraMap (Polynomial A') (Localization.AtPrime QA') Polynomial.X} ∧
      ∃ (jA' : Localization.AtPrime QA' →+* O)
        (ψA' : GlobalTheory.LocAcyc.GenFib A' (Localization.AtPrime QA') →+* GlobalTheory.LocAcyc.GenFib T O),
        ψA'.comp (algebraMap (Localization.AtPrime QA') (GlobalTheory.LocAcyc.GenFib A' (Localization.AtPrime QA'))) =
          (algebraMap O (GlobalTheory.LocAcyc.GenFib T O)).comp jA' ∧
      ∃ (DA' : Type) (_ : CommRing DA') (_ : Algebra (GlobalTheory.LocAcyc.GenFib A' (Localization.AtPrime QA')) DA')
        (actA' : Multiplicative (ZMod q) →* (DA' ≃ₐ[GlobalTheory.LocAcyc.GenFib A' (Localization.AtPrime QA')] DA')),
        GlobalTheory.KeyOriginCut.IsZTorsor (GlobalTheory.LocAcyc.GenFib A' (Localization.AtPrime QA')) DA' q actA' ∧
        GlobalTheory.KeyOriginNoeth.Good A' (Localization.AtPrime QA') DA' ρ' ∧
        ∃ (β : GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA) →+* GlobalTheory.LocAcyc.GenFib A' (Localization.AtPrime QA'))
          (h : DA →+* DA'),
          ψA'.comp β = ψA ∧
          h.comp (algebraMap (GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA)) DA) =
            (algebraMap (GlobalTheory.LocAcyc.GenFib A' (Localization.AtPrime QA')) DA').comp β := by
  intro T O _ _ _ _ _ _ _ _ hT P _ φ hφ hsh hP q hq0 hqT A _ _ _ _ _ _ i hi hil hqA EA _ _ _ _ _ QA _ hQA jA hjA
    ψA hψA DA _ _ actA htor
  have hF : GlobalTheory.KeyOriginEnlarge.Fits T O q A i EA QA jA ψA DA actA :=
    ⟨hi, hil, hqA, hQA, hjA, hψA, htor⟩
  obtain ⟨A₁, _, _, _, _, _, _, i₁, EA₁, _, _, _, _, _, QA₁, _, jA₁, ψA₁, DA₁, _, _, act₁, hF₁,
    ⟨ρ₁, hR₁, -⟩, β₁, h₁, hβ₁, hh₁⟩ := GlobalTheory.T.enlarge_strictHenselisation_retract_mod T O hT P φ hφ hsh hP q hq0 hqT A i EA QA jA ψA DA actA hF
  obtain ⟨A₂, _, _, _, _, _, _, i₂, EA₂, _, _, _, _, _, QA₂, _, jA₂, ψA₂, DA₂, _, _, act₂, hF₂,
    ⟨ρ₂, hR₂, hpt₂⟩, β₂, h₂, hβ₂, hh₂⟩ :=
    GlobalTheory.T.enlarge_base_separable_point_integralClosure T O hT P φ hφ hsh hP q hq0 hqT A₁ i₁ EA₁ QA₁ jA₁ ψA₁ DA₁ act₁ hF₁ ρ₁ hR₁
  obtain ⟨A₃, _, _, _, _, _, _, i₃, EA₃, _, _, _, _, _, QA₃, _, jA₃, ψA₃, DA₃, _, _, act₃, hF₃,
    ⟨ρ₃, hR₃, hgood⟩, β₃, h₃, hβ₃, hh₃⟩ :=
    GlobalTheory.T.etale_enlarge_by_uniformiser_roots T O hT P φ hφ hsh hP q hq0 hqT A₂ i₂ EA₂ QA₂ jA₂ ψA₂ DA₂ act₂ hF₂ ρ₂ hR₂ hpt₂
  refine ⟨A₃, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    EA₃, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, QA₃, inferInstance,
    hF₃.2.2.2.1, hF₃.2.2.1, ρ₃, hR₃.1, hR₃.2.1, jA₃, ψA₃, hF₃.2.2.2.2.2.1, DA₃, inferInstance,
    inferInstance, act₃, hF₃.2.2.2.2.2.2, hgood, β₃.comp (β₂.comp β₁), h₃.comp (h₂.comp h₁), ?_, ?_⟩
  · ext x
    have a1 := RingHom.congr_fun hβ₁ x
    have a2 := RingHom.congr_fun hβ₂ (β₁ x)
    have a3 := RingHom.congr_fun hβ₃ (β₂ (β₁ x))
    simp only [RingHom.comp_apply] at a1 a2 a3 ⊢
    rw [a3, a2, a1]
  · ext x
    have a1 := RingHom.congr_fun hh₁ x
    have a2 := RingHom.congr_fun hh₂ (β₁ x)
    have a3 := RingHom.congr_fun hh₃ (β₂ (β₁ x))
    simp only [RingHom.comp_apply] at a1 a2 a3 ⊢
    rw [a1, a2, a3]

end GlobalTheory.KeyOriginEnlarge
