import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsorsTrivial
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OriginIdeal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClosureFiniteEtale
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PointAtZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ZmodTorsorExistsPointFiniteSeparableStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNormalLocalBetweenStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBaseChangeFittingDatumRetractionStatement
open IsLocalRing Polynomial

noncomputable section

namespace GlobalTheory.KeyOriginEnlargePoint

theorem enlarge_point : ∀ (T O : Type) [CommRing T] [IsDomain T] [IsLocalRing T] [CommRing O] [IsLocalRing O] [Algebra T O]
    [Algebra (Polynomial T) O] [IsScalarTower T (Polynomial T) O], GlobalTheory.LocAcyc.AbsIntClosed T →
    ∀ (P : Ideal (Polynomial T)) [P.IsPrime] (φ : Localization.AtPrime P →+* O),
    φ.comp (algebraMap (Polynomial T) _) = algebraMap (Polynomial T) O →
    GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec.IsStrictHenselisation φ → P = GlobalTheory.KeyOriginCut.originIdeal T →
    ∀ (q : ℕ), 0 < q → IsUnit (q : T) →
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
    ∃ (A' : Type) (_ : CommRing A') (_ : IsDomain A') (_ : IsLocalRing A') (_ : IsNoetherianRing A')
      (_ : IsIntegrallyClosed A') (_ : Algebra.EssFiniteType ℤ A') (i' : A' →+* T)
      (EA' : Type) (_ : CommRing EA') (_ : Algebra (Polynomial A') EA') (_ : Algebra A' EA')
      (_ : IsScalarTower A' (Polynomial A') EA') (_ : Algebra.Etale (Polynomial A') EA')
      (QA' : Ideal EA') (_ : QA'.IsPrime) (jA' : Localization.AtPrime QA' →+* O)
      (ψA' : GlobalTheory.LocAcyc.GenFib A' (Localization.AtPrime QA') →+* GlobalTheory.LocAcyc.GenFib T O)
      (DA' : Type) (_ : CommRing DA') (_ : Algebra (GlobalTheory.LocAcyc.GenFib A' (Localization.AtPrime QA')) DA')
      (actA' : Multiplicative (ZMod q) →* (DA' ≃ₐ[GlobalTheory.LocAcyc.GenFib A' (Localization.AtPrime QA')] DA')),
      GlobalTheory.KeyOriginEnlarge.Fits T O q A' i' EA' QA' jA' ψA' DA' actA' ∧
      (∃ ρ' : Localization.AtPrime QA' →+* A',
        GlobalTheory.KeyOriginEnlarge.Retracts T O A' i' EA' QA' jA' ρ' ∧ GlobalTheory.KeyOriginEnlarge.PointAtZero A' (Localization.AtPrime QA') DA' ρ') ∧
      ∃ (β : GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA) →+* GlobalTheory.LocAcyc.GenFib A' (Localization.AtPrime QA')) (h : DA →+* DA'),
        ψA'.comp β = ψA ∧
        h.comp (algebraMap (GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA)) DA) = (algebraMap (GlobalTheory.LocAcyc.GenFib A' (Localization.AtPrime QA')) DA').comp β := by
  intro T O _ _ _ _ _ _ _ _ hAIC P _ φ hφ hSH hP q hq hqT A _ _ _ _ _ _ i EA _ _ _ _ _ QA _ jA ψA DA _ _ actA hFits ρ hRet
  obtain ⟨hi, _hil, _hqA, _hQA, _hjA, _hψA, hTor⟩ := hFits
  have hu : ∀ y : Algebra.algebraMapSubmonoid (Localization.AtPrime QA) (nonZeroDivisors A),
      IsUnit (((algebraMap A (FractionRing A)).comp ρ) (y : Localization.AtPrime QA)) := by
    rintro ⟨y, a, ha, rfl⟩
    have h1 : ρ (algebraMap A (Localization.AtPrime QA) a) = a := by
      simpa using congrArg (fun f => f a) hRet.1
    simp only [RingHom.comp_apply, h1]
    exact IsLocalization.map_units (FractionRing A) (⟨a, ha⟩ : nonZeroDivisors A)
  let ρK : GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA) →+* FractionRing A := IsLocalization.lift hu
  have hρK : ρK.comp (algebraMap (Localization.AtPrime QA) (GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA))) =
      (algebraMap A (FractionRing A)).comp ρ := IsLocalization.lift_comp hu
  obtain ⟨L, _, _, _, _, σL, hσL⟩ := GlobalTheory.T.zmodTorsor_exists_point_finite_separable _ (FractionRing A) ρK DA q hq actA hTor
  obtain ⟨A₁, _, _, _, _, _, _, j, i₁, hj, hi₁, hl₁, hji, κ, hκ⟩ := GlobalTheory.T.exists_normal_local_between_alt T hAIC A i hi L
  obtain ⟨EA₁, _, _, _, _, _, QA₁, _, jA₁, ψA₁, DA₁, _, _, actA₁, ρ₁, hF₁, hR₁, β, h, hβ, hh, hσ⟩ :=
    GlobalTheory.T.exists_baseChange_fittingDatum_retraction T O P φ hφ hSH hP q hq A i EA QA jA ψA DA actA ⟨hi, _hil, _hqA, _hQA, _hjA, _hψA, hTor⟩ ρ hRet
      A₁ j i₁ hj hi₁ hl₁ hji
  obtain ⟨σ₁, hσ₁⟩ := hσ (κ.comp σL) (by
    ext x
    have h1 := congrArg (fun f => f (algebraMap (Localization.AtPrime QA)
      (GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA)) x)) hσL
    have h2 := congrArg (fun f => f x) hρK
    have h3 := congrArg (fun f => f (ρ x)) hκ
    simp only [RingHom.comp_apply] at h1 h2 h3 ⊢
    rw [h1, h2, h3])
  refine ⟨A₁, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, i₁,
    EA₁, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, QA₁, inferInstance, jA₁, ψA₁,
    DA₁, inferInstance, inferInstance, actA₁, hF₁, ⟨ρ₁, hR₁, ?_⟩, β, h, hβ, hh⟩
  letI := GlobalTheory.KeyOriginNoeth.closureAlg A₁ (Localization.AtPrime QA₁) DA₁
  refine ⟨σ₁.comp (GlobalTheory.KeyOriginNoeth.closure A₁ (Localization.AtPrime QA₁) DA₁).subtype, ?_⟩
  ext r
  exact congrArg (fun f => f r) hσ₁

end GlobalTheory.KeyOriginEnlargePoint
