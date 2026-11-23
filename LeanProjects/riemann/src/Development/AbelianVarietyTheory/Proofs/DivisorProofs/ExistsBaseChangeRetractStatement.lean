import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBaseChangeRetract
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsorsTrivial
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OriginIdeal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClosureFiniteEtale
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PointAtZero
open IsLocalRing Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_baseChange_retract_alt : ∀ (T O : Type) [CommRing T] [IsDomain T] [IsLocalRing T] [CommRing O] [IsLocalRing O] [Algebra T O]
    [Algebra (Polynomial T) O] [IsScalarTower T (Polynomial T) O],
    IsLocalHom (algebraMap T O) → algebraMap (Polynomial T) O Polynomial.X ∈ maximalIdeal O →
    ∀ (A : Type) [CommRing A] [IsDomain A] [IsLocalRing A] [IsNoetherianRing A] (i : A →+* T)
      (EA : Type) [CommRing EA] [Algebra (Polynomial A) EA] [Algebra A EA]
      [IsScalarTower A (Polynomial A) EA] [Algebra.Etale (Polynomial A) EA]
      (QA : Ideal EA) [QA.IsPrime] (jA : Localization.AtPrime QA →+* O) (ρ : Localization.AtPrime QA →+* A),
    QA.comap (algebraMap (Polynomial A) EA) = GlobalTheory.KeyOriginCut.originIdeal A →
    jA.comp (algebraMap (Polynomial A) (Localization.AtPrime QA)) =
      (algebraMap (Polynomial T) O).comp (Polynomial.mapRingHom i) →
    GlobalTheory.KeyOriginEnlarge.Retracts T O A i EA QA jA ρ →
    ∀ (A₁ : Type) [CommRing A₁] [IsDomain A₁] [IsLocalRing A₁] (j : A →+* A₁) (i₁ : A₁ →+* T),
      Function.Injective i₁ → IsLocalHom i₁ → i₁.comp j = i →
    ∃ (EA₁ : Type) (_ : CommRing EA₁) (_ : Algebra (Polynomial A₁) EA₁) (_ : Algebra A₁ EA₁)
      (_ : IsScalarTower A₁ (Polynomial A₁) EA₁) (_ : Algebra.Etale (Polynomial A₁) EA₁)
      (QA₁ : Ideal EA₁) (_ : QA₁.IsPrime) (jA₁ : Localization.AtPrime QA₁ →+* O)
      (γ₀ : EA →+* EA₁) (γ : Localization.AtPrime QA →+* Localization.AtPrime QA₁) (ρ' : EA₁ →+* A₁),
      QA₁.comap (algebraMap (Polynomial A₁) EA₁) = GlobalTheory.KeyOriginCut.originIdeal A₁ ∧
      jA₁.comp (algebraMap (Polynomial A₁) (Localization.AtPrime QA₁)) =
        (algebraMap (Polynomial T) O).comp (Polynomial.mapRingHom i₁) ∧
      jA₁.comp γ = jA ∧
      γ.comp (algebraMap EA (Localization.AtPrime QA)) = (algebraMap EA₁ (Localization.AtPrime QA₁)).comp γ₀ ∧
      γ.comp (algebraMap A (Localization.AtPrime QA)) = (algebraMap A₁ (Localization.AtPrime QA₁)).comp j ∧
      ρ'.comp γ₀ = j.comp (ρ.comp (algebraMap EA (Localization.AtPrime QA))) ∧
      ρ'.comp (algebraMap A₁ EA₁) = RingHom.id A₁ ∧
      ρ' (algebraMap (Polynomial A₁) EA₁ Polynomial.X) = 0 ∧
      (∀ x : EA₁, algebraMap T O (i₁ (ρ' x)) - jA₁ (algebraMap EA₁ (Localization.AtPrime QA₁) x) ∈
        Ideal.span {algebraMap (Polynomial T) O Polynomial.X}) ∧
      (∀ x : EA₁, ρ' x = 0 → ∃ s ∉ QA₁, s * x ∈ Ideal.span {algebraMap (Polynomial A₁) EA₁ Polynomial.X}) := by
  first | (exact @GlobalTheory.KeyOriginBaseChangeCons.exists_baseChange_retract) | (exact GlobalTheory.KeyOriginBaseChangeCons.exists_baseChange_retract) | (intros; apply GlobalTheory.KeyOriginBaseChangeCons.exists_baseChange_retract <;> assumption)
