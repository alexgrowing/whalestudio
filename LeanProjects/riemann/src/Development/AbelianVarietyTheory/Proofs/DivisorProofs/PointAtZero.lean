import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsorsTrivial
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OriginIdeal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClosureFiniteEtale

open IsLocalRing Polynomial

noncomputable section

namespace GlobalTheory.KeyOriginEnlarge

def Fits (T O : Type) [CommRing T] [CommRing O] [Algebra T O] [Algebra (Polynomial T) O]
    (q : ℕ) (A : Type) [CommRing A] [IsLocalRing A] (i : A →+* T)
    (EA : Type) [CommRing EA] [Algebra (Polynomial A) EA] [Algebra A EA]
    (QA : Ideal EA) [QA.IsPrime] (jA : Localization.AtPrime QA →+* O)
    (ψA : GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA) →+* GlobalTheory.LocAcyc.GenFib T O)
    (DA : Type) [CommRing DA] [Algebra (GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA)) DA]
    (actA : Multiplicative (ZMod q) →* (DA ≃ₐ[GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA)] DA)) :
    Prop :=
  Function.Injective i ∧ IsLocalHom i ∧ IsUnit (q : A) ∧
    QA.comap (algebraMap (Polynomial A) EA) = GlobalTheory.KeyOriginCut.originIdeal A ∧
    jA.comp (algebraMap (Polynomial A) (Localization.AtPrime QA)) =
      (algebraMap (Polynomial T) O).comp (Polynomial.mapRingHom i) ∧
    ψA.comp (algebraMap (Localization.AtPrime QA) (GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA))) =
      (algebraMap O (GlobalTheory.LocAcyc.GenFib T O)).comp jA ∧
    GlobalTheory.KeyOriginCut.IsZTorsor (GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA)) DA q actA

def Retracts (T O : Type) [CommRing T] [CommRing O] [Algebra T O] [Algebra (Polynomial T) O]
    (A : Type) [CommRing A] (i : A →+* T)
    (EA : Type) [CommRing EA] [Algebra (Polynomial A) EA] [Algebra A EA]
    (QA : Ideal EA) [QA.IsPrime] (jA : Localization.AtPrime QA →+* O)
    (ρ : Localization.AtPrime QA →+* A) : Prop :=
  ρ.comp (algebraMap A (Localization.AtPrime QA)) = RingHom.id A ∧
    RingHom.ker ρ = Ideal.span {algebraMap (Polynomial A) (Localization.AtPrime QA) Polynomial.X} ∧
    ∀ x : Localization.AtPrime QA,
      algebraMap T O (i (ρ x)) - jA x ∈ Ideal.span {algebraMap (Polynomial T) O Polynomial.X}

def PointAtZero (A R D : Type) [CommRing A] [CommRing R] [Algebra A R] [CommRing D]
    [Algebra (GlobalTheory.LocAcyc.GenFib A R) D] (ρ : R →+* A) : Prop :=
  letI := GlobalTheory.KeyOriginNoeth.closureAlg A R D
  ∃ s : GlobalTheory.KeyOriginNoeth.closure A R D →+* FractionRing A,
    s.comp (algebraMap R (GlobalTheory.KeyOriginNoeth.closure A R D)) = (algebraMap A (FractionRing A)).comp ρ

end GlobalTheory.KeyOriginEnlarge
