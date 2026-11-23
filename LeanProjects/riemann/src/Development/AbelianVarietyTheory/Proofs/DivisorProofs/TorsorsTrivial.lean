import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.CMModuli.ProjectiveSpaceOverSpec

open scoped TensorProduct
open IsLocalRing Polynomial

noncomputable section

namespace GlobalTheory.LocAcyc

abbrev GenFib (T O : Type) [CommRing T] [CommRing O] [Algebra T O] : Type :=
  Localization (Algebra.algebraMapSubmonoid O (nonZeroDivisors T))

def TorsorsTrivial (B : Type) [CommRing B] (q : ℕ) : Prop :=
  ∀ (D : Type) [CommRing D] [Algebra B D], Module.Finite B D → Module.Projective B D →
    Module.FaithfullyFlat B D →
    ∀ act : Multiplicative (ZMod q) →* (D ≃ₐ[B] D),
    Function.Bijective (Algebra.TensorProduct.productMap
      (Pi.algHom B (fun _ : Multiplicative (ZMod q) => D) (fun _ => AlgHom.id B D))
      (Pi.algHom B (fun _ : Multiplicative (ZMod q) => D) (fun g => (act g).toAlgHom))) →
    Nonempty (D →ₐ[B] B)

def AbsIntClosed (T : Type) [CommRing T] : Prop :=
  ∀ f : Polynomial T, f.Monic → 0 < f.natDegree → ∃ x : T, f.eval x = 0

def KeyAll : Prop :=
  ∀ (T O : Type) [CommRing T] [IsDomain T] [CommRing O] [IsLocalRing O] [Algebra T O]
    [Algebra (Polynomial T) O] [IsScalarTower T (Polynomial T) O], AbsIntClosed T →
    ∀ (P : Ideal (Polynomial T)) [P.IsPrime] (φ : Localization.AtPrime P →+* O),
    φ.comp (algebraMap (Polynomial T) _) = algebraMap (Polynomial T) O →
    GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec.IsStrictHenselisation φ →
    ∀ (q : ℕ), 0 < q → IsUnit (q : T) → TorsorsTrivial (GenFib T O) q

def KeyLocalWith (S : ∀ (T : Type) [CommRing T] [IsLocalRing T], Ideal (Polynomial T) → Prop) : Prop :=
  ∀ (T O : Type) [CommRing T] [IsDomain T] [IsLocalRing T] [CommRing O] [IsLocalRing O] [Algebra T O]
    [Algebra (Polynomial T) O] [IsScalarTower T (Polynomial T) O], AbsIntClosed T →
    ∀ (P : Ideal (Polynomial T)) [P.IsPrime] (φ : Localization.AtPrime P →+* O),
    φ.comp (algebraMap (Polynomial T) _) = algebraMap (Polynomial T) O →
    GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec.IsStrictHenselisation φ →
    P.comap (Polynomial.C : T →+* Polynomial T) = maximalIdeal T → S T P →
    ∀ (q : ℕ), 0 < q → IsUnit (q : T) → TorsorsTrivial (GenFib T O) q

def KeyLocal : Prop := KeyLocalWith (fun _ _ _ _ => True)

def KeyGeneric : Prop :=
  KeyLocalWith (fun T _ _ P => P = (maximalIdeal T).map (Polynomial.C : T →+* Polynomial T))

def KeyClosedPts : Prop :=
  KeyLocalWith (fun T _ _ P => P ≠ (maximalIdeal T).map (Polynomial.C : T →+* Polynomial T))

def KeyOrigin : Prop :=
  KeyLocalWith (fun T _ _ P =>
    P = (maximalIdeal T).map (Polynomial.C : T →+* Polynomial T) ⊔ Ideal.span {Polynomial.X})

end GlobalTheory.LocAcyc
