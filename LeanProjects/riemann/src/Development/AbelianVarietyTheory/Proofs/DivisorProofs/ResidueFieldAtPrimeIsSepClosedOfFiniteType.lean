import Mathlib

namespace GlobalTheory

theorem residueField_localization_atPrime_isSepClosed_of_finiteType :
    ∀ (k B : Type) [Field k] [IsAlgClosed k] [CommRing B] [Algebra k B] [Algebra.FiniteType k B]
      (P : Ideal B) [P.IsMaximal],
      IsSepClosed (IsLocalRing.ResidueField (Localization.AtPrime P)) := by
  intro k B _ _ _ _ _ P _
  letI : Field (B ⧸ P) := Ideal.Quotient.field P
  haveI : Module.Finite k (B ⧸ P) := finite_of_finite_type_of_isJacobsonRing k (B ⧸ P)
  haveI : Algebra.IsIntegral k (B ⧸ P) := inferInstance
  let f : k ≃+* (B ⧸ P) := RingEquiv.ofBijective (algebraMap k (B ⧸ P))
    IsAlgClosed.algebraMap_bijective_of_isIntegral
  haveI : IsAlgClosed (B ⧸ P) := IsAlgClosed.of_ringEquiv k (B ⧸ P) f
  let e : (B ⧸ P) ≃+* IsLocalRing.ResidueField (Localization.AtPrime P) :=
    IsLocalization.AtPrime.equivQuotMaximalIdeal P (Localization.AtPrime P)
  haveI : IsAlgClosed (IsLocalRing.ResidueField (Localization.AtPrime P)) :=
    IsAlgClosed.of_ringEquiv _ _ e
  infer_instance

end GlobalTheory
