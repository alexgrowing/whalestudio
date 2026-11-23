import Mathlib

noncomputable section

namespace GlobalTheory.LocM.Lift

variable {R : Type} [CommRing R] [IsDomain R]

def locToFrac (P : Ideal R) [P.IsPrime] : Localization.AtPrime P →+* FractionRing R :=
  (Localization.mapToFractionRing (FractionRing R) P.primeCompl (Localization.AtPrime P)
    (Ideal.primeCompl_le_nonZeroDivisors P)).toRingHom

theorem locToFrac_algebraMap (P : Ideal R) [P.IsPrime] (r : R) :
    locToFrac P (algebraMap R (Localization.AtPrime P) r) = algebraMap R (FractionRing R) r :=
  AlgHom.commutes _ r

end GlobalTheory.LocM.Lift
