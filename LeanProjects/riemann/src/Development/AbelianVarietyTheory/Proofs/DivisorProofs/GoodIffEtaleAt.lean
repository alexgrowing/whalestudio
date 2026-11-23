import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsorsTrivial
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OriginIdeal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClosureFiniteEtale
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PointAtZero

open IsLocalRing Polynomial

noncomputable section

namespace GlobalTheory.KeyOriginEnlarge

def ClosureEtaleAt (A R D : Type) [CommRing A] [CommRing R] [Algebra A R] [CommRing D]
    [Algebra (GlobalTheory.LocAcyc.GenFib A R) D] (P : Ideal R) [P.IsPrime] : Prop :=
  letI := GlobalTheory.KeyOriginNoeth.closureAlg A R D
  Algebra.Etale (Localization.AtPrime P)
    (TensorProduct R (Localization.AtPrime P) (GlobalTheory.KeyOriginNoeth.closure A R D))

theorem good_iff_etaleAt (A R D : Type) [CommRing A] [CommRing R] [Algebra A R] [CommRing D]
    [Algebra (GlobalTheory.LocAcyc.GenFib A R) D] (ρ : R →+* A) :
    GlobalTheory.KeyOriginNoeth.Good A R D ρ ↔
      ((∀ (P : Ideal R) [P.IsPrime], (P.comap (algebraMap A R)).height ≤ 1 →
          ClosureEtaleAt A R D P) ∧ PointAtZero A R D ρ) := Iff.rfl

end GlobalTheory.KeyOriginEnlarge
