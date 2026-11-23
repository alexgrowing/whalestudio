import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StFlatNormalFibres
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open IsLocalRing RingTheory.Sequence

def SerreRAt (B : Type*) [CommRing B] (k : ℕ) : Prop :=
  ringKrullDim B ≤ (k : WithBot ℕ∞) → IsRegularLocalRing B

def SerreSAt (B : Type*) [CommRing B] [IsLocalRing B] (k : ℕ) : Prop :=
  ∃ rs : List B, (∀ r ∈ rs, r ∈ maximalIdeal B) ∧ IsWeaklyRegular B rs ∧
    min (k : WithBot ℕ∞) (ringKrullDim B) ≤ (rs.length : WithBot ℕ∞)

def SerreR (A : Type*) [CommRing A] (k : ℕ) : Prop :=
  ∀ (P : Ideal A) [P.IsPrime], SerreRAt (Localization.AtPrime P) k

def SerreS (A : Type*) [CommRing A] (k : ℕ) : Prop :=
  ∀ (P : Ideal A) [P.IsPrime], SerreSAt (Localization.AtPrime P) k

def NormalRing (A : Type*) [CommRing A] : Prop :=
  ∀ (P : Ideal A) [P.IsPrime], IsDomain (Localization.AtPrime P) ∧ IsIntegrallyClosed (Localization.AtPrime P)

theorem primeFibreLocalRing_ideal_ne_top (R : Type*) {S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    (P : Ideal S) [P.IsPrime] :
    Ideal.map (algebraMap S (Localization.AtPrime P))
      (Ideal.map (algebraMap R S) (Ideal.comap (algebraMap R S) P)) ≠ ⊤ := by
  intro h
  have hle : Ideal.map (algebraMap S (Localization.AtPrime P))
      (Ideal.map (algebraMap R S) (Ideal.comap (algebraMap R S) P)) ≤ maximalIdeal (Localization.AtPrime P) := by
    rw [← Localization.AtPrime.map_eq_maximalIdeal]
    exact Ideal.map_mono Ideal.map_comap_le
  exact (maximalIdeal.isMaximal _).ne_top (top_le_iff.mp (h ▸ hle))

instance primeFibreLocalRing.isLocalRing (R : Type*) {S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    (P : Ideal S) [P.IsPrime] : IsLocalRing (primeFibreLocalRing R P) := by
  have : Nontrivial (primeFibreLocalRing R P) :=
    Ideal.Quotient.nontrivial_iff.mpr (primeFibreLocalRing_ideal_ne_top R P)
  exact IsLocalRing.of_surjective' (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective

noncomputable def localizationAtPrimeComplexEquiv (P : Ideal ℂ) [P.IsPrime] :
    Localization.AtPrime P ≃+* ℂ := by
  have hP : P = ⊥ := (Ideal.eq_bot_or_top P).resolve_right (Ideal.IsPrime.ne_top ‹_›)
  exact (IsLocalization.atUnits ℂ P.primeCompl (fun x hx => by
    subst hP
    exact isUnit_iff_ne_zero.2 (by simpa using hx))).toRingEquiv.symm

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
