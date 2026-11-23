import Mathlib
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

abbrev primeFibreLocalRing (R : Type*) {S : Type*} [CommRing R] [CommRing S] [Algebra R S] (P : Ideal S)
    [P.IsPrime] : Type _ :=
  Localization.AtPrime P ⧸
    Ideal.map (algebraMap S (Localization.AtPrime P)) (Ideal.map (algebraMap R S) (Ideal.comap (algebraMap R S) P))

def FlatNormalFibres.Statement : Prop :=
  ∀ (R S : Type) [CommRing R] [CommRing S] [Algebra R S],
    IsNoetherianRing R → IsNoetherianRing S → IsLocalRing S → Module.Flat R S →
      IsDomain R → IsIntegrallyClosed R →
      (∀ (P : Ideal S) [P.IsPrime],
        IsDomain (primeFibreLocalRing R P) ∧ IsIntegrallyClosed (primeFibreLocalRing R P)) →
        IsDomain S ∧ IsIntegrallyClosed S

noncomputable def primeFibreLocalRing_complex_equiv (P : Ideal ℂ) [P.IsPrime] :
    primeFibreLocalRing ℂ P ≃+* ℂ := by
  have hP : P = ⊥ := (Ideal.eq_bot_or_top P).resolve_right (Ideal.IsPrime.ne_top ‹_›)
  have hmap : Ideal.map (algebraMap ℂ (Localization.AtPrime P))
      (Ideal.map (algebraMap ℂ ℂ) (Ideal.comap (algebraMap ℂ ℂ) P)) = ⊥ := by
    subst hP
    simp
  refine (Ideal.quotEquivOfEq hmap).trans (RingEquiv.quotientBot _) |>.trans ?_
  exact (IsLocalization.atUnits ℂ P.primeCompl (fun x hx => by
    subst hP
    exact isUnit_iff_ne_zero.2 (by simpa using hx))).toRingEquiv.symm

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
