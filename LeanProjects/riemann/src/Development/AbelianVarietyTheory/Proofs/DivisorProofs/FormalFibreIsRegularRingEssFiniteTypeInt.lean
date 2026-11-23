import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormalFibreIsRegularRingOfEssFiniteTypeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdicCompletionTensorQuotientRingEquivStatement
open IsLocalRing TensorProduct

namespace GlobalTheory

theorem perfectField_fractionRing_zmod (p : ℕ) [Fact p.Prime] :
    PerfectField (FractionRing (ZMod p)) :=
  PerfectField.of_ringEquiv (FractionRing.algEquiv (ZMod p) (ZMod p)).symm.toRingEquiv

theorem formalFibre_isRegularRing_of_essFiniteType_int :
    ∀ (R K : Type) [CommRing R] [IsLocalRing R] [Algebra.EssFiniteType ℤ R] [Field K] [Algebra R K]
      [Algebra.EssFiniteType R K], IsRegularRing (AdicCompletion (maximalIdeal R) R ⊗[R] K) := by
  intro R K _ _ _ _ _ _
  rcases CharP.char_is_prime_or_zero K (ringChar K) with hp | h0
  ·
    set p := ringChar K with hpdef
    haveI : Fact p.Prime := ⟨hp⟩
    haveI : IsNoetherianRing R := Algebra.EssFiniteType.isNoetherianRing ℤ R
    have hpK : algebraMap R K (p : R) = 0 := by
      rw [map_natCast]; exact CharP.cast_eq_zero K p
    have hnu : ((p : ℕ) : R) ∈ nonunits R := fun hu => by
      have := hu.map (algebraMap R K); rw [hpK] at this; exact not_isUnit_zero this
    let I : Ideal R := Ideal.span {((p : ℕ) : R)}
    haveI : CharP (R ⧸ I) p := CharP.quotient R p hnu
    have hI : I ≠ ⊤ := by
      exact fun h => hnu (Ideal.span_singleton_eq_top.mp h)
    haveI : Nontrivial (R ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr hI
    haveI : IsLocalRing (R ⧸ I) :=
      IsLocalRing.of_surjective' (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
    have hker : I ≤ RingHom.ker (algebraMap R K) := by
      rw [Ideal.span_le, Set.singleton_subset_iff]; exact hpK
    letI : Algebra (R ⧸ I) K := (Ideal.Quotient.lift I (algebraMap R K) hker).toAlgebra
    haveI : IsScalarTower R (R ⧸ I) K := IsScalarTower.of_algebraMap_eq fun x => rfl
    haveI : Algebra.EssFiniteType R (R ⧸ I) :=
      Algebra.EssFiniteType.of_surjective (Ideal.Quotient.mkₐ R I) Ideal.Quotient.mk_surjective
    haveI : Algebra.EssFiniteType ℤ (R ⧸ I) := Algebra.EssFiniteType.comp ℤ R (R ⧸ I)
    letI : Algebra (ZMod p) (R ⧸ I) := ZMod.algebra (R ⧸ I) p
    haveI : Algebra.EssFiniteType (ZMod p) (R ⧸ I) := Algebra.EssFiniteType.of_comp ℤ (ZMod p) (R ⧸ I)
    haveI : Algebra.EssFiniteType (R ⧸ I) K := Algebra.EssFiniteType.of_comp R (R ⧸ I) K
    haveI := perfectField_fractionRing_zmod p
    have hinj : ∀ a : ZMod p, algebraMap (R ⧸ I) K (algebraMap (ZMod p) (R ⧸ I) a) = 0 → a = 0 :=
      fun a ha => ((algebraMap (R ⧸ I) K).comp (algebraMap (ZMod p) (R ⧸ I))).injective
        (by simpa using ha)
    have hreg := GlobalTheory.T.isRegularRing_formalFibre_of_essFiniteType (ZMod p) (R ⧸ I) K hinj
    obtain ⟨e⟩ := GlobalTheory.T.nonempty_adicCompletion_tensor_ringEquiv_of_surjective R (R ⧸ I) K Ideal.Quotient.mk_surjective
    exact IsRegularRing.of_ringEquiv e
  ·
    haveI : CharP K 0 := by rw [← h0]; exact ringChar.charP K
    haveI : CharZero K := CharP.charP_to_charZero K
    refine GlobalTheory.T.isRegularRing_formalFibre_of_essFiniteType ℤ R K ?_
    intro a ha
    rw [eq_intCast (algebraMap ℤ R), map_intCast] at ha
    exact_mod_cast ha

end GlobalTheory
