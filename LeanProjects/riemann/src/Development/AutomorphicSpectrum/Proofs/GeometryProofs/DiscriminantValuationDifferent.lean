import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.PadicValNatAbsNormEqZero

open NumberField IsDedekindDomain UniqueFactorizationMonoid

namespace GlobalTheory.CompanionTheory.Different

theorem padicValInt_discr_mul_count_eq :
    ∀ (E : Type) [Field E] [NumberField E] [IsGalois ℚ E] (p : ℕ) [Fact p.Prime] (P : Ideal (𝓞 E)),
      P.IsPrime → (p : 𝓞 E) ∈ P →
      ((padicValInt p (discr E) : ℕ)) * (normalizedFactors (Ideal.span {(p : 𝓞 E)})).count P =
        (normalizedFactors (differentIdeal ℤ (𝓞 E))).count P * Module.finrank ℚ E := by
  intro E _ _ _ p hp P hP hpP
  have hd : (discr E).natAbs ≠ 0 := Int.natAbs_ne_zero.2 (discr_ne_zero E)
  have hdecomp : (discr E).natAbs =
      p ^ padicValNat p (discr E).natAbs * ((discr E).natAbs / p ^ (discr E).natAbs.factorization p) := by
    conv_lhs => rw [← Nat.ordProj_mul_ordCompl_eq_self (discr E).natAbs p]
    rw [Nat.factorization_def _ hp.out]
  have hnd : ¬ p ∣ (discr E).natAbs / p ^ (discr E).natAbs.factorization p :=
    Nat.not_dvd_ordCompl hp.out hd
  have h := ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.diffExp E p _ _ hp.out hnd hdecomp P hP hpP
  rw [h]
  rfl

end GlobalTheory.CompanionTheory.Different
