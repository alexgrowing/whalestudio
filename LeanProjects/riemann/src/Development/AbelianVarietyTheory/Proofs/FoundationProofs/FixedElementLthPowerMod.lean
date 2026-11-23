import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MemCycAlgOfPow
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.VanishOrdOfKatoUseN
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.InertiaFixedValuationEqZpowPrimeRatAlgClosure
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PowFixedOfAlgebraic

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.RecOne GlobalTheory.AlmostEt
open scoped Matrix NNReal

namespace GlobalTheory.RecOne

open Polynomial IsLocalRing

theorem exists_residue_pow_pow_eq (l : ℕ) [Fact l.Prime] {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω]
    (A : ValuationSubring Ω) (hl1 : A.valuation (l : Ω) < 1) (xA : A) :
    ∃ N : ℕ, 0 < N ∧ residue A xA ^ (l ^ N) = residue A xA := by
  first
  | exact @_root_.GlobalTheory.ResiduePowerFixed.residue_pow_fixed
  | exact _root_.GlobalTheory.ResiduePowerFixed.residue_pow_fixed
  | (apply _root_.GlobalTheory.ResiduePowerFixed.residue_pow_fixed <;> assumption)
  | (intros; apply _root_.GlobalTheory.ResiduePowerFixed.residue_pow_fixed <;> assumption)
  | (intros; apply @_root_.GlobalTheory.ResiduePowerFixed.residue_pow_fixed <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.ResiduePowerFixed.residue_pow_fixed ..)

theorem fixA_eq_pow_add_mul : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω]
    (A : ValuationSubring Ω), OverL l A → ∀ a : fixA A, ∃ (b : fixA A) (z : A), (a : A) = (b : A) ^ l + (l : A) * z := by
  intro l _ Ω _ _ _ A hO a
  have hl : l.Prime := Fact.out
  haveI : CharZero Ω := algebraRat.charZero Ω
  have hl1 : A.valuation (l : Ω) < 1 := GlobalTheory.Ord2.VanishNarrow.valuation_lt_one hO
  obtain ⟨N, hN, hr⟩ := exists_residue_pow_pow_eq l A hl1 (a : A)
  refine ⟨a ^ (l ^ (N - 1)), ?_⟩
  have hb : ((a ^ (l ^ (N - 1)) : fixA A) : A) ^ l = (a : A) ^ (l ^ N) := by
    rw [SubmonoidClass.coe_pow, ← pow_mul, ← pow_succ, Nat.sub_add_cancel hN]
  rw [hb]
  set cA : A := (a : A) - (a : A) ^ (l ^ N) with hcA
  have hcfix : cA ∈ fixA A := (fixA A).sub_mem a.2 ((fixA A).pow_mem a.2 _)
  have hcm : cA ∈ maximalIdeal A := by
    rw [← residue_eq_zero_iff, hcA, map_sub, map_pow, hr, sub_self]
  have hcv : A.valuation (cA : Ω) < 1 := by
    have := (A.valuation_lt_one_iff _).1 hcm
    simpa using this
  suffices h : ∃ z : A, cA = (l : A) * z by
    obtain ⟨z, hz⟩ := h
    refine ⟨z, ?_⟩
    rw [← hz, hcA]
    ring
  have hl0 : (l : Ω) ≠ 0 := Nat.cast_ne_zero.2 hl.ne_zero
  have hvl0 : A.valuation (l : Ω) ≠ 0 := (_root_.map_ne_zero _).2 hl0
  by_cases hc0 : (cA : Ω) = 0
  · exact ⟨0, by rw [mul_zero]; exact Subtype.ext hc0⟩
  obtain ⟨k, hk⟩ := GlobalTheory.InertiaFixedValue.valuation_eq_zpow_of_ine_fixed l Ω A hO (cA : Ω) hc0 (mem_fixA.1 hcfix)
  obtain ⟨n, rfl | rfl⟩ := Int.eq_nat_or_neg k
  · rw [zpow_natCast] at hk
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · rw [pow_zero] at hk; exact absurd hk hcv.ne
    have hz : A.valuation ((cA : Ω) / (l : Ω)) ≤ 1 := by
      rw [map_div₀, hk, ← Nat.sub_add_cancel hn, pow_succ, mul_div_assoc, div_self hvl0, mul_one]
      exact pow_le_one' hl1.le _
    refine ⟨⟨(cA : Ω) / (l : Ω), (A.valuation_le_one_iff _).1 hz⟩, Subtype.ext ?_⟩
    change (cA : Ω) = (l : Ω) * ((cA : Ω) / (l : Ω))
    rw [mul_div_cancel₀ _ hl0]
  · exfalso
    rw [zpow_neg, zpow_natCast] at hk
    have e : A.valuation (cA : Ω) * A.valuation (l : Ω) ^ n = 1 := by
      rw [hk, inv_mul_cancel₀ (pow_ne_zero _ hvl0)]
    have : A.valuation (cA : Ω) * A.valuation (l : Ω) ^ n ≤ A.valuation (cA : Ω) :=
      mul_le_of_le_one_right' (pow_le_one' hl1.le _)
    rw [e] at this
    exact absurd hcv (not_lt.2 this)

end GlobalTheory.RecOne
