import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KrullDimQuotientMinimalPrimeOverL
import ReciprocityTheory.AnalyticForms.RegularLocalRings.IntToRatA

namespace GlobalTheory.IntFiniteTypeDim

theorem exists_natPrime_mem_of_isMaximal (A : Type) [CommRing A] [Algebra.FiniteType ℤ A]
    (m : Ideal A) [m.IsMaximal] : ∃ l : ℕ, l.Prime ∧ (l : A) ∈ m := by
  haveI := ReciprocityTheory.AnForm.R.IntegerToRational.isJacobsonRing_int
  letI := Ideal.Quotient.field m
  have hfin : Module.Finite ℤ (A ⧸ m) := finite_of_finite_type_of_isJacobsonRing ℤ (A ⧸ m)
  obtain ⟨p, hp⟩ := CharP.exists (A ⧸ m)
  rcases CharP.char_is_prime_or_zero (A ⧸ m) p with h | h
  · refine ⟨p, h, ?_⟩
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast]
    exact CharP.cast_eq_zero _ p
  · subst h
    haveI : CharZero (A ⧸ m) := CharP.charP_to_charZero _
    exfalso
    have hinj : Function.Injective (algebraMap ℤ (A ⧸ m)) :=
      RingHom.injective_int _
    exact Int.not_isField
      ((Algebra.IsIntegral.isField_iff_isField hinj).mpr (Field.toIsField (A ⧸ m)))

theorem ringKrullDim_quotient_le_of_minimalPrimes {A : Type} [CommRing A] (I : Ideal A)
    (c : WithBot ℕ∞) (h : ∀ P ∈ I.minimalPrimes, ringKrullDim (A ⧸ P) ≤ c) :
    ringKrullDim (A ⧸ I) ≤ c := by
  rw [ringKrullDim_quotient]
  refine iSup_le fun s => ?_
  obtain ⟨P, hP, hle⟩ := Ideal.exists_minimalPrimes_le (I := I) (J := s.head.1.asIdeal) s.head.2
  refine le_trans ?_ (h P hP)
  rw [ringKrullDim_quotient]
  let t : LTSeries (PrimeSpectrum.zeroLocus (R := A) P) :=
    ⟨s.length, fun i => ⟨(s i).1, hle.trans (show s.head.1 ≤ (s i).1 from s.head_le i)⟩,
      fun i => s.step i⟩
  exact Order.LTSeries.length_le_krullDim t

theorem ringKrullDim_eq_trdeg_add_one :
    ∀ (A : Type) [CommRing A] [IsDomain A] [Algebra.FiniteType ℤ A],
      Function.Injective (algebraMap ℤ A) →
        ringKrullDim A = ((Cardinal.toENat (Algebra.trdeg ℤ A) + 1 : ℕ∞) : WithBot ℕ∞) := by
  intro A _ _ _ hinj
  haveI : CharZero A := charZero_of_injective_algebraMap hinj
  haveI : FaithfulSMul ℤ A := (faithfulSMul_iff_algebraMap_injective _ _).mpr hinj
  haveI : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing ℤ A
  obtain ⟨d, hd⟩ := Cardinal.lt_aleph0.mp (trdeg_lt_aleph0_of_finiteType (R := ℤ) (S := A))
  have hrhs : ((Cardinal.toENat (Algebra.trdeg ℤ A) + 1 : ℕ∞) : WithBot ℕ∞) =
      (d : WithBot ℕ∞) + 1 := by
    rw [hd, Cardinal.toENat_nat]; rfl
  rw [hrhs]
  apply le_antisymm
  · refine (ringKrullDim_le_iff_isMaximal_height_le _).mpr fun m hm => ?_
    obtain ⟨l, hl, hlm⟩ := exists_natPrime_mem_of_isMaximal A m
    haveI := Fact.mk hl
    refine (Ideal.height_le_ringKrullDim_quotient_add_one hlm).trans ?_
    gcongr
    refine ringKrullDim_quotient_le_of_minimalPrimes _ _ fun q hq => ?_
    haveI := hq.1.1
    exact (ringKrullDim_quotient_eq_trdeg_of_mem_minimalPrimes_natPrime A l q hq d hd).le
  · obtain ⟨m, hm⟩ := Ideal.exists_maximal A
    obtain ⟨l, hl, hlm⟩ := exists_natPrime_mem_of_isMaximal A m
    haveI := Fact.mk hl
    obtain ⟨q, hq, -⟩ := Ideal.exists_minimalPrimes_le (I := Ideal.span {(l : A)}) (J := m)
      ((Ideal.span_singleton_le_iff_mem _).mpr hlm)
    haveI := hq.1.1
    rw [← ringKrullDim_quotient_eq_trdeg_of_mem_minimalPrimes_natPrime A l q hq d hd]
    have hlq : (l : A) ∈ q := hq.1.2 (Ideal.mem_span_singleton_self _)
    exact ringKrullDim_succ_le_of_surjective (Ideal.Quotient.mk q) Ideal.Quotient.mk_surjective
      (r := (l : A)) (mem_nonZeroDivisors_of_ne_zero (Nat.cast_ne_zero.mpr hl.ne_zero))
      (Ideal.Quotient.eq_zero_iff_mem.mpr hlq)

end GlobalTheory.IntFiniteTypeDim
