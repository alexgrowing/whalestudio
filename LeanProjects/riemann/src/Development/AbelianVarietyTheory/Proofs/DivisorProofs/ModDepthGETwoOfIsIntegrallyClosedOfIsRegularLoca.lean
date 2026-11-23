import Mathlib
import ReciprocityTheory.CommutativeAlgebra.CohenMacaulay.ModDepthGE
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PurityFree
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.MemRangeOfForallHeightEqOneOfIsReflexive
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RegularLocalRingNormalDomain
open IsLocalRing

namespace GlobalTheory

theorem exists_isPrime_ne_bot_lt_maximalIdeal_of_two_le_ringKrullDim (R : Type) [CommRing R]
    [IsLocalRing R] (h : 2 ≤ ringKrullDim R) :
    ∃ q : Ideal R, q.IsPrime ∧ q ≠ ⊥ ∧ q < maximalIdeal R := by
  obtain ⟨l, hl⟩ : ∃ l : LTSeries (PrimeSpectrum R), l.length = 2 :=
    Order.le_krullDim_iff.mp (by exact_mod_cast h)
  let i0 : Fin l.length := ⟨0, by omega⟩
  let i1 : Fin l.length := ⟨1, by omega⟩
  have h01 : l i0.succ = l i1.castSucc := congrArg l (Fin.ext rfl)
  have s0 := l.step i0
  have s1 := l.step i1
  rw [h01] at s0
  refine ⟨(l i1.castSucc).asIdeal, (l i1.castSucc).isPrime, ?_, ?_⟩
  · intro h0
    have : (l i0.castSucc).asIdeal < (l i1.castSucc).asIdeal := s0
    rw [h0] at this
    exact not_lt_bot this
  · exact lt_of_lt_of_le (show (l i1.castSucc).asIdeal < (l i1.succ).asIdeal from s1)
      (le_maximalIdeal (l i1.succ).isPrime.ne_top)

end GlobalTheory

namespace GlobalTheory

open Pointwise

theorem modDepthGE_two_of_isIntegrallyClosed_of_isRegularLocalRing :
    ∀ (R A : Type) [CommRing R] [IsRegularLocalRing R] [CommRing A] [IsDomain A]
      [IsIntegrallyClosed A] [Algebra R A] [Module.Finite R A] [FaithfulSMul R A],
      2 ≤ ringKrullDim R → ReciprocityTheory.CA.ModDepthGE R A 2 := by
  intro R A _ _ _ _ _ _ _ _ hdim
  obtain ⟨hRd, hRic⟩ := isDomain_and_isIntegrallyClosed_of_isRegularLocalRing R
  haveI : IsNoetherianRing A := isNoetherian_of_tower R inferInstance
  have hinj := FaithfulSMul.algebraMap_injective R A
  obtain ⟨q, hq, hq0, hqm⟩ := exists_isPrime_ne_bot_lt_maximalIdeal_of_two_le_ringKrullDim R hdim
  have hm0 : maximalIdeal R ≠ ⊥ := (bot_le.trans_lt hqm).ne'
  obtain ⟨x, hxm, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hm0
  have hx' : algebraMap R A x ≠ 0 := (map_ne_zero_iff _ hinj).mpr hx0
  have hreg : IsSMulRegular A x := by
    intro a b hab
    simp only [Algebra.smul_def] at hab
    exact mul_left_cancel₀ hx' hab

  have hmemx : ∀ a : A, a ∈ x • (⊤ : Submodule R A) ↔ a ∈ Ideal.span {algebraMap R A x} := by
    intro a
    rw [Submodule.mem_smul_pointwise_iff_exists, Ideal.mem_span_singleton']
    constructor
    · rintro ⟨b, -, rfl⟩
      exact ⟨b, by rw [Algebra.smul_def, mul_comm]⟩
    · rintro ⟨b, rfl⟩
      exact ⟨b, Submodule.mem_top, by rw [Algebra.smul_def, mul_comm]⟩

  obtain ⟨y, hym, hyreg⟩ : ∃ y ∈ maximalIdeal R, IsSMulRegular (QuotSMulTop x A) y := by
    by_contra hno
    push_neg at hno
    have hfin := associatedPrimes.finite R (QuotSMulTop x A)
    have hsub : (maximalIdeal R : Set R) ⊆
        ⋃ p ∈ associatedPrimes R (QuotSMulTop x A), (p : Set R) := by
      intro y hy
      rw [biUnion_associatedPrimes_eq_compl_regular]
      exact hno y hy
    obtain ⟨p, hp, hmp⟩ := (Ideal.subset_union_prime (s := hfin.toFinset) (f := id) ⊥ ⊥
      (fun p hp _ _ => (hfin.mem_toFinset.mp hp).isPrime)).mp (by simpa using hsub)
    rw [hfin.mem_toFinset] at hp
    have hpm : p = maximalIdeal R :=
      (le_antisymm (le_maximalIdeal (hp.isPrime.ne_top)) hmp)
    rw [hpm] at hp
    obtain ⟨-, w, hw⟩ := isAssociatedPrime_iff.mp hp
    obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ w
    have hmz : ∀ a ∈ maximalIdeal R, algebraMap R A a * z ∈ Ideal.span {algebraMap R A x} := by
      intro a ha
      rw [hw, Submodule.mem_colon_singleton, Submodule.mem_bot, ← Submodule.Quotient.mk_smul,
        Submodule.Quotient.mk_eq_zero, hmemx] at ha
      simpa [Algebra.smul_def] using ha
    have hz : z ∉ Ideal.span {algebraMap R A x} := by
      intro hz
      apply (maximalIdeal.isMaximal R).ne_top
      rw [hw, Ideal.eq_top_iff_one, Submodule.mem_colon_singleton, Submodule.mem_bot, one_smul,
        Submodule.Quotient.mk_eq_zero, hmemx]
      exact hz
    set I := Ideal.span {algebraMap R A x}
    have hzq : (Ideal.Quotient.mk I z : A ⧸ I) ≠ 0 := by
      rwa [ne_eq, Ideal.Quotient.eq_zero_iff_mem]
    obtain ⟨P, hP, hle⟩ := exists_le_isAssociatedPrime_of_isNoetherianRing A _ hzq
    haveI hPp : P.IsPrime := hP.isPrime
    have hmP : maximalIdeal R ≤ P.comap (algebraMap R A) := by
      intro a ha
      apply hle
      rw [Submodule.mem_colon_singleton, Submodule.mem_bot, Algebra.smul_def,
        Ideal.Quotient.algebraMap_eq, ← map_mul, Ideal.Quotient.eq_zero_iff_mem]
      exact hmz a ha
    have hPm : P.comap (algebraMap R A) = maximalIdeal R :=
      ((maximalIdeal.isMaximal R).eq_of_le (Ideal.comap_isPrime _ P).ne_top hmP).symm
    haveI : P.LiesOver (maximalIdeal R) := ⟨hPm.symm⟩
    obtain ⟨Q, hQP, hQp, hQq⟩ := Ideal.exists_ideal_lt_liesOver_of_lt (S := A) P hqm
    have h1 : P.height = 1 := height_eq_one_of_mem_associatedPrimes hx' hP
    have hlt : Q.height < P.height := Ideal.height_strict_mono_of_isPrime hQP
    rw [h1, ENat.lt_one_iff_eq_zero, Ideal.height_eq_zero_iff_eq_bot] at hlt
    apply hq0
    rw [hQq.over, hlt]
    exact Ideal.comap_bot_of_injective _ hinj
  refine ⟨[x, y], rfl, (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> assumption), ?_⟩
  rw [IsLocalRing.isRegular_iff_isWeaklyRegular_of_subset_maximalIdeal
    (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> assumption),
    RingTheory.Sequence.isWeaklyRegular_cons_iff, RingTheory.Sequence.isWeaklyRegular_cons_iff]
  exact ⟨hreg, hyreg, RingTheory.Sequence.IsWeaklyRegular.nil _ _⟩

end GlobalTheory
