import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SquarePairLocal.SqPairLocalOfSteps
import Lemmata.GeneralBFactLeftBis.Imports

noncomputable section
open NumberField

namespace PI.SqPairLocal

open PI.SqPair Formalism.L2.PairingIndexBounds.Eq.SqG

theorem powLoc : PowLoc := by
  intro E _ _ Q hQ c hc
  have := hQ.isPrime
  have hQ0 : Q ≠ ⊥ := Ring.ne_bot_of_isMaximal_of_not_isField hQ (NumberField.RingOfIntegers.not_isField E)
  have : IsDiscreteValuationRing (Localization.AtPrime Q) :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain (𝓞 E) hQ0 _
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible (Localization.AtPrime Q)
  have hc' : algebraMap (𝓞 E) (Localization.AtPrime Q) c ≠ 0 := by
    intro h
    apply hc
    apply IsLocalization.injective (Localization.AtPrime Q) (Ideal.primeCompl_le_nonZeroDivisors Q)
    rw [h, map_zero]
  obtain ⟨K, hK⟩ := IsDiscreteValuationRing.ideal_eq_span_pow_irreducible
    (s := Ideal.span {algebraMap (𝓞 E) (Localization.AtPrime Q) c})
    (by rwa [Ne, Ideal.span_singleton_eq_bot]) hϖ
  refine ⟨K, fun x hx => ?_⟩
  have hmax : IsLocalRing.maximalIdeal (Localization.AtPrime Q) = Ideal.span {ϖ} :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mp hϖ
  have hxA : algebraMap (𝓞 E) (Localization.AtPrime Q) x ∈
      Ideal.span {algebraMap (𝓞 E) (Localization.AtPrime Q) c} := by
    rw [hK, ← Ideal.span_singleton_pow, ← hmax,
      ← IsLocalization.AtPrime.map_eq_maximalIdeal (p := Q), ← Ideal.map_pow]
    exact Ideal.mem_map_of_mem _ hx
  obtain ⟨y, hy⟩ := Ideal.mem_span_singleton'.mp hxA
  obtain ⟨⟨w, s⟩, rfl⟩ := IsLocalization.mk'_surjective Q.primeCompl y
  have key : algebraMap (𝓞 E) (Localization.AtPrime Q) (c * w) =
      algebraMap (𝓞 E) (Localization.AtPrime Q) (s * x) := by
    rw [map_mul, map_mul, ← hy, ← IsLocalization.mk'_spec (Localization.AtPrime Q) w s]
    ring
  obtain ⟨t, ht⟩ := (IsLocalization.eq_iff_exists Q.primeCompl (Localization.AtPrime Q)).mp key
  refine ⟨(t * s : Q.primeCompl), (t * s : Q.primeCompl).2, t * w, ?_⟩
  push_cast
  linear_combination -ht

theorem locGlob : LocGlob := by
  intro E _ _ W _ _ X x p hp hloc
  let J : Ideal (𝓞 E) := X.comap (LinearMap.toSpanSingleton (𝓞 E) W x)
  have hJ : ∀ a, a ∈ J ↔ a • x ∈ X := fun a => by
    simp [J, LinearMap.toSpanSingleton_apply]
  have htop : J ⊔ Ideal.span {(p : 𝓞 E)} = ⊤ := by
    by_contra h
    obtain ⟨Q, hQ, hle⟩ := Ideal.exists_le_maximal _ h
    obtain ⟨s, hs, hsx⟩ := hloc Q hQ (hle (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _)))
    exact hs (hle (Ideal.mem_sup_left ((hJ s).mpr hsx)))
  have hpnu : Ideal.span {(p : 𝓞 E)} ≠ ⊤ := by
    intro h
    have h2 := congrArg Ideal.absNorm h
    rw [Ideal.absNorm_span_singleton, Algebra.norm_natCast, Ideal.absNorm_top, Int.natAbs_pow,
      Int.natAbs_natCast] at h2
    have hd : 0 < Module.finrank ℤ (𝓞 E) := Module.finrank_pos
    rcases Nat.pow_eq_one.mp h2 with h1 | h1
    · exact hp.one_lt.ne' h1
    · omega
  have hJ0 : J ≠ ⊥ := by
    rintro h
    rw [h, bot_sup_eq] at htop
    exact hpnu htop
  have : Finite (𝓞 E ⧸ J) :=
    (Ideal.absNorm_ne_zero_iff J).mp (by rwa [Ne, Ideal.absNorm_eq_zero_iff])
  have h1 : (1 : 𝓞 E) ∈ J ⊔ Ideal.span {(p : 𝓞 E)} := by rw [htop]; exact Submodule.mem_top
  obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp h1
  obtain ⟨r, rfl⟩ := Ideal.mem_span_singleton'.mp hb
  have hunit : Ideal.Quotient.mk J r * Ideal.Quotient.mk J (p : 𝓞 E) = 1 := by
    rw [← map_mul, ← map_one (Ideal.Quotient.mk J), ← hab, Ideal.Quotient.eq]
    have : r * (p : 𝓞 E) - (a + r * (p : 𝓞 E)) = -a := by ring
    rw [this]
    exact J.neg_mem ha
  have hndvd : ¬ p ∣ Ideal.absNorm J := by
    intro hdvd
    have := Fact.mk hp
    let := Fintype.ofFinite (𝓞 E ⧸ J)
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply, Nat.card_eq_fintype_card] at hdvd
    obtain ⟨z, hz⟩ := exists_prime_addOrderOf_dvd_card p hdvd
    have hpz : Ideal.Quotient.mk J (p : 𝓞 E) * z = 0 := by
      rw [map_natCast, ← nsmul_eq_mul, ← hz, addOrderOf_nsmul_eq_zero]
    have hz0 : z = 0 := by
      calc z = (Ideal.Quotient.mk J r * Ideal.Quotient.mk J (p : 𝓞 E)) * z := by rw [hunit, one_mul]
        _ = 0 := by rw [mul_assoc, hpz, mul_zero]
    rw [hz0, addOrderOf_zero] at hz
    exact hp.one_lt.ne hz
  refine ⟨Ideal.absNorm J, ?_, ?_⟩
  · exact_mod_cast hndvd
  · rw [Int.cast_natCast, ← hJ]
    exact Ideal.absNorm_mem J

section IntMulSec

variable {E : Type} [Field E] [NumberField E] {N : ℕ}

theorem exists_den (L'' : Submodule (𝓞 E) (Fin N → E))
    (hsp : Submodule.span E (L'' : Set (Fin N → E)) = ⊤) (v : Fin N → E) :
    ∃ d : 𝓞 E, d ≠ 0 ∧ d • v ∈ L'' := by
  first | exact Bl.general_b_fact_left_bis.goal1 .. | (apply Bl.general_b_fact_left_bis.goal1 <;> assumption) | (intros; apply Bl.general_b_fact_left_bis.goal1 <;> assumption) | (apply @Bl.general_b_fact_left_bis.goal1 <;> assumption) | (intros; apply @Bl.general_b_fact_left_bis.goal1 <;> assumption) | (apply @Bl.general_b_fact_left_bis.goal1 <;> first | assumption | infer_instance)

theorem exists_den_fg (L' L'' : Submodule (𝓞 E) (Fin N → E)) (hfg : L'.FG)
    (hsp : Submodule.span E (L'' : Set (Fin N → E)) = ⊤) :
    ∃ d : 𝓞 E, d ≠ 0 ∧ ∀ y ∈ L', d • y ∈ L'' := by
  classical
  obtain ⟨S, rfl⟩ := hfg
  choose f hf0 hf using fun v => exists_den L'' hsp v
  refine ⟨∏ g ∈ S, f g, Finset.prod_ne_zero_iff.mpr (fun g _ => hf0 g), fun y hy => ?_⟩
  induction hy using Submodule.span_induction with
  | mem g hg =>
    rw [← Finset.mul_prod_erase S f (Finset.mem_coe.mp hg), mul_comm, mul_smul]
    exact L''.smul_mem _ (hf g)
  | zero => rw [smul_zero]; exact L''.zero_mem
  | add y z _ _ hy hz => rw [smul_add]; exact L''.add_mem hy hz
  | smul r y _ h => rw [smul_comm]; exact L''.smul_mem r h

theorem nat_mul (d : 𝓞 E) (hd : d ≠ 0) :
    ∃ d' : 𝓞 E, ((Ideal.absNorm (Ideal.span {d}) : ℕ) : 𝓞 E) = d * d' ∧
      Ideal.absNorm (Ideal.span {d}) ≠ 0 := by
  obtain ⟨d', hd'⟩ := Ideal.mem_span_singleton.mp (Ideal.absNorm_mem (Ideal.span {d}))
  refine ⟨d', hd', ?_⟩
  rw [Ne, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]
  exact hd

end IntMulSec

theorem intMul : IntMul := by
  intro E _ _ _ N L' L'' h' h'' n hn
  obtain ⟨d1, hd1, k1⟩ := exists_den_fg L' L'' h'.1 h''.2.1
  obtain ⟨d2, hd2, k2⟩ := exists_den_fg L'' L' h''.1 h'.2.1
  obtain ⟨D', hD', hD0⟩ := nat_mul (d1 * d2) (mul_ne_zero hd1 hd2)
  obtain ⟨n', hn', hn0⟩ := nat_mul n hn
  refine ⟨Ideal.absNorm (Ideal.span {d1 * d2}) * Ideal.absNorm (Ideal.span {n}),
    mul_ne_zero hD0 hn0, fun y hy => ?_⟩
  have hDy : (d1 * d2) • y ∈ L' ∧ (d1 * d2) • y ∈ L'' := by
    rcases hy with hy | hy
    · have e : (d1 * d2) • y = d2 • (d1 • y) := by rw [smul_smul, mul_comm]
      exact ⟨L'.smul_mem _ hy, e ▸ L''.smul_mem d2 (k1 y hy)⟩
    · have e : (d1 * d2) • y = d1 • (d2 • y) := by rw [smul_smul]
      exact ⟨e ▸ L'.smul_mem d1 (k2 y hy), L''.smul_mem _ hy⟩
  refine ⟨(D' * n') • ((d1 * d2) • y), L'.smul_mem _ hDy.1, L''.smul_mem _ hDy.2, ?_⟩
  rw [Nat.cast_mul, hD', hn', smul_smul, smul_smul]
  congr 1
  ring

end PI.SqPairLocal
