import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormPeriodSq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemLsB
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardLatticeDoubleCosetClassesStabilisers
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteWeilRepEqLatticeIntertwinerMulCharacter

open NumberField MeasureTheory IsDedekindDomain
open scoped Classical
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum
open Formalism.MainNotions.TaylorLogMetric (VC embT tor0 Hf lamOf area Th U)
open Formalism.MainNotions.StandardLatticesGL3 (WeilO HeckeU TT stdL pt oddE0)
open GlobalTheory.NormExact
open GlobalTheory.BotFormula (IsFinPt)
open GlobalTheory.BotClassDict (finQ)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ZeroAtPlaces

section Generic

variable {K : Type} [Field K] [NumberField K]

theorem ev_mul (a b : FiniteAdeleRing (𝓞 K) K) (Q : HeightOneSpectrum (𝓞 K)) : (a * b) Q = a Q * b Q := rfl

theorem val_nat (Q : HeightOneSpectrum (𝓞 K)) (n : ℕ) :
    Valued.v ((n : FiniteAdeleRing (𝓞 K) K) Q) = Q.valuation K ((n : 𝓞 K) : K) := by
  rw [← Formalism.UG.P.levelaf_valued_algebraMap, ← map_natCast (algebraMap K (FiniteAdeleRing (𝓞 K) K)) n]
  rfl

theorem val_nat_eq_one (Q : HeightOneSpectrum (𝓞 K)) {n : ℕ} (hn : (n : 𝓞 K) ∉ Q.asIdeal) :
    Valued.v ((n : FiniteAdeleRing (𝓞 K) K) Q) = 1 := by
  rw [val_nat]
  rw [← HeightOneSpectrum.valuation_lt_one_iff_mem (K := K), not_lt] at hn
  exact le_antisymm (Q.valuation_le_one (K := K) _) hn

theorem val_nat_lt_one (Q : HeightOneSpectrum (𝓞 K)) {n : ℕ} (hn : (n : 𝓞 K) ∈ Q.asIdeal) :
    Valued.v ((n : FiniteAdeleRing (𝓞 K) K) Q) < 1 := by
  rw [val_nat]
  exact (HeightOneSpectrum.valuation_lt_one_iff_mem (K := K) Q _).2 hn

theorem divisible_iff {q : ℕ} (hq : q.Prime) (y : FiniteAdeleRing (𝓞 K) K)
    (hy : ∃ n : ℕ, 0 < n ∧ ∀ Q, ((n : FiniteAdeleRing (𝓞 K) K) * y) Q ∈ Q.adicCompletionIntegers K) :
    (∀ k : ℕ, ∃ m : ℕ, 0 < m ∧ Nat.Coprime m q ∧ ∃ s : FiniteAdeleRing (𝓞 K) K,
      (∀ Q, s Q ∈ Q.adicCompletionIntegers K) ∧
        (m : FiniteAdeleRing (𝓞 K) K) * y = (q : FiniteAdeleRing (𝓞 K) K) ^ k * s) ↔
    ∀ Q : HeightOneSpectrum (𝓞 K), (q : 𝓞 K) ∈ Q.asIdeal → y Q = 0 := by
  constructor
  · intro h Q hQ
    by_contra h0
    have h1 : Valued.v (y Q) ≠ 0 := (Valuation.ne_zero_iff _).2 h0
    obtain ⟨k, hk⟩ := exists_pow_lt₀ (val_nat_lt_one Q hQ) (Units.mk0 _ h1)
    obtain ⟨m, -, hm, s, hs, e⟩ := h k
    have hm' : (m : 𝓞 K) ∉ Q.asIdeal := by
      intro hmem
      obtain ⟨a, b, hab⟩ := (Nat.isCoprime_iff_coprime.2 hm).map (Int.castRingHom (𝓞 K))
      simp only [eq_intCast, Int.cast_natCast] at hab
      refine Q.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 ?_)
      rw [← hab]
      exact add_mem (Ideal.mul_mem_left _ _ hmem) (Ideal.mul_mem_left _ _ hQ)
    have e1 : (m : FiniteAdeleRing (𝓞 K) K) Q * y Q = ((q : FiniteAdeleRing (𝓞 K) K) Q) ^ k * s Q :=
      congrArg (fun z : FiniteAdeleRing (𝓞 K) K => z Q) e
    have e2 := congrArg Valued.v e1
    rw [map_mul, map_mul, map_pow, val_nat_eq_one Q hm', one_mul] at e2
    have hs1 : Valued.v (s Q) ≤ 1 := (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 (hs Q)
    rw [Units.val_mk0, e2] at hk
    exact absurd hk (not_lt.2 (mul_le_of_le_one_right' hs1))
  · intro h k
    obtain ⟨n, hn, hint⟩ := hy
    obtain ⟨j, m, hm, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn.ne' q hq.ne_one
    have hm0 : 0 < m := Nat.pos_of_ne_zero (by rintro rfl; exact hm (dvd_zero _))
    have hq0 : (q : K) ≠ 0 := Nat.cast_ne_zero.2 hq.ne_zero
    have hu : (q : FiniteAdeleRing (𝓞 K) K) ^ k * algebraMap K _ ((q : K) ^ k)⁻¹ = 1 := by
      rw [← map_natCast (algebraMap K (FiniteAdeleRing (𝓞 K) K)) q, ← map_pow, ← map_mul,
        mul_inv_cancel₀ (pow_ne_zero k hq0), map_one]
    refine ⟨m, hm0, ((Nat.Prime.coprime_iff_not_dvd hq).2 hm).symm,
      algebraMap K _ ((q : K) ^ k)⁻¹ * ((m : FiniteAdeleRing (𝓞 K) K) * y), fun Q => ?_,
      by rw [← mul_assoc, hu, one_mul]⟩
    by_cases hQ : (q : 𝓞 K) ∈ Q.asIdeal
    · rw [ev_mul, ev_mul, h Q hQ, mul_zero, mul_zero]
      exact zero_mem _
    · have h1 := val_nat_eq_one Q hQ
      have h2 := (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 (hint Q)
      have e1 : ((q : FiniteAdeleRing (𝓞 K) K) Q) ^ k *
          (algebraMap K (FiniteAdeleRing (𝓞 K) K) ((q : K) ^ k)⁻¹) Q = 1 :=
        congrArg (fun z : FiniteAdeleRing (𝓞 K) K => z Q) hu
      have e2 := congrArg Valued.v e1
      rw [map_mul, map_pow, h1, one_pow, one_mul, map_one] at e2
      have e3 : (((q ^ j * m : ℕ) : FiniteAdeleRing (𝓞 K) K) * y) Q =
          ((q : FiniteAdeleRing (𝓞 K) K) Q) ^ j * ((m : FiniteAdeleRing (𝓞 K) K) * y) Q := by
        rw [Nat.cast_mul, Nat.cast_pow, mul_assoc]
        rfl
      rw [e3, map_mul, map_pow, h1, one_pow, one_mul] at h2
      rw [HeightOneSpectrum.mem_adicCompletionIntegers, ev_mul, map_mul, e2, one_mul]
      exact h2

end Generic

open GlobalTheory.BotFormula GlobalTheory.BotClassDict

theorem mem_OhE_iff {D : D7} (y : Formalism.MainNotions.StandardLatticesGL3.AE D) :
    y ∈ Formalism.MainNotions.StandardLatticesGL3.OhE D ↔ ∀ Q, toFinE D y Q ∈ Q.adicCompletionIntegers D.host.E :=
  ⟨fun hy => GlobalTheory.AdeleBaseChange.map_mem_int (ι := (toFinE D).toRingHom) toFinE_tmul hy,
    fun hy => GlobalTheory.AdeleBaseChange.mem_int_of_map (ι := (toFinE D).toRingHom) toFinE_tmul hy⟩

theorem zeroAt_iff_comp {D : D7} {q : ℕ} (hq : q.Prime) (y : Formalism.MainNotions.StandardLatticesGL3.AE D) :
    Formalism.MainNotions.StandardLatticesGL3.ZeroAt D q y ↔
      ∀ Q : HeightOneSpectrum (𝓞 D.host.E), (q : 𝓞 D.host.E) ∈ Q.asIdeal → toFinE D y Q = 0 := by
  obtain ⟨n, hn, hint⟩ := (GlobalTheory.AdelicApprox.approx_mod_ideal D ⊤ top_ne_bot).2.1 y
  rw [mem_OhE_iff, map_mul, map_natCast] at hint
  rw [← divisible_iff hq (toFinE D y) ⟨n, hn, hint⟩]
  refine forall_congr' fun k => exists_congr fun m => and_congr_right' (and_congr_right' ⟨?_, ?_⟩)
  · rintro ⟨s, hs, e⟩
    refine ⟨toFinE D s, (mem_OhE_iff s).1 hs, ?_⟩
    have := congrArg (toFinE D) e
    rwa [map_mul, map_mul, map_pow, map_natCast, map_natCast] at this
  · rintro ⟨s, hs, e⟩
    obtain ⟨s, rfl⟩ := (toFinE D).surjective s
    refine ⟨s, (mem_OhE_iff s).2 hs, (toFinE D).injective ?_⟩
    rw [map_mul, map_mul, map_pow, map_natCast, map_natCast]
    exact e

theorem toFinE_finQ {D : D7} (a : AE D) :
    toFinE D (finQ D a) = GlobalTheory.LFun.finAdEquiv D.host.F D.host.E (finPart D a) := by
  rw [← finAdEquiv_toAfE, toAfE_finQ]
  rfl

theorem comp_base {D : D7} (η : AF D.host.F) (Q : HeightOneSpectrum (𝓞 D.host.E)) :
    toFinE D (finQ D (algebraMap (AF D.host.F) (AE D) η)) Q =
      GlobalTheory.AdeleBaseChange.locMap D.host.F Q (η.2 (Q.under (𝓞 D.host.F))) := by
  have h : GlobalTheory.LFun.finAdEquiv D.host.F D.host.E (finPart D (algebraMap (AF D.host.F) (AE D) η)) =
      GlobalTheory.AdeleBaseChange.adMap D.host.F D.host.E η.2 * algebraMap D.host.E _ 1 := GlobalTheory.LFun.toFinAd_tmul η.2 1
  rw [toFinE_finQ, h, map_one, mul_one]
  rfl

theorem idem_mul_eq_zero_iff {D : D7} {v : HeightOneSpectrum (𝓞 D.host.F)} {η : AF D.host.F} (h : IsPlaceIdem D v η)
    (a : AE D) : algebraMap (AF D.host.F) (AE D) η * a = 0 ↔
      ∀ Q : HeightOneSpectrum (𝓞 D.host.E), Q.under (𝓞 D.host.F) = v → toFinE D (finQ D a) Q = 0 := by
  have hev : ∀ Q, toFinE D (finQ D (algebraMap (AF D.host.F) (AE D) η * a)) Q =
      GlobalTheory.AdeleBaseChange.locMap D.host.F Q (η.2 (Q.under (𝓞 D.host.F))) * toFinE D (finQ D a) Q := by
    intro Q
    rw [RingHom.map_mul, map_mul, ev_mul, comp_base]
  obtain ⟨α, rfl, h1, h0⟩ := h
  have hinf : infPart D (algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 α)) = 0 := TensorProduct.zero_tmul _ _
  have k1 : ∀ Q : HeightOneSpectrum (𝓞 D.host.E), Q.under (𝓞 D.host.F) = v →
      GlobalTheory.AdeleBaseChange.locMap D.host.F Q ((pairA D.host.F 0 α).2 (Q.under (𝓞 D.host.F))) = 1 := by
    intro Q hQ
    subst hQ
    exact (congrArg _ h1).trans (map_one _)
  have k0 : ∀ Q : HeightOneSpectrum (𝓞 D.host.E), Q.under (𝓞 D.host.F) ≠ v →
      GlobalTheory.AdeleBaseChange.locMap D.host.F Q ((pairA D.host.F 0 α).2 (Q.under (𝓞 D.host.F))) = 0 :=
    fun Q hQ => (congrArg _ (h0 _ hQ)).trans (map_zero _)
  constructor
  · intro e Q hQ
    have := hev Q
    rw [e, k1 Q hQ, one_mul, RingHom.map_zero, map_zero] at this
    exact this.symm
  · intro e
    refine GlobalTheory.SplitScalar.adele_ext (by rw [RingHom.map_mul, hinf, zero_mul, RingHom.map_zero]) ?_
    apply (GlobalTheory.LFun.finAdEquiv D.host.F D.host.E).injective
    rw [← toFinE_finQ, RingHom.map_zero, map_zero]
    refine FiniteAdeleRing.ext _ fun Q => (hev Q).trans ?_
    by_cases hQ : Q.under (𝓞 D.host.F) = v
    · rw [e Q hQ, mul_zero]
      rfl
    · rw [k0 Q hQ, zero_mul]
      rfl

theorem zeroAt_finQ_iff : ∀ (D : D7) (q : ℕ), q.Prime → ∀ a : AE D, (Formalism.MainNotions.StandardLatticesGL3.ZeroAt D q (finQ D a) ↔
  ∀ (v : HeightOneSpectrum (𝓞 D.host.F)) (η : AF D.host.F), IsPlaceIdem D v η → (q : 𝓞 D.host.F) ∈ v.asIdeal →
    algebraMap (AF D.host.F) (AE D) η * a = 0) := by
  intro D q hq a
  have hmem : ∀ Q : HeightOneSpectrum (𝓞 D.host.E),
      (q : 𝓞 D.host.F) ∈ (Q.under (𝓞 D.host.F)).asIdeal ↔ (q : 𝓞 D.host.E) ∈ Q.asIdeal := by
    intro Q
    change algebraMap (𝓞 D.host.F) (𝓞 D.host.E) _ ∈ Q.asIdeal ↔ _
    rw [map_natCast]
  rw [zeroAt_iff_comp hq]
  constructor
  · intro h v η hη hv
    refine (idem_mul_eq_zero_iff hη a).2 fun Q hQ => h Q ((hmem Q).1 ?_)
    rw [hQ]
    exact hv
  · intro h Q hQ
    obtain ⟨η, hη⟩ := GlobalTheory.IdemSupport.exists_placeIdem (D := D) (Q.under (𝓞 D.host.F))
    exact (idem_mul_eq_zero_iff hη a).1 (h _ η hη ((hmem Q).2 hQ)) Q rfl

end GlobalTheory.ZeroAtPlaces
