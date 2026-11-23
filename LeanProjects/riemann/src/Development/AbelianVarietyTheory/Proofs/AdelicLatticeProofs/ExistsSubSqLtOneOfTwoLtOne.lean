import Mathlib
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.SqSubLeNormSub

open NumberField IsDedekindDomain GlobalTheory.QNorm
open scoped WithZero

namespace GlobalTheory.QNorm

theorem exists_sub_sq_mem_of_two_mem (F : Type) [Field F] [NumberField F]
    (v : HeightOneSpectrum (𝓞 F)) (h2 : (2 : 𝓞 F) ∈ v.asIdeal) (a : 𝓞 F) :
    ∃ b : 𝓞 F, a - b ^ 2 ∈ v.asIdeal := by
  haveI : Finite (𝓞 F ⧸ v.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot v.asIdeal v.ne_bot
  haveI := v.isPrime
  have h0 : (2 : 𝓞 F ⧸ v.asIdeal) = 0 := by
    have := Ideal.Quotient.eq_zero_iff_mem.2 h2
    rwa [map_ofNat] at this
  have hinj : Function.Injective (fun t : 𝓞 F ⧸ v.asIdeal => t ^ 2) := by
    intro s t hst
    have hst' : s ^ 2 = t ^ 2 := hst
    have : (s - t) ^ 2 = 0 := by
      linear_combination hst' + (t ^ 2 - s * t) * h0
    exact sub_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 this)
  obtain ⟨t, ht⟩ := Finite.surjective_of_injective hinj (Ideal.Quotient.mk v.asIdeal a)
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective t
  refine ⟨b, Ideal.Quotient.eq.1 ?_⟩
  rw [map_pow]
  exact ht.symm

theorem exists_sub_sq_lt_one_of_two_lt_one :
    ∀ (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)),
      Valued.v (2 : v.adicCompletion F) < 1 → ∀ x : v.adicCompletion F, Valued.v x ≤ 1 →
        ∃ y : v.adicCompletion F, Valued.v y ≤ 1 ∧ Valued.v (x - y ^ 2) < 1 := by
  intro F _ _ v h2 x hx
  set φ := algebraMap F (v.adicCompletion F) with hφ
  have hval : ∀ k : F, Valued.v (φ k) = v.valuation F k := fun k =>
    HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v k
  have hmem : ∀ r : 𝓞 F, v.valuation F (algebraMap (𝓞 F) F r) < 1 ↔ r ∈ v.asIdeal :=
    fun r => HeightOneSpectrum.valuation_lt_one_iff_mem v r

  have h2' : (2 : 𝓞 F) ∈ v.asIdeal := by
    rw [← hmem, ← hval, map_ofNat, map_ofNat]
    exact h2

  obtain ⟨k, hk⟩ : ∃ k : F, Valued.v (φ k - x) < 1 := by
    have hU : {y : v.adicCompletion F | Valued.v (y - x) < 1} ∈ nhds x := by
      rw [Valued.mem_nhds]
      refine ⟨1, fun y hy => ?_⟩
      have hy' : Valued.v.restrict (y - x) < Valued.v.restrict 1 := by simpa using hy
      simpa using Valued.v.restrict_lt_iff.mp hy'
    exact (HeightOneSpectrum.denseRange_algebraMap F v).mem_nhds hU
  have hk1 : v.valuation F k ≤ 1 := by
    rw [← hval]
    have e : φ k = (φ k - x) + x := by ring
    rw [e]
    exact (Valuation.map_add _ _ _).trans (max_le hk.le hx)

  obtain ⟨r, hr⟩ : ∃ r : 𝓞 F, v.valuation F (k - algebraMap (𝓞 F) F r) < 1 := by
    obtain ⟨s, m, hs, hsm⟩ : ∃ s m : 𝓞 F, s ∉ v.asIdeal ∧
        k * algebraMap (𝓞 F) F s = algebraMap (𝓞 F) F m := by
      obtain ⟨n, d, h | h⟩ := HeightOneSpectrum.exists_primeCompl_mul_eq_or_mul_eq (K := F) v k
      · exact ⟨d, n, d.2, h⟩
      · refine ⟨n, d, fun hn => d.2 ?_, h⟩
        show (d : 𝓞 F) ∈ v.asIdeal
        rw [← hmem, ← h, map_mul]
        exact (mul_le_of_le_one_left' hk1).trans_lt ((hmem n).2 hn)
    obtain ⟨t, i, hi, hti⟩ := (Ideal.IsPrime.isMaximal v.isPrime v.ne_bot).exists_inv hs
    refine ⟨t * m, ?_⟩
    have hi' : i = 1 - t * s := by rw [← hti]; ring
    have e : k - algebraMap (𝓞 F) F (t * m) = k * algebraMap (𝓞 F) F i := by
      rw [hi', map_mul, ← hsm, map_sub, map_one, map_mul]; ring
    rw [e, map_mul]
    exact (mul_le_of_le_one_left' hk1).trans_lt ((hmem i).2 hi)

  obtain ⟨b, hb⟩ := exists_sub_sq_mem_of_two_mem F v h2' r
  refine ⟨φ (algebraMap (𝓞 F) F b), ?_, ?_⟩
  · rw [hval]
    exact HeightOneSpectrum.valuation_le_one v b
  · have e : x - φ (algebraMap (𝓞 F) F b) ^ 2 =
        -(φ k - x) + (φ (k - algebraMap (𝓞 F) F r) + φ (algebraMap (𝓞 F) F (r - b ^ 2))) := by
      simp only [map_sub, map_pow]; ring
    rw [e]
    refine Valuation.map_add_lt _ (by rwa [Valuation.map_neg]) (Valuation.map_add_lt _ ?_ ?_)
    · rw [hval]; exact hr
    · rw [hval]; exact (hmem _).2 hb

end GlobalTheory.QNorm
