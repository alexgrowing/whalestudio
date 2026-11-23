import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FixedCoefficientFieldInComplex
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TypeNormOfKummer

noncomputable section

open NumberField IsDedekindDomain Formalism.L2.Host GlobalTheory.NT GlobalTheory.Published GlobalTheory.Mem GlobalTheory.Mem.Fld
open scoped nonZeroDivisors IntermediateField

namespace GlobalTheory.Mem.FieldsEx

theorem exists_unif_one_mod {R : Type} [CommRing R] [IsDedekindDomain R] (𝔮 : Ideal R) (h𝔮 : 𝔮 ≠ ⊥)
    (v : HeightOneSpectrum R) : ∃ c : R, c ∈ v.asIdeal ∧ c ∉ v.asIdeal ^ 2 ∧
      ∀ w : HeightOneSpectrum R, w ≠ v → w.asIdeal ∣ 𝔮 → c - 1 ∈ w.asIdeal := by
  classical
  have hfin := Ideal.finite_factors h𝔮
  let S : Finset (HeightOneSpectrum R) := hfin.toFinset.erase v
  have hcop : IsCoprime (v.asIdeal ^ 2) (∏ w ∈ S, w.asIdeal) := by
    refine IsCoprime.pow_left (IsCoprime.prod_right fun w hw => ?_)
    have hne : v.asIdeal ≠ w.asIdeal := fun h => (Finset.ne_of_mem_erase hw) (HeightOneSpectrum.ext h).symm
    exact Ideal.isCoprime_iff_sup_eq.2 (v.isMaximal.coprime_of_ne w.isMaximal hne)
  obtain ⟨a, ha, b, hb, hab⟩ := Ideal.isCoprime_iff_exists.1 hcop
  obtain ⟨π, hπ1, hπ2⟩ := Ideal.exists_mem_pow_notMem_pow_succ v.asIdeal v.ne_bot v.isPrime.ne_top 1
  rw [pow_one] at hπ1
  refine ⟨π * b + a, ?_, ?_, fun w hw hd => ?_⟩
  · exact v.asIdeal.add_mem (v.asIdeal.mul_mem_right _ hπ1) (Ideal.pow_le_self two_ne_zero ha)
  · intro hc
    apply hπ2
    have : π = (π * b + a) + a * (π - 1) := by linear_combination (-π) * hab
    rw [this]
    exact Ideal.add_mem _ hc (Ideal.mul_mem_right _ _ ha)
  · have hS : w ∈ S := Finset.mem_erase.2 ⟨hw, hfin.mem_toFinset.2 hd⟩
    have hb' : b ∈ w.asIdeal := Ideal.le_of_dvd (Finset.dvd_prod_of_mem _ hS) hb
    have : π * b + a - 1 = b * (π - 1) := by linear_combination hab
    rw [this]
    exact Ideal.mul_mem_right _ _ hb'

theorem exists_gen_pow_prime_one_mod (L : Type) [Field L] [NumberField L] (𝔮 : Ideal (𝓞 L)) (h : ℕ) (h𝔮 : 𝔮 ≠ ⊥)
    (H : ∀ I : Ideal (𝓞 L), I ≠ ⊥ → IsCoprime I 𝔮 →
      ∃ α β : 𝓞 L, RayPair 𝔮 α β ∧ I ^ h * Ideal.span {β} = Ideal.span {α})
    (v : HeightOneSpectrum (𝓞 L)) : ∃ k : Lˣ,
      FractionalIdeal.spanSingleton (𝓞 L)⁰ (k : L) = (v.asIdeal : FractionalIdeal (𝓞 L)⁰ L) ^ h ∧
      ∀ w : HeightOneSpectrum (𝓞 L), w ≠ v → w.asIdeal ∣ 𝔮 → w.valuation L ((k : L) - 1) < 1 := by
  obtain ⟨c, hc1, hc2, hc3⟩ := exists_unif_one_mod 𝔮 h𝔮 v
  have hc0 : c ≠ 0 := by rintro rfl; exact hc2 (Ideal.zero_mem _)
  obtain ⟨J, hJ⟩ : v.asIdeal ∣ Ideal.span {c} :=
    Ideal.dvd_iff_le.2 ((Ideal.span_singleton_le_iff_mem _).2 hc1)
  have hcJ : c ∈ v.asIdeal * J := hJ ▸ Ideal.mem_span_singleton_self c
  have hJ0 : J ≠ ⊥ := by
    rintro rfl
    rw [Ideal.mul_bot] at hcJ
    exact hc0 hcJ
  have hcop : IsCoprime J 𝔮 := by
    rw [Ideal.isCoprime_iff_sup_eq]
    by_contra hne
    obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal _ hne
    have hm0 : m ≠ ⊥ := fun h0 => h𝔮 (le_bot_iff.1 (h0 ▸ le_sup_right.trans hle))
    let w : HeightOneSpectrum (𝓞 L) := ⟨m, hm.isPrime, hm0⟩
    have hJm : J ≤ m := le_sup_left.trans hle
    by_cases hw : w = v
    · apply hc2
      have : v.asIdeal = m := hw ▸ rfl
      rw [sq]
      exact Ideal.mul_mono_right (this ▸ hJm) hcJ
    · have h1 : c - 1 ∈ m := hc3 w hw (Ideal.dvd_iff_le.2 (le_sup_right.trans hle))
      have h2 : c ∈ m := hJm (Ideal.le_of_dvd (dvd_mul_left J v.asIdeal) hcJ)
      exact hm.ne_top ((Ideal.eq_top_iff_one _).2 (by simpa using m.sub_mem h2 h1))
  obtain ⟨α, β, ⟨hα0, hβ0, hα, -, hαβ, -⟩, hE⟩ := H J hJ0 hcop
  have hαL : algebraMap (𝓞 L) L α ≠ 0 := by simpa using hα0
  have hβL : algebraMap (𝓞 L) L β ≠ 0 := by simpa using hβ0
  have hcL : algebraMap (𝓞 L) L c ≠ 0 := by simpa using hc0
  refine ⟨Units.mk0 (algebraMap (𝓞 L) L (c ^ h * β) / algebraMap (𝓞 L) L α)
    (div_ne_zero (by rw [map_mul, map_pow]; exact mul_ne_zero (pow_ne_zero _ hcL) hβL) hαL), ?_, fun w hw hd => ?_⟩
  · have hI : Ideal.span {c ^ h * β} = v.asIdeal ^ h * Ideal.span {α} := by
      rw [← Ideal.span_singleton_mul_span_singleton, ← Ideal.span_singleton_pow, hJ, mul_pow, mul_assoc, hE]
    have hne : FractionalIdeal.spanSingleton (𝓞 L)⁰ (algebraMap (𝓞 L) L α) ≠ 0 :=
      FractionalIdeal.spanSingleton_ne_zero_iff.2 hαL
    apply mul_right_cancel₀ hne
    rw [Units.val_mk0, FractionalIdeal.spanSingleton_mul_spanSingleton, div_mul_cancel₀ _ hαL,
      ← FractionalIdeal.coeIdeal_span_singleton, ← FractionalIdeal.coeIdeal_span_singleton, hI,
      FractionalIdeal.coeIdeal_mul, FractionalIdeal.coeIdeal_pow]
  · have hle : 𝔮 ≤ w.asIdeal := Ideal.le_of_dvd hd
    have hαw : α ∉ w.asIdeal := fun hm => w.isPrime.ne_top (top_le_iff.1 (by
      rw [← Ideal.isCoprime_iff_sup_eq.1 hα]
      exact sup_le ((Ideal.span_singleton_le_iff_mem _).2 hm) hle))
    have hp : c ^ h - 1 ∈ w.asIdeal := by
      have := sub_dvd_pow_sub_pow c 1 h
      rw [one_pow] at this
      obtain ⟨t, ht⟩ := this
      rw [ht]
      exact Ideal.mul_mem_right _ _ (hc3 w hw hd)
    have hm : c ^ h * β - α ∈ w.asIdeal := by
      have : c ^ h * β - α = (c ^ h - 1) * β - (α - β) := by ring
      rw [this]
      exact Ideal.sub_mem _ (Ideal.mul_mem_right _ _ hp) (hle hαβ)
    rw [Units.val_mk0, div_sub_one hαL, ← map_sub, map_div₀,
      (w.valuation_eq_one_iff_notMem (K := L)).2 hαw, div_one]
    exact (w.valuation_lt_one_iff_mem (K := L) _).2 hm

end GlobalTheory.Mem.FieldsEx

end
