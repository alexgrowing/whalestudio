import Mathlib
import Development.AbelianVarietyTheory.Definitions.CMLattices.LamLetters
import Development.AbelianVarietyTheory.Definitions.CMLattices.ExistsIsThetaDegOfIsLocalModel
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsUniqueIdeleOfLinearEquivQuotientLocal

open NumberField IsDedekindDomain Formalism.L2.LamCM WithZero
open scoped nonZeroDivisors

namespace GlobalTheory.LamF

variable {K : Type} [Field K] [NumberField K]

theorem isLocGen_iff_valuation_eq (p : HeightOneSpectrum (𝓞 K)) (c : K) (I : FractionalIdeal (𝓞 K)⁰ K) :
    IsLocGen p c I ↔ p.valuation K c = exp (-FractionalIdeal.count K p I) := by
  constructor
  · rintro ⟨h0, h⟩
    rw [GlobalTheory.Idele.valuation_eq_exp_neg_count p h0, h]
  · intro h
    have h0 : c ≠ 0 := by
      rintro rfl
      rw [map_zero] at h
      exact exp_ne_zero h.symm
    refine ⟨h0, ?_⟩
    rw [GlobalTheory.Idele.valuation_eq_exp_neg_count p h0, exp_inj] at h
    exact neg_injective h

theorem valuation_le_iff_exists_smul_mem (p : HeightOneSpectrum (𝓞 K)) {I : FractionalIdeal (𝓞 K)⁰ K}
    (hI : I ≠ 0) (c : K) :
    p.valuation K c ≤ exp (-FractionalIdeal.count K p I) ↔ ∃ s : 𝓞 K, s ∉ p.asIdeal ∧ s • c ∈ I := by
  constructor
  · intro h
    obtain ⟨y, hy, hv⟩ := GlobalTheory.Idele.exists_mem_valuation_eq hI p
    have hvy : p.valuation K y ≠ 0 := by rw [hv]; exact exp_ne_zero
    have hy0 : y ≠ 0 := by rintro rfl; simp at hvy
    have h1 : p.valuation K (c / y) ≤ 1 := by
      rw [map_div₀, div_le_one₀ (zero_lt_iff.2 hvy), hv]; exact h
    obtain ⟨a, s, hs⟩ := HeightOneSpectrum.exists_primeCompl_mul_eq_of_integer p (c / y) h1
    refine ⟨s.1, s.2, ?_⟩
    have : (s.1 : 𝓞 K) • c = a • y := by
      rw [Algebra.smul_def, Algebra.smul_def, ← hs]
      field_simp
    rw [this]
    exact Submodule.smul_mem (I : Submodule (𝓞 K) K) a hy
  · rintro ⟨s, hs, hc⟩
    have h := (GlobalTheory.Idele.mem_iff_valuation_le hI _).1 hc p
    have h1 : p.valuation K (algebraMap (𝓞 K) K s) = 1 := by
      refine le_antisymm (p.valuation_le_one s) (not_lt.1 fun hlt => hs ?_)
      exact (p.valuation_lt_one_iff_mem s).1 hlt
    rwa [Algebra.smul_def, map_mul, h1, one_mul] at h

theorem mem_iff_forall_exists_smul_mem {V : Type} [AddCommGroup V] [Module (𝓞 K) V]
    (Λ : Submodule (𝓞 K) V) (z : V) :
    z ∈ Λ ↔ ∀ p : HeightOneSpectrum (𝓞 K), ∃ s : 𝓞 K, s ∉ p.asIdeal ∧ s • z ∈ Λ := by
  constructor
  · intro hz p
    exact ⟨1, fun h => p.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h), by simpa using hz⟩
  · intro h
    let A : Ideal (𝓞 K) := Λ.comap (LinearMap.toSpanSingleton (𝓞 K) V z)
    have hA : A = ⊤ := by
      by_contra hne
      obtain ⟨m, hm, hAm⟩ := Ideal.exists_le_maximal A hne
      have hm0 : m ≠ ⊥ := Ring.ne_bot_of_isMaximal_of_not_isField hm (RingOfIntegers.not_isField K)
      obtain ⟨s, hs, hsz⟩ := h ⟨m, hm.isPrime, hm0⟩
      exact hs (hAm (by simpa [A] using hsz))
    have : (1 : 𝓞 K) ∈ A := hA ▸ Submodule.mem_top
    simpa [A] using this

theorem local_global_ideal_lattice : ∀ (K : Type) [Field K] [NumberField K],
    (∀ (I : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) (cl : HeightOneSpectrum (𝓞 K) → K), I ≠ 0 →
      (∀ p, IsLocGen p (cl p) I) → ∀ c : K,
        c ∈ I ↔ ∀ p : HeightOneSpectrum (𝓞 K), p.valuation K c ≤ p.valuation K (cl p)) ∧
    (∀ (I : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) (p : HeightOneSpectrum (𝓞 K)), I ≠ 0 →
      (∃ cl ∈ I, IsLocGen p cl I) ∧ ∀ cl, IsLocGen p cl I ↔ cl ≠ 0 ∧ ∀ c : K,
        p.valuation K c ≤ p.valuation K cl ↔ ∃ s : 𝓞 K, s ∉ p.asIdeal ∧ s • c ∈ I) ∧
    ∀ (V : Type) [AddCommGroup V] [Module (𝓞 K) V] (Λ : Submodule (𝓞 K) V) (z : V),
      z ∈ Λ ↔ ∀ p : HeightOneSpectrum (𝓞 K), ∃ s : 𝓞 K, s ∉ p.asIdeal ∧ s • z ∈ Λ := by
  intro K _ _
  refine ⟨fun I cl hI hcl c => ?_, fun I p hI => ⟨?_, fun cl => ?_⟩,
    fun V _ _ Λ z => mem_iff_forall_exists_smul_mem Λ z⟩
  · rw [GlobalTheory.Idele.mem_iff_valuation_le hI]
    refine forall_congr' fun p => ?_
    rw [(isLocGen_iff_valuation_eq p _ I).1 (hcl p)]
  · obtain ⟨y, hy, hv⟩ := GlobalTheory.Idele.exists_mem_valuation_eq hI p
    exact ⟨y, hy, (isLocGen_iff_valuation_eq p y I).2 hv⟩
  · constructor
    · intro h
      refine ⟨h.1, fun c => ?_⟩
      rw [(isLocGen_iff_valuation_eq p _ I).1 h]
      exact valuation_le_iff_exists_smul_mem p hI c
    · rintro ⟨-, h⟩
      obtain ⟨y, hy, hv⟩ := GlobalTheory.Idele.exists_mem_valuation_eq hI p
      refine (isLocGen_iff_valuation_eq p cl I).2 (le_antisymm ?_ ?_)
      · exact (valuation_le_iff_exists_smul_mem p hI cl).2 ((h cl).1 le_rfl)
      · rw [← hv]
        exact (h y).2 ((valuation_le_iff_exists_smul_mem p hI y).1 hv.le)

end GlobalTheory.LamF
