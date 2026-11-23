import Mathlib
import Development.AutomorphicSpectrum.Definitions.AdelicLattices.FactPrimes
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.LatNormGrLatNeZeroOfSpan

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Fl.ValRing

open NumberField IsDedekindDomain

variable {K : Type} [Field K] [NumberField K] {p : Nat.Primes} (j : K →+* ℂ_[p])

theorem norm_natCast_padicComplex (p : Nat.Primes) (n : ℕ) :
    ‖(n : ℂ_[p])‖ = ‖(n : ℚ_[p])‖ := by
  have h := PadicComplex.norm_extends' (p : ℕ) (n : ℚ_[p])
  simpa using h

def unitBall : ValuationSubring K where
  carrier := {a | ‖j a‖ ≤ 1}
  mul_mem' := fun {a b} ha hb => by
    simp only [Set.mem_setOf_eq, map_mul, norm_mul] at *
    exact mul_le_one₀ ha (norm_nonneg _) hb
  one_mem' := by simp
  add_mem' := fun {a b} ha hb => by
    simp only [Set.mem_setOf_eq, map_add] at *
    exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ha hb)
  zero_mem' := by simp
  neg_mem' := fun {a} ha => by
    simpa using ha
  mem_or_inv_mem' := fun a => by
    simp only [Subring.mem_mk, Subsemiring.mem_mk, Submonoid.mem_mk, Subsemigroup.mem_mk,
      Set.mem_setOf_eq, map_inv₀, norm_inv]
    rcases le_total ‖j a‖ 1 with h | h
    · exact Or.inl h
    · exact Or.inr (inv_le_one_of_one_le₀ h)

theorem mem_unitBall {a : K} : a ∈ unitBall j ↔ ‖j a‖ ≤ 1 := Iff.rfl

theorem integer_mem_unitBall (a : 𝓞 K) : (a : K) ∈ unitBall j := by
  have h : IsIntegral (unitBall j) (a : K) :=
    IsIntegral.tower_top (R := ℤ) (RingOfIntegers.isIntegral_coe a)
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.1 h
  rw [← hy]
  exact y.2

theorem norm_integer_le_one (a : 𝓞 K) : ‖j (a : K)‖ ≤ 1 := integer_mem_unitBall j a

def primeBelow : Ideal (𝓞 K) where
  carrier := {a | ‖j (a : K)‖ < 1}
  add_mem' := fun {a b} ha hb => by
    simp only [Set.mem_setOf_eq, map_add] at *
    exact (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt ha hb)
  zero_mem' := by simp
  smul_mem' := fun c a ha => by
    simp only [Set.mem_setOf_eq, smul_eq_mul, map_mul, norm_mul] at *
    exact (mul_le_of_le_one_left (norm_nonneg _) (norm_integer_le_one j c)).trans_lt ha

theorem mem_primeBelow {a : 𝓞 K} : a ∈ primeBelow j ↔ ‖j (a : K)‖ < 1 := Iff.rfl

instance primeBelow_isPrime : (primeBelow j).IsPrime := by
  refine ⟨fun h => ?_, fun {a b} hab => ?_⟩
  · have : (1 : 𝓞 K) ∈ primeBelow j := h ▸ Submodule.mem_top
    simp [mem_primeBelow] at this
  · by_contra hc
    push_neg at hc
    obtain ⟨ha, hb⟩ := hc
    have ha1 : ‖j (a : K)‖ = 1 := le_antisymm (norm_integer_le_one j a) (not_lt.1 ha)
    have hb1 : ‖j (b : K)‖ = 1 := le_antisymm (norm_integer_le_one j b) (not_lt.1 hb)
    have := (mem_primeBelow j).1 hab
    simp [ha1, hb1] at this

theorem norm_p_lt_one : ‖j ((p : ℕ) : K)‖ < 1 := by
  rw [map_natCast, norm_natCast_padicComplex, Padic.norm_p]
  exact inv_lt_one_of_one_lt₀ (by exact_mod_cast (p.2.one_lt))

theorem primeBelow_ne_bot : primeBelow j ≠ ⊥ := by
  intro h
  have h1 : (((p : ℕ) : 𝓞 K)) ∈ primeBelow j := by
    rw [mem_primeBelow]
    simpa using norm_p_lt_one j
  rw [h, Ideal.mem_bot] at h1
  exact p.2.ne_zero (by exact_mod_cast h1)

def place : HeightOneSpectrum (𝓞 K) := ⟨primeBelow j, primeBelow_isPrime j, primeBelow_ne_bot j⟩

theorem norm_le_one_of_valuation_le_one {y : K} (hy : (place j).valuation K y ≤ 1) :
    ‖j y‖ ≤ 1 := by
  obtain ⟨n, d, h⟩ := (place j).exists_primeCompl_mul_eq_of_integer y hy
  have hd : ‖j ((d : 𝓞 K) : K)‖ = 1 :=
    le_antisymm (norm_integer_le_one j _) (not_lt.1 d.2)
  have h2 := congrArg (fun t => ‖j t‖) h
  simp only [map_mul, norm_mul] at h2
  change ‖j y‖ * ‖j ((d : 𝓞 K) : K)‖ = ‖j (n : K)‖ at h2
  rw [hd, mul_one] at h2
  exact h2.le.trans (norm_integer_le_one j n)

theorem norm_lt_one_of_valuation_lt_one {y : K} (hy : (place j).valuation K y < 1) :
    ‖j y‖ < 1 := by
  obtain ⟨n, d, h⟩ := (place j).exists_primeCompl_mul_eq_of_integer y hy.le
  have hd : ‖j ((d : 𝓞 K) : K)‖ = 1 :=
    le_antisymm (norm_integer_le_one j _) (not_lt.1 d.2)
  have hdv : (place j).valuation K ((d : 𝓞 K) : K) = 1 := by
    have := ((place j).intValuation_eq_one_iff_mem_primeCompl (d : 𝓞 K)).2 d.2
    rw [← (place j).valuation_of_algebraMap (K := K)] at this
    exact this
  have hn : (place j).valuation K (n : K) < 1 := by
    have h3 := congrArg ((place j).valuation K) h
    rw [map_mul] at h3
    change (place j).valuation K y * (place j).valuation K ((d : 𝓞 K) : K) =
      (place j).valuation K (n : K) at h3
    rw [hdv, mul_one] at h3
    exact h3 ▸ hy
  have hn' : n ∈ primeBelow j := ((place j).valuation_lt_one_iff_mem (K := K) n).1 hn
  have h2 := congrArg (fun t => ‖j t‖) h
  simp only [map_mul, norm_mul] at h2
  change ‖j y‖ * ‖j ((d : 𝓞 K) : K)‖ = ‖j (n : K)‖ at h2
  rw [hd, mul_one] at h2
  exact h2.trans_lt hn'

theorem unitBall_eq : unitBall j = ((place j).valuation K).valuationSubring := by
  ext y
  rw [Valuation.mem_valuationSubring_iff, mem_unitBall]
  refine ⟨fun h => ?_, norm_le_one_of_valuation_le_one j⟩
  by_contra hc
  have hc' := not_le.1 hc
  have hy : y ≠ 0 := by
    rintro rfl
    simp at hc'
  have h1 : (place j).valuation K y⁻¹ < 1 := by
    rw [map_inv₀]
    exact inv_lt_one_of_one_lt₀ hc'
  have h2 := norm_lt_one_of_valuation_lt_one j h1
  rw [map_inv₀, norm_inv] at h2
  have h3 : 0 < ‖j y‖ := norm_pos_iff.2 ((map_ne_zero j).2 hy)
  exact absurd ((one_le_inv₀ h3).2 h) (not_le.2 h2)

theorem exists_dvr_of_padic_embedding : ∀ (K : Type) [Field K] [NumberField K] (p : Nat.Primes)
    (j : K →+* ℂ_[p]), ∃ (V : ValuationSubring K), IsDiscreteValuationRing V ∧
      (∀ a : K, ‖j a‖ ≤ 1 ↔ a ∈ V) ∧ (∀ a : 𝓞 K, (a : K) ∈ V) ∧
      ∀ n : ℕ, ¬ (p : ℕ) ∣ n → ‖j (n : K)‖ = 1 := by
  intro K _ _ p j
  refine ⟨unitBall j, ?_, fun a => Iff.rfl, integer_mem_unitBall j, fun n hn => ?_⟩
  · rw [unitBall_eq]
    infer_instance
  · rw [map_natCast, norm_natCast_padicComplex, Padic.norm_natCast_eq_one_iff]
    exact (Nat.Prime.coprime_iff_not_dvd p.2).2 hn

end GlobalTheory.CompanionTheory.Ar.Fl.ValRing
