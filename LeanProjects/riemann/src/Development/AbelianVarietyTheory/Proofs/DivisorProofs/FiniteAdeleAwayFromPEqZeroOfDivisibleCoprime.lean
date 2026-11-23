import Development.AbelianVarietyTheory.Definitions.Divisors.HasDivPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PowEqPowOfModEqSim
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AV GlobalTheory.AV.AbVar GlobalTheory.PDivGroup GlobalTheory.Dieu GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.LKGeo GlobalTheory.LKRes
open ReciprocityTheory.DiscreteGroups.LocalClassField
open scoped TensorProduct
open scoped TensorProduct

noncomputable section
open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum WithZero
open scoped RestrictedProduct

namespace GlobalTheory.AfPZero

theorem natCast_eq_algebraMap (v : HeightOneSpectrum ℤ) (n : ℕ) :
    (n : v.adicCompletion ℚ) = algebraMap ℤ (v.adicCompletion ℚ) (n : ℤ) :=
  (map_natCast (algebraMap ℤ (v.adicCompletion ℚ)) n).symm

theorem valued_natCast (v : HeightOneSpectrum ℤ) (n : ℕ) :
    Valued.v (n : v.adicCompletion ℚ) = v.intValuation (n : ℤ) := by
  rw [natCast_eq_algebraMap]
  have := valuedAdicCompletion_eq_valuation (K := ℚ) v (n : ℤ)
  rw [← valuation_of_algebraMap (K := ℚ)]
  exact this

theorem eq_zero_of_dvd (v : HeightOneSpectrum ℤ) (x : v.adicCompletion ℚ)
    (h : ∀ k : ℕ, ∃ n : ℕ, (n : ℤ) ∈ v.asIdeal ^ k ∧
      ∃ y ∈ v.adicCompletionIntegers ℚ, x = (n : v.adicCompletion ℚ) * y) : x = 0 := by
  by_contra hx
  have hγ : Valued.v x ≠ 0 := by simpa using hx
  set L : ℤ := log (Valued.v x) with hL
  obtain ⟨n, hn, y, hy, hxe⟩ := h ((-L).toNat + 1)
  have h1 : Valued.v x ≤ exp (-(((-L).toNat + 1 : ℕ) : ℤ)) := by
    rw [hxe, map_mul]
    calc Valued.v (n : v.adicCompletion ℚ) * Valued.v y ≤ Valued.v (n : v.adicCompletion ℚ) * 1 :=
          by gcongr; exact (mem_adicCompletionIntegers ℤ ℚ v).1 hy
      _ = v.intValuation (n : ℤ) := by rw [_root_.mul_one, valued_natCast]
      _ ≤ _ := (intValuation_le_pow_iff_mem v _ _).2 hn
  rw [← exp_log hγ, ← hL] at h1
  have h2 := exp_le_exp.1 h1
  omega

open GlobalTheory.LKTrip GlobalTheory.LKGeo

theorem exists_prime (p : ℕ) [Fact p.Prime] (v : AwayP p) :
    ∃ l : ℕ, l.Prime ∧ l.Coprime p ∧ (l : ℤ) ∈ v.1.asIdeal := by
  set q : ℤ := Submodule.IsPrincipal.generator v.1.asIdeal with hq
  have hspan : v.1.asIdeal = Ideal.span {q} := (Submodule.IsPrincipal.span_singleton_generator v.1.asIdeal).symm
  have hq0 : q ≠ 0 := by
    intro h0
    apply v.1.ne_bot
    rw [hspan, h0, Ideal.span_singleton_eq_bot]
  have hqp : Prime q := by
    have := v.1.isPrime
    rw [hspan] at this
    exact (Ideal.span_singleton_prime hq0).1 this
  have hl : q.natAbs.Prime := Int.prime_iff_natAbs_prime.1 hqp
  have hspan' : v.1.asIdeal = Ideal.span {((q.natAbs : ℕ) : ℤ)} := by
    rw [hspan, Int.span_natAbs]
  refine ⟨q.natAbs, hl, (Nat.coprime_primes hl (Fact.out)).2 ?_, ?_⟩
  · intro he
    apply v.2
    rw [hspan', he]
  · rw [hspan']
    exact Ideal.subset_span rfl

theorem main : ∀ (p : ℕ) [Fact p.Prime] (α : AfP p),
    (∀ n : ℕ, 0 < n → n.Coprime p → ∃ β : AfP p, IsIntAf β ∧ α = n • β) → α = 0 := by
  intro p _ α h
  have hloc : ∀ v : AwayP p, AfP.eval v α = 0 := by
    intro v
    obtain ⟨l, hl, hlp, hlv⟩ := exists_prime p v
    apply eq_zero_of_dvd v.1
    intro k
    obtain ⟨β, hβ, hαβ⟩ := h (l ^ k) (pow_pos hl.pos k) (Nat.Coprime.pow_left k hlp)
    refine ⟨l ^ k, by push_cast; exact Ideal.pow_mem_pow hlv k, AfP.eval v β, hβ v, ?_⟩
    rw [hαβ, map_nsmul, nsmul_eq_mul]
  exact Subtype.ext (funext fun v => hloc v)

end GlobalTheory.AfPZero
