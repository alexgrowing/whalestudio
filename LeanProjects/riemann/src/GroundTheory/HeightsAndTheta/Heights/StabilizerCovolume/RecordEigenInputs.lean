import Mathlib
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.NineStatements

open NumberField IsDedekindDomain
open scoped nonZeroDivisors

def logRd (E : Type) [Field E] [NumberField E] : ℝ :=
  Real.log |(NumberField.discr E : ℝ)| / Module.finrank ℚ E

def extDifferent {E L : Type} [Field E] [NumberField E] [Field L] [NumberField L] (ι : E →+* L) :
    Ideal (𝓞 L) :=
  Ideal.map (RingOfIntegers.mapRingHom ι) (differentIdeal ℤ (𝓞 E))

def primeFrac (L : Type) [Field L] [NumberField L] (p : ℕ) : FractionalIdeal (𝓞 L)⁰ L :=
  ((Ideal.span {(p : 𝓞 L)} : Ideal (𝓞 L)) : FractionalIdeal (𝓞 L)⁰ L)

def PrimeLogSum.Statement : Prop :=
  ∃ C : ℝ, ∀ B : ℕ, 2 ≤ B → ∀ P : Finset ℕ, (∀ p ∈ P, p.Prime) → P.card ≤ B →
    ∑ p ∈ P, Real.log p / ((p : ℝ) - 1) ≤ C * Real.log B

def LocalCountBound {L : Type} [Field L] [NumberField L] (𝔠 : FractionalIdeal (𝓞 L)⁰ L) (𝔇 : Ideal (𝓞 L))
    (S : Finset ℕ) (a b : ℝ) : Prop :=
  ∀ p : ℕ, p.Prime → ∀ 𝔓 : HeightOneSpectrum (𝓞 L), (p : 𝓞 L) ∈ 𝔓.asIdeal →
    |(FractionalIdeal.count L 𝔓 𝔠 : ℝ)| ≤
      (if p ∈ S then a * (FractionalIdeal.count L 𝔓 (primeFrac L p) : ℝ) / ((p : ℝ) - 1) else 0) +
        b * (FractionalIdeal.count L 𝔓 (𝔇 : FractionalIdeal (𝓞 L)⁰ L) : ℝ)

def NormCountBound.Statement : Prop :=
  ∀ (L : Type) [Field L] [NumberField L] (𝔠 : FractionalIdeal (𝓞 L)⁰ L) (𝔇 : Ideal (𝓞 L)) (S : Finset ℕ)
    (a b : ℝ), 𝔠 ≠ 0 → 𝔇 ≠ ⊥ → 0 ≤ a → 0 ≤ b → LocalCountBound 𝔠 𝔇 S a b →
    |Real.log (FractionalIdeal.absNorm 𝔠 : ℝ)| ≤
      Module.finrank ℚ L * (a * ∑ p ∈ S, Real.log p / ((p : ℝ) - 1)) + b * Real.log (Ideal.absNorm 𝔇 : ℝ)

def DifferentExtNorm.Statement : Prop :=
  ∀ (E L : Type) [Field E] [NumberField E] [Field L] [NumberField L] (ι : E →+* L),
    extDifferent ι ≠ ⊥ ∧
      Real.log (Ideal.absNorm (extDifferent ι) : ℝ) = Module.finrank ℚ L * logRd E

theorem natCast_notMem_of_ne {L : Type} [Field L] [NumberField L] {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hpq : p ≠ q) (𝔓 : HeightOneSpectrum (𝓞 L)) (h : (p : 𝓞 L) ∈ 𝔓.asIdeal) : (q : 𝓞 L) ∉ 𝔓.asIdeal := by
  intro hq'
  obtain ⟨u, v, huv⟩ : IsCoprime (p : ℤ) (q : ℤ) :=
    Nat.isCoprime_iff_coprime.mpr ((Nat.coprime_primes hp hq).mpr hpq)
  apply 𝔓.isPrime.ne_top
  rw [Ideal.eq_top_iff_one]
  have h1 : ((u * p + v * q : ℤ) : 𝓞 L) = 1 := by rw [huv]; simp
  rw [← h1]
  push_cast
  exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ h) (Ideal.mul_mem_left _ _ hq')

theorem primeSpan_ne_bot {L : Type} [Field L] [NumberField L] {q : ℕ} (hq : q.Prime) :
    (Ideal.span {(q : 𝓞 L)} : Ideal (𝓞 L)) ≠ ⊥ := by
  rw [Ne, Ideal.span_singleton_eq_bot]
  exact_mod_cast hq.ne_zero

theorem count_primeFrac_of_ne {L : Type} [Field L] [NumberField L] {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hpq : p ≠ q) (𝔓 : HeightOneSpectrum (𝓞 L)) (h : (p : 𝓞 L) ∈ 𝔓.asIdeal) :
    FractionalIdeal.count L 𝔓 (primeFrac L q) = 0 := by
  classical
  have hJ := primeSpan_ne_bot (L := L) hq
  rw [primeFrac, FractionalIdeal.count_coe L 𝔓 hJ, Nat.cast_eq_zero]
  by_contra hc
  have hd := (Associates.count_ne_zero_iff_dvd hJ 𝔓.irreducible).mp hc
  exact natCast_notMem_of_ne hp hq hpq 𝔓 h
    ((Ideal.dvd_iff_le.mp hd) (Ideal.subset_span (Set.mem_singleton _)))

theorem primeFrac_ne_zero (L : Type) [Field L] [NumberField L] {q : ℕ} (hq : q.Prime) : primeFrac L q ≠ 0 := by
  rw [primeFrac, Ne, FractionalIdeal.coeIdeal_eq_zero]
  exact primeSpan_ne_bot hq

end GroundTheory.Heights₂.Heights.NineStatements
