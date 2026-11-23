import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.WittExactSequences.IsCompl
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PfFacts

open TensorProduct CrystallineSemistableComparison.D
open scoped LaurentPolynomial

namespace GlobalTheory.CompanionTheory.PerfectRing

theorem mul_eq_zero_of_C_pow_mem_span (K : Type) [CommRing K]
    (hred : ∀ (x : K) (n : ℕ), x ^ n = 0 → x = 0) (f g a : K) (n : ℕ)
    (h : (Polynomial.C a) ^ n ∈
      Ideal.span {Polynomial.C f - Polynomial.X * Polynomial.C g}) : g * a = 0 := by
  let L := Localization.Away g
  let u : L := IsLocalization.Away.invSelf g
  have hu : algebraMap K L g * u = 1 := IsLocalization.Away.mul_invSelf g
  let φ : Polynomial K →+* L := Polynomial.eval₂RingHom (algebraMap K L) (u * algebraMap K L f)
  have h0 : φ (Polynomial.C f - Polynomial.X * Polynomial.C g) = 0 := by
    have e1 : φ (Polynomial.C f) = algebraMap K L f := by simp [φ]
    have e2 : φ Polynomial.X = u * algebraMap K L f := by simp [φ]
    have e3 : φ (Polynomial.C g) = algebraMap K L g := by simp [φ]
    rw [map_sub, map_mul, e1, e2, e3]
    linear_combination (-(algebraMap K L f)) * hu
  have h1 : φ ((Polynomial.C a) ^ n) = 0 := by
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 h
    rw [← hc, map_mul, h0, mul_zero]
  have h2 : algebraMap K L (a ^ n) = 0 := by
    have e : φ ((Polynomial.C a) ^ n) = algebraMap K L (a ^ n) := by simp [φ]
    rw [← e, h1]
  obtain ⟨⟨m, hm⟩, e⟩ := (IsLocalization.map_eq_zero_iff (Submonoid.powers g) L _).1 h2
  obtain ⟨M, rfl⟩ := hm
  have e' : g ^ M * a ^ n = 0 := e
  apply hred _ (M + n)
  calc (g * a) ^ (M + n) = g ^ n * a ^ M * (g ^ M * a ^ n) := by ring
    _ = 0 := by rw [e', mul_zero]

theorem b_inj : ∀ (p : ℕ) [Fact p.Prime] (K : Type) [CommRing K] (K₁ : Type) [CommRing K₁]
    (K₂ : Type) [CommRing K₂] (f g : K) (i₁ : Polynomial K →+* K₁) (i₂ : Polynomial K →+* K₂)
    (r : ℕ → K) (N : ℕ), Pf p K → IsRt p r → r 0 ^ N ∈ Ideal.span {f, g} →
    PQ p i₁ (Ideal.span {Polynomial.C f - Polynomial.X * Polynomial.C g}) →
    PQ p i₂ (Ideal.span {Polynomial.C g - Polynomial.X * Polynomial.C f}) →
    ∀ a : K, i₁ (Polynomial.C a) = 0 → i₂ (Polynomial.C a) = 0 → ∀ k, r k * a = 0 := by
  intro p _ K _ K₁ _ K₂ _ f g i₁ i₂ r N hK hr hN h₁ h₂ a ha₁ ha₂
  obtain ⟨-, hred, -, -, hroots⟩ := pf_facts p K hK
  obtain ⟨k₁, hk₁⟩ := (h₁.ker _).1 ha₁
  obtain ⟨k₂, hk₂⟩ := (h₂.ker _).1 ha₂
  have hg : g * a = 0 := mul_eq_zero_of_C_pow_mem_span K hred f g a _ hk₁
  have hf : f * a = 0 := mul_eq_zero_of_C_pow_mem_span K hred g f a _ hk₂
  obtain ⟨u, v, huv⟩ := Ideal.mem_span_pair.1 hN
  have h0 : r 0 ^ N * a = 0 := by
    rw [← huv]
    linear_combination u * hf + v * hg
  exact (hroots r hr).2.2 N a h0

end GlobalTheory.CompanionTheory.PerfectRing
