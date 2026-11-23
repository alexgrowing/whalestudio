import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.HasMultiplier

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Small

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]

def FinBounds (y : (Σ k, ι k) → Ω) {I : Type} [Fintype I] (w : I → Ω) (a₁ a' aτ aσ : K → ℤ) (τ σ : Ω)
    (q m₁ m₂ : ℕ) (u : MRing ι) (p : ℕ) [Fact p.Prime] (e a b : ℝ) : Prop :=
  ∀ z ∈ algPts p (mCoordIdeal y), aeval z u ≠ 0 → ∃ r₁ r' rτ rσ E φ : ℝ,
    0 < r₁ ∧ 0 < r' ∧ 0 < rτ ∧ 0 < rσ ∧ r₁ ^ q = r' ^ q * rτ ^ m₁ * rσ ^ m₂ ∧ φ ≤ 3 * E ∧
    (∀ v : I → PadicAlgCl p, (∀ i, HasVal y a₁ (w i) z (v i)) → (p : ℝ) ^ (-(e + φ)) * r₁ ≤ ‖v‖) ∧
    ValLe y aτ τ z ((p : ℝ) ^ (-(8 * E)) * rτ) ∧ ValLe y aσ σ z ((p : ℝ) ^ b * rσ) ∧
    supMet a' z ≤ (p : ℝ) ^ a * r'

def ArchBounds (y : (Σ k, ι k) → Ω) {F : Type} [Field F] [Algebra F Ω] {I : Type} [Fintype I] (w : I → Ω)
    (L : HermLine (fun _ : Unit => I)) (M : HermLine ι) (a₁ aτ aσ aε : K → ℤ) (τ σ ε : Ω)
    (q m₁ m₂ m₃ : ℕ) (u : MRing ι) (sg : F →+* ℂ) (A P R κ C : ℝ) : Prop :=
  ∀ z ∈ mcPts (mCoordIdeal y), LiesOver y sg z → aeval z u ≠ 0 → ∃ h₁ h' hτ hσ ρ : ℝ,
    0 < h₁ ∧ 0 < h' ∧ 0 < hτ ∧ 0 < hσ ∧ h₁ ^ q = h' ^ q * hτ ^ m₁ * hσ ^ m₂ ∧
    (∀ v : I → ℂ, (∀ i, HasVal y a₁ (w i) z (v i)) →
      v ≠ 0 ∧ Real.exp (-(A + 3 * ρ) / 2) * h₁ ≤ L.h fun x => v x.2) ∧
    ValLe y aτ τ z (Real.exp (4 * (2 * P - ρ) + R) * hτ) ∧ ValLe y aσ σ z (Real.exp κ * hσ) ∧
    ∀ x, HasVal y aε ε z x → ‖x‖ ^ m₃ * M.h z ≤ Real.exp C * h' ^ q

structure SectionInputs (y : (Σ k, ι k) → Ω) (F : Type) [Field F] [NumberField F] [Algebra F Ω] {I : Type}
    [Fintype I] (w : I → Ω) (L : HermLine (fun _ : Unit => I)) (M : HermLine ι) (q : ℕ) (cc C s : ℝ) where

  a₁ : K → ℤ

  a' : K → ℤ

  aτ : K → ℤ

  aσ : K → ℤ

  aε : K → ℤ

  τ : Ω

  σ : Ω

  ε : Ω

  m₁ : ℕ

  m₂ : ℕ

  m₃ : ℕ

  u : MRing ι

  S : Finset ℕ

  e : ℕ → ℝ

  a : ℕ → ℝ

  b : ℕ → ℝ

  c : ℕ → ℝ

  A : ℝ

  P : ℝ

  R : ℝ

  κ : (F →+* ℂ) → ℝ

  cinf : ℝ
  L_deg : L.a = fun _ => 1
  deg₁ : ∀ k, (q : ℤ) * a₁ k = q * a' k + m₁ * aτ k + m₂ * aσ k
  deg₂ : ∀ k, (q : ℤ) * a' k = M.a k + m₃ * aε k
  eight : 8 * m₁ = 3 * q
  τ_ne : τ ≠ 0
  σ_ne : σ ≠ 0
  ε_ne : ε ≠ 0
  ε_int : ε ∈ chartLatNm y aε 1
  u_off : IsFormOff (mCoordIdeal y) u
  S_prime : ∀ p ∈ S, p.Prime
  c_nonneg : ∀ p, 0 ≤ c p
  c_zero : ∀ p, p ∉ S → c p = 0
  c_ge : ∀ p : ℕ, p.Prime → ((q : ℝ) * (e p + a p) + m₂ * b p) * Real.log p ≤ q * c p
  fin : ∀ (p : ℕ) [Fact p.Prime], FinBounds y w a₁ a' aτ aσ τ σ q m₁ m₂ u p (e p) (a p) (b p)
  κ_conj : ∀ sg, κ (NumberField.ComplexEmbedding.conjugate sg) = κ sg
  arch : ∀ sg, ArchBounds y w L M a₁ aτ aσ aε τ σ ε q m₁ m₂ m₃ u sg A P R (κ sg) (q * (C * s))
  cinf_ge : (q : ℝ) * (A / 2 + 3 * P) + m₁ * R + m₂ * embMean κ ≤ q * cinf
  cc_ge : ∑ p ∈ S, c p + cinf ≤ cc

end GlobalTheory.CompanionTheory.Ar.Small
