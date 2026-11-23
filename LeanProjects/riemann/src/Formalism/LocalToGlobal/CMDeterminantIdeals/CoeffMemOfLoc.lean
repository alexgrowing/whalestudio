import Formalism.LocalToGlobal.CMDeterminantIdeals.StatementC

noncomputable section

namespace Formalism.L2.LamCM

open NumberField IsDedekindDomain
open scoped nonZeroDivisors ComplexOrder

def CMNumbers0 {K : Type} [Field K] [NumberField K] {g : ℕ} (abelian₂ : MLine K) (ℓ : Fin g → MLine K) (de : MLine K)
    (La logOm : ℝ) : Prop :=
  abelian₂.Good ∧ (∀ j, (ℓ j).Good) ∧ de.Good ∧ 1 ≤ La ∧
  ∑ j, (ℓ j).deg - (g : ℝ) * (Module.finrank ℚ K : ℝ) * Real.log La ≤ abelian₂.deg ∧ (∀ j, (ℓ j).ndeg = logOm / 2) ∧
  de.ndeg ≤ (1 / 2) * abelian₂.dual.ndeg + (g : ℝ) / 4 * Real.log (2 * Real.pi)

def CMNumbersLink : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (g : ℕ) (Lie : MLat K g) (ℓ : Fin g → MLine K) (u : Fin g → Fin g → K)
    (de : MLine K) (La logOm : ℝ), CMNumbers Lie ℓ u de La logOm → CMNumbers0 Lie.detLine ℓ de La logOm

def DegDe0 : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (g : ℕ) (abelian₂ : MLine K) (ℓ : Fin g → MLine K) (de : MLine K) (La logOm : ℝ),
    CMNumbers0 abelian₂ ℓ de La logOm → de.ndeg ≤ (g : ℝ) * (pDeg logOm + (1 / 2) * Real.log La)

def DegNN0 : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (g : ℕ) (abelian₂ : MLine K) (ℓ : Fin g → MLine K) (de : MLine K) (La logOm : ℝ)
    (V : Type) [Fintype V] (c : V → Fin g) (μ : V → ℕ) (n : ℕ), CMNumbers0 abelian₂ ℓ de La logOm →
    (lineNN de ℓ c μ n).Good ∧
    (lineNN de ℓ c μ n).ndeg ≤ (pDeg logOm + (1 / 2) * Real.log La) * ((∑ v, (μ v : ℝ)) + (g : ℝ) * n)

def LamNumber0 : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (g : ℕ) (abelian₂ : MLine K) (ℓ : Fin g → MLine K) (de : MLine K) (La logOm : ℝ)
    (V : Type) [Fintype V] (c : V → Fin g) (G : MvPolynomial V K) (μ : V →₀ ℕ) (n : ℕ) (S : (K →+* ℂ) → ℝ) (Rr : ℝ),
    CMNumbers0 abelian₂ ℓ de La logOm → MvPolynomial.coeff μ G ≠ 0 → MvPolynomial.coeff μ G ∈ (lineNN de ℓ c μ n).I →
    (∀ σ, 0 < S σ) → 0 < Rr →
    (∀ (σ : K →+* ℂ) (z : V → ℂ), (∀ v, ‖z v‖ * (ℓ (c v)).n σ ≤ 1) →
      ‖MvPolynomial.eval z (MvPolynomial.map σ G)‖ * de.n σ ^ n ≤ S σ * Rr ^ (∑ v, μ v)) →
    - ((pDeg logOm + (1 / 2) * Real.log La) * ((∑ v, (μ v : ℝ)) + (g : ℝ) * n)) - (∑ v, (μ v : ℝ)) * Real.log Rr ≤
      (∑ σ : K →+* ℂ, Real.log (S σ)) / (Module.finrank ℚ K : ℝ)

def HadamardLoc : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (g : ℕ) (abelian₂ : MLine K) (ℓ : Fin g → MLine K) (u : Fin g → Fin g → K)
    (B : HeightOneSpectrum (𝓞 K) → Matrix (Fin g) (Fin g) K) (H : (K →+* ℂ) → Matrix (Fin g) (Fin g) ℂ) (La : ℝ),
    abelian₂.I ≠ 0 → (∀ j, (ℓ j).Good) → LinearIndependent K u → 0 < La → (∀ σ, (H σ).PosDef) →
    (∀ σ, abelian₂.n σ = Real.sqrt (H σ).det.re) → (∀ p, IsLocGen p (B p).det abelian₂.I) →
    (∀ p j, ∃ c : K, IsLocGen p c (ℓ j).I ∧ ∀ i, p.valuation K (((B p)⁻¹.mulVec (c • u j)) i) ≤ 1) →
    (∀ σ j, ReciprocityTheory.MultiplicativeHeights.hq (H σ) (ReciprocityTheory.MultiplicativeHeights.embVec σ (u j)) ≤ (La * (ℓ j).n σ) ^ 2) →
    ∑ j, (ℓ j).deg - (g : ℝ) * (Module.finrank ℚ K : ℝ) * Real.log La ≤ abelian₂.deg

def CoeffMemOfLoc : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (g : ℕ) (ℓ : Fin g → MLine K) (de : MLine K) (V : Type) [Fintype V] (c : V → Fin g)
    (μ : V → ℕ) (n : ℕ) (cf : K), de.Good → (∀ j, (ℓ j).Good) →
    (∀ p : HeightOneSpectrum (𝓞 K), ∃ (t : K) (cl : Fin g → K), IsLocGen p t de.I ∧ (∀ j, IsLocGen p (cl j) (ℓ j).I) ∧
      p.valuation K (cf * ∏ v, cl (c v) ^ μ v) ≤ p.valuation K (t ^ n)) →
    cf ∈ (lineNN de ℓ c μ n).I

def DegGalois : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (γ : K ≃+* K) (L L' : MLine K), L.Good →
    (∀ x : K, γ x ∈ L'.I ↔ x ∈ L.I) → (∀ σ : K →+* ℂ, L'.n σ = L.n (σ.comp (γ : K →+* K))) → L'.deg = L.deg

end Formalism.L2.LamCM
