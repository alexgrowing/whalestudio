import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ToricSymbols
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.LatticeNormTransport

noncomputable section

open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.HeckeGal
open GlobalTheory.IndefiniteRowSideFullHecke.ToricSymbols (IsTwistedSum IsSymbol conjChar classOf)
open GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport (IsConjWt IsConjChar lamF upIdele)

namespace GlobalTheory.ToricTransport

def coordIn (E : Type) [Field E] [NumberField E] {I : Type} [Fintype I] (d s : ℕ) (κ : I → ℕ) (Ω T : ℂ) : ℂ :=
  (C0 E d (2 * s) κ : ℂ) * T / Ω ^ (2 * s * Fintype.card I + 2 * ∑ i, κ i)

def IsDatum {K E : Type} [Field K] [Field E] [NumberField E] [Algebra K E] {I : Type} [Fintype I] (ι : K →+* ℂ)
    (φ : I → E →+* ℂ) (s : ℕ) (κ : I → ℕ) (𝔣 : Ideal (OF E)) (Q : Finset (HeightOneSpectrum (OF E))) (χ : HChar E) : Prop :=
  UnramFin E ∧ IsCMType φ ∧ (∀ i, (φ i).comp (algebraMap K E) = ι) ∧ 1 ≤ s ∧ (∀ i, 1 ≤ κ i) ∧ IsBaseCond 𝔣 ∧ IsFinSetSplitPlacesCoprimeConductor 𝔣 Q ∧
    IsValChar φ s κ 𝔣 ∅ χ

def TwistedTransport : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (d : ℕ) (δ : K) (ι : K →+* ℂ),
    Module.finrank ℚ K = 2 → 0 < d → δ ^ 2 = -(d : K) →
    ∃ Ω₀ : ℂ, Ω₀ ≠ 0 ∧
      (∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [Algebra K E] (I : Type) [Fintype I] (φ : I → E →+* ℂ) (s : ℕ)
        (κ : I → ℕ) (𝔣 : Ideal (OF E)) (Q : Finset (HeightOneSpectrum (OF E))) (χ : HChar E), IsDatum ι φ s κ 𝔣 Q χ →
        ∀ (ψ : PicO (condQ 𝔣 Q) →* ℂˣ) (T : ℂ), IsTwistedSum φ s κ (condQ 𝔣 Q) χ ψ T → IsAlgebraic ℚ (coordIn E d s κ Ω₀ T)) ∧
      ∀ (Ω : Type) [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω] (j : Ω →+* ℂ) (art : Ideles K →* Gab K Ω),
        j.comp (algebraMap K Ω) = ι → IsGlobalArtin art →
        ∀ (g : ℂ ≃+* ℂ) (σ : Formalism.ConjugateSelfDual.G K Ω) (t : (Af K)ˣ), (∀ x, j (σ x) = g (j x)) → IsSymbol art t σ →
        ∃ Ω₁ : ℂ, Ω₁ ≠ 0 ∧
          ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [Algebra K E] (I : Type) [Fintype I] (φ : I → E →+* ℂ) (s : ℕ)
            (κ : I → ℕ) (𝔣 : Ideal (OF E)) (Q : Finset (HeightOneSpectrum (OF E))) (χ : HChar E), IsDatum ι φ s κ 𝔣 Q χ →
            ∀ (κ' : I → ℕ) (χ' : HChar E), IsConjWt φ g κ κ' → IsConjChar φ s κ' g χ χ' →
            ∀ (ψ : PicO (condQ 𝔣 Q) →* ℂˣ) (T T' : ℂ), IsTwistedSum φ s κ (condQ 𝔣 Q) χ ψ T →
              IsTwistedSum φ s κ' (condQ 𝔣 Q) χ' (conjChar g ψ) T' →
              g (coordIn E d s κ Ω₀ T) =
                coordIn E d s κ Ω₁ ((((modF t : ℝ) : ℂ) ^ (∑ i, κ i))⁻¹ *
                  (lamF s χ' (upIdele K E t) * ((conjChar g ψ (classOf K (condQ 𝔣 Q) t) : ℂˣ) : ℂ))⁻¹ * T')

example (E : Type) [Field E] [NumberField E] {I : Type} [Fintype I] (d s : ℕ) (κ : I → ℕ) (Ω T : ℂ) (Λ : PeriodPair)
    (h : Ω ^ 12 = latDisc Λ) : coordIn E d s κ Ω T ^ 12 = beta E d s κ Λ T := by
  rw [beta_eq, coordIn, div_pow, ← h, ← pow_mul, ← pow_mul, mul_comm 12]

theorem coordIn_div (E : Type) [Field E] [NumberField E] {I : Type} [Fintype I] {d s : ℕ} (hd : 0 < d) (hs : 1 ≤ s) (κ : I → ℕ)
    {Ω : ℂ} (hΩ : Ω ≠ 0) (T T₀ : ℂ) : coordIn E d s κ Ω T / coordIn E d s κ Ω T₀ = T / T₀ := by
  have hC : (C0 E d (2 * s) κ : ℂ) ≠ 0 := by exact_mod_cast (cmValueConst_pos E hd (by omega) κ).ne'
  rw [coordIn, coordIn, div_div_div_cancel_right₀ (pow_ne_zero _ hΩ), mul_div_mul_left _ _ hC]

end GlobalTheory.ToricTransport
