import Mathlib
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.SmulCommClassGalIntegers

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FieldSize

open NumberField IsDedekindDomain

def Sz (F : IntermediateField ℚ ℂ) (a b : ℝ) : Prop :=
  ∃ _ : FiniteDimensional ℚ F, letI : NumberField F := NumberField.mk
    Real.log (Module.finrank ℚ F) ≤ a ∧ Real.log |((NumberField.discr F : ℤ) : ℝ)| / Module.finrank ℚ F ≤ b

def IsRay {K : Type} [Field K] [NumberField K] (L : Type) [Field L] [NumberField L] [Algebra K L] (𝔮 : Ideal (𝓞 K)) : Prop :=
  (∀ 𝔭 : HeightOneSpectrum (𝓞 K), ¬ 𝔭.asIdeal ∣ 𝔮 → GlobalTheory.NT.UnramIn L 𝔭) ∧
  Subgroup.closure {σ : L ≃ₐ[K] L | ∃ 𝔭 : HeightOneSpectrum (𝓞 K), ¬ 𝔭.asIdeal ∣ 𝔮 ∧ GlobalTheory.NT.IsFrob L 𝔭 σ} = ⊤ ∧
  ∀ I : Ideal (𝓞 K), I ≠ ⊥ → IsCoprime I 𝔮 →
    ((∀ χ : (L ≃ₐ[K] L) →* ℂˣ, GlobalTheory.NT.heckeIdeal L χ I = 1) ↔
      ∃ α β : 𝓞 K, GlobalTheory.NT.RayPair 𝔮 α β ∧ I * Ideal.span {β} = Ideal.span {α})

def weberSet (L : PeriodPair) (n : ℕ) : Set ℂ :=
  insert (L.g₂ ^ 3 / (L.g₂ ^ 3 - 27 * L.g₃ ^ 2))
    {w | ∃ z ∈ L.lattice, z / n ∉ L.lattice ∧ w = L.g₂ * L.g₃ / (L.g₂ ^ 3 - 27 * L.g₃ ^ 2) * L.weierstrassP (z / n)}

theorem finiteDimensional_of_sz {F : IntermediateField ℚ ℂ} {a b : ℝ} (h : Sz F a b) : FiniteDimensional ℚ F := h.1

end GlobalTheory.FieldSize
