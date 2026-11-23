import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.AllLeaves

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Rs

namespace PositivityTheory.Rg.BcB.SpectralAccumulation.FD

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {N : ℕ}

def sat (Ω : Set (GA E N)) : Set (GA E N) := {g | ∃ γ ∈ latticeGL E N, γ * g ∈ Ω}

def FDEx : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (N : ℕ) [MeasurableSpace (GA E N)]
  [BorelSpace (GA E N)] (μ : Measure (GA E N)) [μ.IsHaarMeasure], ∃ 𝓕 : Set (GA E N), IsFundamentalDomain (latticeGL E N) 𝓕 μ

def SqIntAt : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (N : ℕ) [MeasurableSpace (GA E N)]
  [BorelSpace (GA E N)] (μ : Measure (GA E N)) [μ.IsHaarMeasure] (𝓕 : Set (GA E N)), IsFundamentalDomain (latticeGL E N) 𝓕 μ →
  ∀ φ : Sm E N, IsAutForm φ → IsSqInt φ.1 → ∫⁻ g in 𝓕, ‖φ.1 g‖ₑ ^ 2 ∂μ < ⊤

def Orth : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (N : ℕ) [MeasurableSpace (GA E N)]
  [BorelSpace (GA E N)] (μ : Measure (GA E N)) [μ.IsHaarMeasure] (𝓕 : Set (GA E N)), IsFundamentalDomain (latticeGL E N) 𝓕 μ →
  ∀ V V' : Submodule ℂ (Sm E N), IsDiscrete V → IsDiscrete V' → ¬ IsoV V V' →
    ∀ φ ∈ V, ∀ ψ ∈ V', ∫ g in 𝓕, φ.1 g * (starRingEnd ℂ) (ψ.1 g) ∂μ = 0

def Mass : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (N : ℕ) [MeasurableSpace (GA E N)]
  [BorelSpace (GA E N)] (μ : Measure (GA E N)) [μ.IsHaarMeasure] (𝓕 : Set (GA E N)), IsFundamentalDomain (latticeGL E N) 𝓕 μ →
  ∀ (K : Subgroup (GL (Fin N) (Af E))) (W : Submodule ℂ (Kinf E N → ℂ)) (R ε : ℝ), IsOpen (K : Set (GL (Fin N) (Af E))) →
    FiniteDimensional ℂ W → 0 < ε →
  ∃ Ω : Set (GA E N), IsCompact Ω ∧ ∀ V : Submodule ℂ (Sm E N), IsDiscrete V → InfBdd R V →
    (∀ r, 0 < r → r < N → ∀ c ∈ ExpV r V, pE E N r c ≤ -ε * (r * ((N : ℝ) - r))) → ∀ φ ∈ V, TypeB K W φ →
      ∫⁻ g in 𝓕, ‖φ.1 g‖ₑ ^ 2 ∂μ ≤ 2 * ∫⁻ g in 𝓕 ∩ sat Ω, ‖φ.1 g‖ₑ ^ 2 ∂μ

def Bessel : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (N : ℕ) [MeasurableSpace (GA E N)]
  [BorelSpace (GA E N)] (μ : Measure (GA E N)) [μ.IsHaarMeasure] (𝓕 : Set (GA E N)), IsFundamentalDomain (latticeGL E N) 𝓕 μ →
  ∀ (α : GA E N → ℂ) (δ : ℝ) (Ω : Set (GA E N)), Continuous α → HasCompactSupport α → 0 < δ → IsCompact Ω →
  ∃ C : ℕ, ∀ (k : ℕ) (ψ : Fin k → GA E N → ℂ), (∀ i, Continuous (ψ i)) →
    (∀ i, ∀ γ ∈ latticeGL E N, ∀ g, ψ i (γ * g) = ψ i g) →
    (∀ i j, ∫ g in 𝓕, ψ i g * (starRingEnd ℂ) (ψ j g) ∂μ = if i = j then 1 else 0) →
    (∀ i, ∃ s : ℂ, δ ≤ ‖s‖ ∧ ∀ x, ∫ y, α y * ψ i (x * y) ∂μ = s * ψ i x) →
    (∀ i, (1 : ENNReal) ≤ 2 * ∫⁻ g in 𝓕 ∩ sat Ω, ‖ψ i g‖ₑ ^ 2 ∂μ) → k ≤ C

def ContAF : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (N : ℕ) (φ : Sm E N), IsAutForm φ → Continuous φ.1

def PosNorm : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (N : ℕ) [MeasurableSpace (GA E N)]
  [BorelSpace (GA E N)] (μ : Measure (GA E N)) [μ.IsHaarMeasure] (𝓕 : Set (GA E N)), IsFundamentalDomain (latticeGL E N) 𝓕 μ →
  ∀ φ : Sm E N, IsAutForm φ → IsSqInt φ.1 → φ ≠ 0 → 0 < ∫⁻ g in 𝓕, ‖φ.1 g‖ₑ ^ 2 ∂μ

end PositivityTheory.Rg.BcB.SpectralAccumulation.FD

end
