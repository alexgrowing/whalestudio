import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.GLMatrixDerivatives.KchainSt

noncomputable section

open Matrix Finset
open scoped ContDiff

namespace PositivityTheory.RgBcC.LfSt.Kchain

open PositivityTheory.RgBcC PositivityTheory.RgBcC.LfSt
open PositivityTheory.RgTw (Mat hb)

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

def HalfOne : Prop :=
  ∀ (n : ℕ) (lam : Fin n → ℤ) E Fr ε ι S Γ T, CxData lam E Fr ε ι S Γ T →
    ∀ (σ : (Fin n × Fin n → ℝ) → Mat n), ContDiffOn ℝ ∞ σ (cone n) → (∀ v ∈ cone n, σ v * (σ v)ᴴ = hOf v) →
    ∀ (k : Mat n → (E.V →L[ℂ] E.V)), ContDiffOn ℝ ∞ k (GLs n) →
    (∀ y ∈ GLs n, ∀ k₁ k₂ : Matrix.unitaryGroup (Fin n) ℂ, k (k₁.1 * y * k₂.1) = E.ρ k₁ * k y * E.ρ k₂) →
    ∀ (d : Mat n), d ∈ GLs n → ∀ c : ℝ, ∀ v ∈ cone n, ∀ w ∈ cone n,
      ∑ i, ε (hb i) * fderiv ℝ (Kc σ c Fr k Γ T d) (v, w) (Pi.single i 1, 0) =
        ((c : ℂ) * ((hOf w).det ^ n)⁻¹) • (Fr (σ v) * ((1 / 2 : ℂ) • ∑ p, ε (hb p) *
          (fderiv ℝ Fr 1 (hb p) * k ((σ v)⁻¹ * d * (σ w)ᴴ⁻¹) + Ld (hb p) k ((σ v)⁻¹ * d * (σ w)ᴴ⁻¹))) * Γ * T * Fr (σ w)⁻¹)

def HalfTwo : Prop :=
  ∀ (n : ℕ) (lam : Fin n → ℤ) E Fr ε ι S Γ T, CxData lam E Fr ε ι S Γ T →
    ∀ (σ : (Fin n × Fin n → ℝ) → Mat n), ContDiffOn ℝ ∞ σ (cone n) → (∀ v ∈ cone n, σ v * (σ v)ᴴ = hOf v) →
    ∀ (k : Mat n → (E.V →L[ℂ] E.V)), ContDiffOn ℝ ∞ k (GLs n) →
    (∀ y ∈ GLs n, ∀ k₁ k₂ : Matrix.unitaryGroup (Fin n) ℂ, k (k₁.1 * y * k₂.1) = E.ρ k₁ * k y * E.ρ k₂) →
    ∀ (d : Mat n), d ∈ GLs n → ∀ c : ℝ, ∀ v ∈ cone n, ∀ w ∈ cone n,
      ∑ i, fderiv ℝ (Kc σ c Fr k Γ T d) (v, w) (0, Pi.single i 1) * ε (hb i) =
        ((c : ℂ) * ((hOf w).det ^ n)⁻¹) • (Fr (σ v) * ((1 / 2 : ℂ) • ∑ p,
          (Rd (hb p) k ((σ v)⁻¹ * d * (σ w)ᴴ⁻¹) * ε (hb p) -
            k ((σ v)⁻¹ * d * (σ w)ᴴ⁻¹) * ε (hb p) * fderiv ℝ Fr 1 (hb p))) * Γ * T * Fr (σ w)⁻¹)

end PositivityTheory.RgBcC.LfSt.Kchain
