import Mathlib
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.DiscreteSpectrumKFiniteDecomposition

open MeasureTheory Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec
open scoped InnerProductSpace ComplexOrder ContDiff

noncomputable section

namespace GlobalTheory.DSId

def IsHCDS {n : ℕ} (ε : Fin n → Bool) (lam : Fin n → ℝ) {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) : Prop :=
  IsSqIntIrr ε σ ∧ HasInfChar ε (fun a => (lam a : ℂ)) σ ∧ (∃! S : Submodule ℂ H, IsKTypeOf ε σ (lowK ε lam) S) ∧
    ∀ (μ : Fin n → ℝ) (S : Submodule ℂ H), IsKTypeOf ε σ μ S →
      ∃ c : Fin n → Fin n → ℕ, (∀ a b, c a b ≠ 0 → a < b) ∧ μ = lowK ε lam + ∑ a, ∑ b, (c a b : ℝ) • root a b

def DSClass : Prop :=
  ∀ n : ℕ, ∃ (H : (Fin n → Bool) → (Fin n → ℝ) → Type) (_ : ∀ ε lam, NormedAddCommGroup (H ε lam))
    (_ : ∀ ε lam, InnerProductSpace ℂ (H ε lam)) (π : ∀ ε lam, Matrix (Fin n) (Fin n) ℂ → (H ε lam →L[ℂ] H ε lam)),
    (∀ ε lam, IsHCParam lam → IsHCDS ε lam (π ε lam)) ∧
    ∀ (ε : Fin n → Bool) (H' : Type) [NormedAddCommGroup H'] [InnerProductSpace ℂ H'] (σ' : Matrix (Fin n) (Fin n) ℂ → (H' →L[ℂ] H')), IsSqIntIrr ε σ' →
      ∃ (s : Equiv.Perm (Fin n)) (mu : Fin n → ℝ), IsHCParam mu ∧ (∀ a b, a < b → ε (s a) = ε (s b) → s a < s b) ∧
        UEquiv (ε ∘ s) (fun g => σ' (g.submatrix s.symm s.symm)) (π (ε ∘ s) mu)

def StrictLow : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ), IsHCParam lam →
    ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), IsDS ε lam σ →
      IsKTypeOf ε σ (lowK ε lam) (lowKSub ε lam σ) ∧
        ∀ (μ : Fin n → ℝ) (S : Submodule ℂ H), IsKTypeOf ε σ μ S → μ ≠ lowK ε lam →
          vNormSq ε (lowK ε lam) < vNormSq ε μ

def EigenfunctionFiniteCoefficients : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (χ : Fin n → ℂ) (f : Matrix (Fin n) (Fin n) ℂ → ℂ), IsZEigen ε χ f → IsBiKFin ε f →
    MemLp (fun g : UJ ε => f (umat g)) 2 (muG ε) →
    ∃ (N : ℕ) (H : Fin N → Type) (_ : ∀ i, NormedAddCommGroup (H i)) (_ : ∀ i, InnerProductSpace ℂ (H i))
      (σ : ∀ i, Matrix (Fin n) (Fin n) ℂ → (H i →L[ℂ] H i)) (u v : ∀ i, H i),
      (∀ i, IsSqIntIrr ε (σ i)) ∧ ∀ g ∈ UJset ε, f g = ∑ i, ⟪v i, σ i g (u i)⟫_ℂ

def SphUnique : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), IsHCParam lam → IsDS ε lam σ →
    ∀ F : H → H → Matrix (Fin n) (Fin n) ℂ → ℂ,
      (∀ g ∈ UJset ε, ∃ A : lowKSub ε lam σ →ₗ[ℂ] lowKSub ε lam σ,
        ∀ x y : lowKSub ε lam σ, F y x g = ⟪(y : H), (A x : H)⟫_ℂ) →
      (∀ x ∈ lowKSub ε lam σ, ∀ y ∈ lowKSub ε lam σ,
        (∀ k₁ ∈ Kset ε, ∀ k₂ ∈ Kset ε, ∀ g ∈ UJset ε, F y x (k₁ * g * k₂) = F (σ k₁⁻¹ y) (σ k₂ x) g) ∧
        F y x 1 = ⟪y, x⟫_ℂ ∧ IsZEigen ε (fun a => (lam a : ℂ)) (F y x) ∧
        MemLp (fun g : UJ ε => F y x (umat g)) 2 (muG ε)) →
      ∀ x ∈ lowKSub ε lam σ, ∀ y ∈ lowKSub ε lam σ, ∀ g ∈ UJset ε, F y x g = ⟪y, σ g x⟫_ℂ

def FormulaGap : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), IsHCParam lam → IsDS ε lam σ →
    ∀ h : ℝ, GapAtLeast ε lam h → 120 * (n : ℝ) * ((rkR ε : ℕ) : ℝ) ^ ((3 : ℝ) / 2) ≤ h → ∀ w, IsHighestUnit ε lam σ w →
    ∀ X, inP ε X → ∀ u ∈ lowKSub ε lam σ, ∀ v ∈ lowKSub ε lam σ,
      ⟪v, σ (NormedSpace.exp X) u⟫_ℂ = (Module.finrank ℂ (lowKSub ε lam σ) : ℂ) *
        ∫ k' : KG ε, Phi lam ((toMK k')⁻¹ * NormedSpace.exp X * toMK k') *
          (⟪v, σ (toMK k') w⟫_ℂ * ⟪σ (toMK k') w, u⟫_ℂ) ∂(muK ε)

def DecGap : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), IsHCParam lam → IsDS ε lam σ →
    ∀ h : ℝ, GapAtLeast ε lam h → 120 * (n : ℝ) * ((rkR ε : ℕ) : ℝ) ^ ((3 : ℝ) / 2) ≤ h → ∀ g ∈ UJset ε,
    ∀ u ∈ lowKSub ε lam σ, ∀ v ∈ lowKSub ε lam σ,
      ‖⟪v, σ g u⟫_ℂ‖ ≤ decHS h (rkR ε) (dHS g) * ‖u‖ * ‖v‖ ∧ ‖⟪v, σ g u⟫_ℂ‖ ≤ decE (rkR ε) h (dOp g) * ‖u‖ * ‖v‖

end GlobalTheory.DSId
