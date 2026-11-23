import Mathlib
import ReciprocityTheory.ThetaQuasiPeriods.PeriodLattice

noncomputable section

open Complex Matrix

namespace ReciprocityTheory.ChartRestriction.G.Key

open ReciprocityTheory.PTheta

def phSym {g : ℕ} (x : Matrix (Fin g) (Fin g) ℂ) : Matrix (Fin g) (Fin g) ℂ :=
  (1 / 2 : ℂ) • (x + xᵀ)

def phDom (g : ℕ) : Set (Fin g → Fin g → ℂ) :=
  {x | phSym (Matrix.of x) ∈ SiegelH (Fin g)}

def IsHoloSiegel (g : ℕ) (H : Matrix (Fin g) (Fin g) ℂ → ℂ) : Prop :=
  DifferentiableOn ℂ (fun x : Fin g → Fin g → ℂ => H (phSym (Matrix.of x))) (phDom g)

def IsPluriharmonicSiegel (g : ℕ) (u : Matrix (Fin g) (Fin g) ℂ → ℝ) : Prop :=
  ContDiffOn ℝ 2 (fun x : Fin g → Fin g → ℂ => u (phSym (Matrix.of x))) (phDom g) ∧
    ∀ τ ∈ SiegelH (Fin g), ∀ V : Matrix (Fin g) (Fin g) ℂ, V.IsSymm →
      InnerProductSpace.HarmonicAt (fun w : ℂ => u (τ + w • V)) 0

def phActC {g : ℕ} (γ : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℂ) (τ : Matrix (Fin g) (Fin g) ℂ) :
    Matrix (Fin g) (Fin g) ℂ :=
  (γ.toBlocks₁₁ * τ + γ.toBlocks₁₂) * (γ.toBlocks₂₁ * τ + γ.toBlocks₂₂)⁻¹

def phAct {g : ℕ} (γ : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ) (τ : Matrix (Fin g) (Fin g) ℂ) :
    Matrix (Fin g) (Fin g) ℂ :=
  phActC (γ.map (Int.cast : ℤ → ℂ)) τ

def IsSpInvariant {α : Type*} (g : ℕ) (f : Matrix (Fin g) (Fin g) ℂ → α) : Prop :=
  ∀ γ ∈ Matrix.symplecticGroup (Fin g) ℤ, ∀ τ ∈ SiegelH (Fin g), f (phAct γ τ) = f τ

def PhStatement : Prop :=
  ∀ g : ℕ, 2 ≤ g → ∀ u : Matrix (Fin g) (Fin g) ℂ → ℝ, IsPluriharmonicSiegel g u →
    IsSpInvariant g u → ∃ c : ℝ, ∀ τ ∈ SiegelH (Fin g), u τ = c

def PhReStatement : Prop :=
  ∀ g : ℕ, ∀ u : Matrix (Fin g) (Fin g) ℂ → ℝ, IsPluriharmonicSiegel g u →
    ∃ H : Matrix (Fin g) (Fin g) ℂ → ℂ, IsHoloSiegel g H ∧ ∀ τ ∈ SiegelH (Fin g), (H τ).re = u τ

def PhInvStatement : Prop :=
  ∀ g : ℕ, 2 ≤ g → ∀ H : Matrix (Fin g) (Fin g) ℂ → ℂ, IsHoloSiegel g H →
    IsSpInvariant g (fun τ => (H τ).re) → IsSpInvariant g H

def PhKoecherStatement : Prop :=
  ∀ g : ℕ, 2 ≤ g → ∀ N : ℕ, 1 ≤ N → ∀ F : Matrix (Fin g) (Fin g) ℂ → ℂ, IsHoloSiegel g F →
    (∀ B : Matrix (Fin g) (Fin g) ℤ, B.IsSymm → ∀ τ ∈ SiegelH (Fin g),
        F (τ + (N : ℂ) • B.map (Int.cast : ℤ → ℂ)) = F τ) →
    (∀ U : Matrix (Fin g) (Fin g) ℤ, U.det = 1 → (∀ i j, (N : ℤ) ∣ U i j - (1 : Matrix (Fin g) (Fin g) ℤ) i j) →
        ∀ τ ∈ SiegelH (Fin g),
          F (U.map (Int.cast : ℤ → ℂ) * τ * (U.map (Int.cast : ℤ → ℂ))ᵀ) = F τ) →
    ∀ c : ℝ, 0 < c → ∃ K : ℝ, ∀ τ ∈ SiegelH (Fin g),
      (τ.map Complex.im - c • (1 : Matrix (Fin g) (Fin g) ℝ)).PosSemidef → ‖F τ‖ ≤ K

def PhHoloStatement : Prop :=
  ∀ g : ℕ, 2 ≤ g → ∀ H : Matrix (Fin g) (Fin g) ℂ → ℂ, IsHoloSiegel g H → IsSpInvariant g H →
    ∃ c : ℂ, ∀ τ ∈ SiegelH (Fin g), H τ = c

end ReciprocityTheory.ChartRestriction.G.Key
