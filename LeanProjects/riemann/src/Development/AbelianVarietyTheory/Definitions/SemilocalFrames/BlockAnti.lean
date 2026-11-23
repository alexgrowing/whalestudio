import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.UpperOff

noncomputable section

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.Amp

def Zr (k r : ℕ) (g : Mat k r) : Matrix (Fin r) (Fin r) ℂ := fun a b => g (esI k r a) (eI k r b)

def BlockAnti {r : ℕ} (β : Fin r → ℕ) (Z : Matrix (Fin r) (Fin r) ℂ) : Prop :=
  Monotone β ∧ Z.det ≠ 0 ∧ (∀ a b, Z a b ≠ 0 → β a = β b) ∧
    ∀ a b a' b', Z a b ≠ 0 → Z a' b' ≠ 0 → β a = β a' → ‖Z a b‖ = ‖Z a' b'‖ ∧ (a = a' → b = b') ∧ (a < a' → b' < b)

def IsNormal (k r : ℕ) (β : Fin r → ℕ) (g : Mat k r) : Prop :=
  g ∈ GG k r ∧ (∀ a : Fin r, g⁻¹ *ᵥ bvec (eI k r a) ∈ Xst k r ∧ g *ᵥ bvec (eI k r a) ∈ Xst k r) ∧ BlockAnti β (Zr k r g)

def lebR (k r : ℕ) (β : Fin r → ℕ) : Measure (Mt k r) :=
  (volume : Measure (UTin β → ℂ)).map fun x => Matrix.of.symm (uEmb k r (upperIn β x))

def NormR (k r : ℕ) (γ : Mat k r) (s : ℝ) (μR : Measure (Mt k r)) : Prop :=
  ∃ n₁ ∈ Nset k r, ∃ n₂ ∈ Nset k r, ∃ (g₀ : Mat k r) (β : Fin r → ℕ), IsNormal k r β g₀ ∧ γ = n₁ * g₀ * n₂ ∧
    μR = (ENNReal.ofReal s • lebR k r β).map (conjM n₂⁻¹)

def muProd {k r : ℕ} (μW μN : Measure (Mt k r)) : Measure (Mt k r) :=
  (μW.prod μN).map fun p : Mt k r × Mt k r => lmulM (Matrix.of p.1) p.2

def OneSide {k r : ℕ} {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
    (z : Fin (2 * r + k + 1) → ℂ) (π : Mat k r → (Wp →L[ℂ] Wp)) (ψ : Mat k r → ℂ) (μG μW μN νS : Measure (Mt k r))
    (Φ : Mat k r → Wp) (c : ℝ) : Prop :=
  inWb k r z ∧ 0 < Tz k r z ∧ Nontrivial Wp ∧ IsURepOn (UWset k r z) π ∧ IsIrredOn (UWset k r z) π ∧
    IsHaarOn (GG k r) μG ∧ IsHaarOn (UWset k r z) μW ∧ μW Set.univ = 1 ∧ IsHaarOn (Nset k r) μN ∧
    IsQuotMeas μG (muProd μW μN) νS ∧ (∀ n ∈ Nset k r, ‖ψ n‖ = 1) ∧ IsSPsiEquiv z ψ π Φ ∧ ContinuousOn Φ (GG k r) ∧
    0 < c ∧ l2SG νS Φ = ENNReal.ofReal (c * Module.finrank ℂ Wp)

def MomBd {k r : ℕ} {Wp : Type} [NormedAddCommGroup Wp] (z : Fin (2 * r + k + 1) → ℂ) (νS : Measure (Mt k r))
    (Φ : Mat k r → Wp) (q : ℕ) (H₁ : ℝ) : Prop :=
  ∀ a : Fin (r + 1), ∫⁻ x, ENNReal.ofReal (lA k r z (Matrix.of x) a ^ (2 * q)) * (‖Φ (Matrix.of x)‖₊ : ℝ≥0∞) ^ 2 ∂νS ≤
    ENNReal.ofReal (H₁ ^ (2 * q)) * l2SG νS Φ

def absBd (k r : ℕ) (H₁ De D : ℝ) : ℝ :=
  (4 * r : ℝ) ^ (44 * r ^ 3) * H₁ ^ (24 * r ^ 3) * De ^ (14 * r ^ 2) *
    (8 * Real.pi * Real.exp 1 / k) ^ (r * (k - 2 - r)) * (D ^ (k - 2 - r))⁻¹

example : BlockAnti (r := 1) (fun _ => 0) !![2] := by
  refine ⟨monotone_const, by simp, fun _ _ _ => rfl, fun a b a' b' _ _ _ => ?_⟩
  fin_cases a; fin_cases b; fin_cases a'; fin_cases b'; simp

end GlobalTheory.Amp
