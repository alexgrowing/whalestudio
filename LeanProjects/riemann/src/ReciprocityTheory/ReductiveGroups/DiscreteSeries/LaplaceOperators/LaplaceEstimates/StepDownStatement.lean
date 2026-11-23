import ReciprocityTheory.ReductiveGroups.DiscreteSeries.IsInfUnitary
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.InterlacingWalks.LowerStepStatement
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.EquivariantL2Space
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.ReproducingKernels.ReproCoreStatement

noncomputable section

namespace ReciprocityTheory.ChartRestriction.DS.Lap

open ReciprocityTheory.ChartRestriction.DS Matrix

def StepGap {n : ℕ} (ε : Fin n → Bool) (r : ℕ) (h : ℝ) : Prop :=
  max (3 * (n : ℝ) / 2) (1 + (n : ℝ) * (pOf ε : ℝ) * (qOf ε : ℝ)) < h - 2 ∧
    4 * max (2 * (n : ℝ) * (min (pOf ε) (qOf ε) : ℝ)) (2 * (r : ℝ) * (n : ℝ) ^ 2) <
      h / (8 * Real.sqrt (2 * (min (pOf ε) (qOf ε) : ℝ))) - 1

def StepStatement : Prop :=
  S0.IntSStatement → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (u : Fin k → ℝ) (h : ℝ),
    StepGap ε r h → pOf ε = k + r → qOf ε = r + 1 →
    StepClosed ε u h (fun lam => BesselNZ ε lam u)

def StepDownStatement : Prop :=
  S0.IntSStatement → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (u : Fin k → ℝ) (h : ℝ), StepGap ε r h →
    pOf ε = k + r → qOf ε = r + 1 →
    ∀ (lam : Fin (2 * r + k + 1) → ℝ) (s : Fin (2 * r + k + 1)), IsHCPar lam → GapAtLeast ε lam h →
      IsHCPar (lam - Pi.single s 1) → GapAtLeast ε (lam - Pi.single s 1) h →
      (∀ j, u j ≠ lam s - 1 / 2) → BesselNZ ε lam u → BesselNZ ε (lam - Pi.single s 1) u

def StepUpStatement : Prop :=
  S0.IntSStatement → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (u : Fin k → ℝ) (h : ℝ), StepGap ε r h →
    pOf ε = k + r → qOf ε = r + 1 →
    ∀ (lam : Fin (2 * r + k + 1) → ℝ) (s : Fin (2 * r + k + 1)), IsHCPar lam → GapAtLeast ε lam h →
      IsHCPar (lam + Pi.single s 1) → GapAtLeast ε (lam + Pi.single s 1) h →
      (∀ j, u j ≠ lam s + 1 / 2) → BesselNZ ε lam u → BesselNZ ε (lam + Pi.single s 1) u

def xOne (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) : Fin (2 * r + k + 1) → ℂ :=
  if r = 0 then z else Pi.single (⟨0, by omega⟩ : Fin (2 * r + k + 1)) 1

def cMul (k r : ℕ) (z y : Fin (2 * r + k + 1) → ℂ) (g : Mat k r) : ℂ :=
  Formalism.QuantumDeterminants.herm (Formalism.QuantumDeterminants.Hpk k r) (g *ᵥ y) (xOne k r z)

def cMulD (k r : ℕ) (z β : Fin (2 * r + k + 1) → ℂ) (g : Mat k r) : ℂ :=
  β ⬝ᵥ (g⁻¹ *ᵥ xOne k r z)

def MultStatement : Prop :=
  ∀ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ), Formalism.QuantumDeterminants.inWb k r z →
    (∀ (y β : Fin (2 * r + k + 1) → ℂ), ∀ s ∈ Formalism.QuantumDeterminants.Sset k r z, ∀ g ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r),
      cMul k r z y (s * g) = cMul k r z y g ∧ cMulD k r z β (s * g) = cMulD k r z β g) ∧
    (∀ (y β : Fin (2 * r + k + 1) → ℂ) (X : Mat k r), ∀ g ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r),
      S7.RdV X (cMul k r z y) g = cMul k r z (X *ᵥ y) g ∧
        S7.RdV X (cMulD k r z β) g = -cMulD k r z (β ᵥ* X) g) ∧
    ∀ (y β : Fin (2 * r + k + 1) → ℂ), ∃ C : ℝ, ∀ g ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r),
      ‖cMul k r z y g‖ ≤ C * ∑ i, ∑ j, ‖g i j‖ ∧ ‖cMulD k r z β g‖ ≤ C * ∑ i, ∑ j, ‖g i j‖

end ReciprocityTheory.ChartRestriction.DS.Lap
