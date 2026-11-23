import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.DensityLemma.PFibreBoundVDefs

open MeasureTheory Matrix Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.C6
open scoped ENNReal NNReal

noncomputable section

namespace PI.UnitaryGroupMassFormula.DLm

def skewOf {r : ℕ} (T : Fin r → Fin r → ℝ) : Matrix (Fin r) (Fin r) ℂ :=
  Matrix.of fun a b => ((T a b - T b a : ℝ) : ℂ) + Complex.I * ((T a b + T b a : ℝ) : ℂ)

def Pz (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ :=
  1 - ((∑ j, Complex.normSq (zW k r z j) : ℝ) : ℂ)⁻¹ • Matrix.vecMulVec (zW k r z) (star (zW k r z))

def psiZ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (p : (Fin r → Fin (k + 1) → ℂ) × (Fin r → Fin r → ℝ)) : Mt k r :=
  unipotentBlockMatrix k r (Matrix.of p.1 * Pz k r z) (skewOf p.2)

def rhoZ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (B0 : Fin r → Fin (k + 1) → ℂ) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp (-(∑ a, Complex.normSq ((Matrix.of B0 *ᵥ zW k r z) a))))

def nuZ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) : Measure (Mt k r) :=
  (((volume : Measure (Fin r → Fin (k + 1) → ℂ)).withDensity (rhoZ k r z)).prod
    (volume : Measure (Fin r → Fin r → ℝ))).map (psiZ k r z)

def UnipotentHaarMultipleExplicit : Prop :=
  ∀ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (μ0 : Measure (Mt k r)), 1 ≤ k → 1 ≤ r → C2.StdZ k r z →
    B.IsHaarOn (C2.N0set k r z) μ0 → ∃ c : ℝ≥0, 0 < c ∧ nuZ k r z = c • μ0

def ExplicitUnipotentVolumeBound : Prop :=
  ∃ C : ℕ, ∀ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ), 1 ≤ k → 1 ≤ r → C2.StdZ k r z →
    ∀ ε : ℝ, 0 < ε → ∃ K : ℝ, 0 ≤ K ∧
      ∀ v : Fin (r + 1) → Fin (2 * r + k + 1) → ℂ, ε ≤ Complex.normSq (Mf k r z v).det → ∀ R : ℝ, 0 ≤ R →
        nuZ k r z {x | (Matrix.of x : B.Mat k r) ∈ C2.N0set k r z ∧
            tN (fun b => (Matrix.of x : B.Mat k r)⁻¹ *ᵥ v b) ≤ R} ≤
          ENNReal.ofReal (K * (1 + zN (Mf k r z v)) ^ ((C : ℝ) * XF k r) * (1 + R) ^ ((C : ℝ) * XF k r))

end PI.UnitaryGroupMassFormula.DLm
