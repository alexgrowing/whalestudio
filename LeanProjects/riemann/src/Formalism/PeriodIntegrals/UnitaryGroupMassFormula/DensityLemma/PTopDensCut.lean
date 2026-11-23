import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.DensityLemma.PTopSlice

open MeasureTheory Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.C6

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

noncomputable section

namespace PI.UnitaryGroupMassFormula.DLm

def zN {m : ℕ} (Z : Matrix (Fin m) (Fin m) ℂ) : ℝ := Real.sqrt (∑ a, ∑ b, Complex.normSq (Z a b))

def FibreBound : Prop :=
  ∃ C : ℕ, ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] (D : B.RealPlaceData k r Wp Wq) (μ0 μ0' : Measure (Mt k r)),
    1 ≤ r → B.IsHaarOn (C2.N0set k r D.z) μ0 → B.IsHaarOn (C2.N0set k r D.z') μ0' →
    ∀ (ε A : ℝ), 0 < ε → (C : ℝ) * (((2 * r + k + 2 : ℕ) : ℝ) ^ 2 + (r : ℝ) ^ 3) ≤ A → ∃ K : ℝ, 0 ≤ K ∧
      ∀ g ∈ B.GV k r, ε ≤ Gf k r D.z D.z' g →
        ∫⁻ x : B.SS k r, ENNReal.ofReal (B.gN (B.sgs x g) ^ (-A)) ∂((D.μW.prod μ0).prod (D.μW'.prod μ0')) ≤
          ENNReal.ofReal (K * (1 + zN (Zhat k r D.z D.z' g)) ^
            (-(A - (C : ℝ) * (((2 * r + k + 2 : ℕ) : ℝ) ^ 2 + (r : ℝ) ^ 3))))

def DensFramesOf : Prop := FibreBound → TopDensEx

end PI.UnitaryGroupMassFormula.DLm
