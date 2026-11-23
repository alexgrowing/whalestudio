import Mathlib
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.SecondCountableTopologyArchUnitary

namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open NumberField GroundTheory.Automorphic Module Matrix Topology MeasureTheory
open scoped Pointwise ComplexOrder ENNReal

noncomputable section

variable {F E : Type*} [Field F] [Field E] [NumberField F] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [IsTotallyReal F] [IsTotallyComplex E]
variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι] [DecidableEq ι]

def BoundedGenerators.Statement (h : HermitianForm F E W) (v : Basis ι E W) : Prop :=
  ∀ (M : Majorant h v) (D : ℕ) (t : ℝ), 0 < t →
    ∃ (n : ℕ) (C : ℝ), ∀ (La : AddSubgroup W) (g : archUnitary h v), IsDIntegral h D La →
      (∀ x ∈ La, x ≠ 0 → t ≤ M.len (invApply g (vecAt v x))) →
      ∃ e : Fin n → W, AddSubgroup.closure (Set.range e) = La ∧
        ∀ a, M.len (invApply g (vecAt v (e a))) ≤ C

end

end GroundTheory.Heights₂.Heights.FiniteCovolume
