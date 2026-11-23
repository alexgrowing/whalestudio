import Mathlib
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.SecondCountableTopologyArchUnitary

namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open NumberField GroundTheory.Automorphic Module Matrix Topology MeasureTheory

noncomputable section

variable {F E : Type*} [Field F] [Field E] [NumberField F] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [IsTotallyReal F] [IsTotallyComplex E]
variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι] [DecidableEq ι]

def MajorantTransport.Statement (h : HermitianForm F E W) (v : Basis ι E W) : Prop :=
  ∀ M : Majorant h v, ∃ (d : ℕ) (κ : ℝ), ∀ g : archUnitary h v,
    ∃ T : (InfinitePlace E → ι → ℂ) ≃L[ℝ] EuclideanSpace ℝ (Fin d),
      (∀ y, ‖T y‖ = M.len (invApply g y)) ∧
      ∀ (L : Submodule ℤ (InfinitePlace E → ι → ℂ)) [DiscreteTopology L] [IsZLattice ℝ L],
        ZLattice.covolume (ZLattice.comap ℝ L T.symm.toLinearMap) = κ * ZLattice.covolume L

end

end GroundTheory.Heights₂.Heights.FiniteCovolume
