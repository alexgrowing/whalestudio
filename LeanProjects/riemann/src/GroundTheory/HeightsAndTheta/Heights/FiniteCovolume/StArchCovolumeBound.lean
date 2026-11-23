import Mathlib
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.SecondCountableTopologyArchUnitary

namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open NumberField GroundTheory.Automorphic Module Matrix Topology MeasureTheory

noncomputable section

variable {F E : Type*} [Field F] [Field E] [NumberField F] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [IsTotallyReal F] [IsTotallyComplex E]
variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι] [DecidableEq ι]

def vecAtHom (v : Basis ι E W) : W →+ (InfinitePlace E → ι → ℂ) where
  toFun := vecAt v
  map_zero' := by funext w i; simp [vecAt]
  map_add' x y := by funext w i; simp [vecAt]

omit [IsTotallyComplex E] [Fintype ι] [DecidableEq ι] in
theorem vecAtHom_apply (v : Basis ι E W) (x : W) : vecAtHom v x = vecAt v x := rfl

def archLattice (v : Basis ι E W) (La : AddSubgroup W) : Submodule ℤ (InfinitePlace E → ι → ℂ) :=
  AddSubgroup.toIntSubmodule (La.map (vecAtHom v))

omit [IsTotallyComplex E] [Fintype ι] [DecidableEq ι] in
theorem mem_archLattice {v : Basis ι E W} {La : AddSubgroup W} {y : InfinitePlace E → ι → ℂ} :
    y ∈ archLattice v La ↔ ∃ x ∈ La, vecAt v x = y := by
  change y ∈ La.map (vecAtHom v) ↔ _
  rw [AddSubgroup.mem_map]
  rfl

def ArchCovolumeBound.Statement (h : HermitianForm F E W) (v : Basis ι E W) : Prop :=
  ∀ D : ℕ, ∃ c : ℝ, ∀ La : AddSubgroup W, IsDIntegral h D La →
    ∃ _ : DiscreteTopology (archLattice v La), IsZLattice ℝ (archLattice v La) ∧
      ZLattice.covolume (archLattice v La) ≤ c

end

end GroundTheory.Heights₂.Heights.FiniteCovolume
