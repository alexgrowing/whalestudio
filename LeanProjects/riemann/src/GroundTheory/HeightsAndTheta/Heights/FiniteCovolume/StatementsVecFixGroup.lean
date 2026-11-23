import Mathlib
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.SecondCountableTopologyArchUnitary

namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open NumberField GroundTheory.Automorphic Module Matrix Topology MeasureTheory
open scoped ENNReal

noncomputable section

variable {F E : Type*} [Field F] [Field E] [Algebra F E] [Algebra.IsQuadraticExtension F E]
variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι] [DecidableEq ι]
variable [NumberField E]

def vecFixGroup (h : HermitianForm F E W) (v : Basis ι E W) (x₀ : W) :
    Subgroup (archUnitary h v) where
  carrier := {g | ∀ w, ((g : InfinitePlace E → GL ι ℂ) w : Matrix ι ι ℂ) *ᵥ vecAt v x₀ w =
    vecAt v x₀ w}
  one_mem' w := by simp
  mul_mem' {a b} ha hb w := by
    simp only [Subgroup.coe_mul, Pi.mul_apply, Units.val_mul, ← Matrix.mulVec_mulVec, hb w, ha w]
  inv_mem' {a} ha w := by
    have e : (((a⁻¹ : archUnitary h v) : InfinitePlace E → GL ι ℂ) w : Matrix ι ι ℂ) *
        ((a : InfinitePlace E → GL ι ℂ) w : Matrix ι ι ℂ) = 1 := by
      rw [Subgroup.coe_inv, Pi.inv_apply, ← Units.val_mul, inv_mul_cancel, Units.val_one]
    calc (((a⁻¹ : archUnitary h v) : InfinitePlace E → GL ι ℂ) w : Matrix ι ι ℂ) *ᵥ vecAt v x₀ w
        = (((a⁻¹ : archUnitary h v) : InfinitePlace E → GL ι ℂ) w : Matrix ι ι ℂ) *ᵥ
            (((a : InfinitePlace E → GL ι ℂ) w : Matrix ι ι ℂ) *ᵥ vecAt v x₀ w) := by rw [ha w]
      _ = vecAt v x₀ w := by rw [Matrix.mulVec_mulVec, e, Matrix.one_mulVec]

omit [NumberField E] in
theorem mem_vecFixGroup {h : HermitianForm F E W} {v : Basis ι E W} {x₀ : W}
    {g : archUnitary h v} : g ∈ vecFixGroup h v x₀ ↔
      ∀ w, ((g : InfinitePlace E → GL ι ℂ) w : Matrix ι ι ℂ) *ᵥ vecAt v x₀ w = vecAt v x₀ w :=
  Iff.rfl

omit [NumberField E] in

theorem isClosed_vecFixGroup (h : HermitianForm F E W) (v : Basis ι E W) (x₀ : W) :
    IsClosed (vecFixGroup h v x₀ : Set (archUnitary h v)) := by
  have : (vecFixGroup h v x₀ : Set (archUnitary h v)) = ⋂ w, {g : archUnitary h v |
      ((g : InfinitePlace E → GL ι ℂ) w : Matrix ι ι ℂ) *ᵥ vecAt v x₀ w = vecAt v x₀ w} := by
    ext g
    simp [mem_vecFixGroup]
  rw [this]
  refine isClosed_iInter fun w => isClosed_eq ?_ continuous_const
  exact (Units.continuous_val.comp ((continuous_apply w).comp continuous_subtype_val)).matrix_mulVec
    continuous_const

instance locallyCompactSpace_vecFixGroup (h : HermitianForm F E W) (v : Basis ι E W) (x₀ : W) :
    LocallyCompactSpace (vecFixGroup h v x₀) :=
  (isClosed_vecFixGroup h v x₀).isClosedEmbedding_subtypeVal.locallyCompactSpace

instance secondCountableTopology_vecFixGroup (h : HermitianForm F E W) (v : Basis ι E W) (x₀ : W) :
    SecondCountableTopology (vecFixGroup h v x₀) :=
  TopologicalSpace.Subtype.secondCountableTopology _

instance sigmaFinite_vecFixGroup (h : HermitianForm F E W) (v : Basis ι E W) (x₀ : W)
    (ν : Measure (vecFixGroup h v x₀)) [ν.IsHaarMeasure] : SigmaFinite ν :=
  inferInstance

instance measurableMul_vecFixGroup (h : HermitianForm F E W) (v : Basis ι E W) (x₀ : W) :
    MeasurableMul (vecFixGroup h v x₀) :=
  inferInstance

end

end GroundTheory.Heights₂.Heights.FiniteCovolume
