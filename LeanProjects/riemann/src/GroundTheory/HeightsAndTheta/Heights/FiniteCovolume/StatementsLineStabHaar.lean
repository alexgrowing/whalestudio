import Mathlib
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.StatementsVecFixGroup

namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open NumberField GroundTheory.Automorphic Module Matrix MeasureTheory
open scoped ENNReal

noncomputable section

section LineStab

variable {F E : Type*} [Field F] [Field E] [Algebra F E] [Algebra.IsQuadraticExtension F E]
variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι] [DecidableEq ι]
variable [NumberField E]

def lineStab (h : HermitianForm F E W) (v : Basis ι E W) (x₀ : W) :
    Subgroup (archUnitary h v) where
  carrier := {g | ∀ w, ∃ c : ℂ, ((g : InfinitePlace E → GL ι ℂ) w : Matrix ι ι ℂ) *ᵥ vecAt v x₀ w =
    c • vecAt v x₀ w}
  one_mem' w := ⟨1, by simp⟩
  mul_mem' {a b} ha hb w := by
    obtain ⟨c, hc⟩ := ha w
    obtain ⟨d, hd⟩ := hb w
    refine ⟨c * d, ?_⟩
    simp only [Subgroup.coe_mul, Pi.mul_apply, Units.val_mul, ← Matrix.mulVec_mulVec, hd,
      Matrix.mulVec_smul, hc, smul_smul, mul_comm d c]
  inv_mem' {a} ha w := by
    obtain ⟨c, hc⟩ := ha w
    have e : (((a⁻¹ : archUnitary h v) : InfinitePlace E → GL ι ℂ) w : Matrix ι ι ℂ) *
        ((a : InfinitePlace E → GL ι ℂ) w : Matrix ι ι ℂ) = 1 := by
      rw [Subgroup.coe_inv, Pi.inv_apply, ← Units.val_mul, inv_mul_cancel, Units.val_one]
    have hz : vecAt v x₀ w = (((a⁻¹ : archUnitary h v) : InfinitePlace E → GL ι ℂ) w :
        Matrix ι ι ℂ) *ᵥ (((a : InfinitePlace E → GL ι ℂ) w : Matrix ι ι ℂ) *ᵥ vecAt v x₀ w) := by
      rw [Matrix.mulVec_mulVec, e, Matrix.one_mulVec]
    by_cases hc0 : c = 0
    · have h0 : vecAt v x₀ w = 0 := by
        rw [hz, hc, hc0, zero_smul, Matrix.mulVec_zero]
      exact ⟨0, by rw [h0, Matrix.mulVec_zero, smul_zero]⟩
    · refine ⟨c⁻¹, ?_⟩
      calc (((a⁻¹ : archUnitary h v) : InfinitePlace E → GL ι ℂ) w : Matrix ι ι ℂ) *ᵥ vecAt v x₀ w
          = c⁻¹ • ((((a⁻¹ : archUnitary h v) : InfinitePlace E → GL ι ℂ) w : Matrix ι ι ℂ) *ᵥ
              (c • vecAt v x₀ w)) := by
            rw [Matrix.mulVec_smul, smul_smul, inv_mul_cancel₀ hc0, one_smul]
        _ = c⁻¹ • vecAt v x₀ w := by rw [← hc, ← hz]

omit [NumberField E] in
theorem mem_lineStab {h : HermitianForm F E W} {v : Basis ι E W} {x₀ : W} {g : archUnitary h v} :
    g ∈ lineStab h v x₀ ↔ ∀ w, ∃ c : ℂ,
      ((g : InfinitePlace E → GL ι ℂ) w : Matrix ι ι ℂ) *ᵥ vecAt v x₀ w = c • vecAt v x₀ w :=
  Iff.rfl

omit [NumberField E] in

theorem vecFixGroup_le_lineStab (h : HermitianForm F E W) (v : Basis ι E W) (x₀ : W) :
    vecFixGroup h v x₀ ≤ lineStab h v x₀ := fun g hg w => ⟨1, by rw [one_smul]; exact hg w⟩

omit [NumberField E] in

theorem isClosed_lineStab (h : HermitianForm F E W) (v : Basis ι E W) (x₀ : W) :
    IsClosed (lineStab h v x₀ : Set (archUnitary h v)) := by
  have : (lineStab h v x₀ : Set (archUnitary h v)) = ⋂ w, (fun g : archUnitary h v =>
      ((g : InfinitePlace E → GL ι ℂ) w : Matrix ι ι ℂ) *ᵥ vecAt v x₀ w) ⁻¹'
        (Submodule.span ℂ {vecAt v x₀ w} : Set (ι → ℂ)) := by
    ext g
    simp only [Set.mem_iInter, Set.mem_preimage, SetLike.mem_coe, Submodule.mem_span_singleton,
      mem_lineStab]
    exact forall_congr' fun w => ⟨fun ⟨c, hc⟩ => ⟨c, hc.symm⟩, fun ⟨c, hc⟩ => ⟨c, hc.symm⟩⟩
  rw [this]
  refine isClosed_iInter fun w => IsClosed.preimage ?_ (Submodule.closed_of_finiteDimensional _)
  exact (Units.continuous_val.comp ((continuous_apply w).comp continuous_subtype_val)).matrix_mulVec
    continuous_const

instance locallyCompactSpace_lineStab (h : HermitianForm F E W) (v : Basis ι E W) (x₀ : W) :
    LocallyCompactSpace (lineStab h v x₀) :=
  (isClosed_lineStab h v x₀).isClosedEmbedding_subtypeVal.locallyCompactSpace

instance secondCountableTopology_lineStab (h : HermitianForm F E W) (v : Basis ι E W) (x₀ : W) :
    SecondCountableTopology (lineStab h v x₀) :=
  TopologicalSpace.Subtype.secondCountableTopology _

end LineStab

variable {F E : Type*} [Field F] [Field E] [NumberField F] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [IsTotallyReal F] [IsTotallyComplex E]
variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι] [DecidableEq ι]

def LineStabHaar.Statement (h : HermitianForm F E W) (v : Basis ι E W) : Prop :=
  ∀ x₀ : W, x₀ ≠ 0 → h.toSesq x₀ x₀ = 0 →
    ∀ (μP : Measure (lineStab h v x₀)) [μP.IsHaarMeasure],
    ∃ (ν : Measure (vecFixGroup h v x₀)) (τ : (InfinitePlace E → ℂ) → archUnitary h v),
      ν.IsHaarMeasure ∧ Measurable τ ∧ (∀ b, τ b ∈ lineStab h v x₀) ∧
      (∀ b : InfinitePlace E → ℂ, (∀ w, b w ≠ 0) →
        invApply (τ b) (vecAt v x₀) = fun w => b w • vecAt v x₀ w) ∧
      ∀ φ : archUnitary h v → ℝ≥0∞, Measurable φ →
        ∫⁻ p, φ (p : archUnitary h v) ∂μP = ∫⁻ b : InfinitePlace E → ℂ,
          (∏ w, ‖b w‖ₑ ^ (2 * (finrank E W - 2))) *
            ∫⁻ x : vecFixGroup h v x₀, φ ((x : archUnitary h v) * τ b) ∂ν

section Inhabitants

open GaussianPlane

end Inhabitants

end

end GroundTheory.Heights₂.Heights.FiniteCovolume
