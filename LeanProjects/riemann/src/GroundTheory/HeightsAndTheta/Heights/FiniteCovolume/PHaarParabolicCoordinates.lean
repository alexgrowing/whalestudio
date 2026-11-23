import Mathlib
import GroundTheory.AutomorphicForms.HaarSK
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.StatementsHaarParabolicCoordinates
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.StatementsLineStabHaar
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.StatementsArchUnimodular
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.StatementsMajorantStabCompact

namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open NumberField GroundTheory.Automorphic Module Matrix MeasureTheory
open scoped ENNReal NNReal

noncomputable section

variable {F E : Type*} [Field F] [Field E] [NumberField F] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [IsTotallyReal F] [IsTotallyComplex E]
variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [NumberField F] [IsTotallyReal F] [IsTotallyComplex E] in

theorem HaarParabolicCoordinates.proof (h : HermitianForm F E W) (v : Basis ι E W)
    (h₁ : ParabolicDecomposition.Statement h v) (h₂ : ArchUnimodular.Statement h v)
    (h₃ : MajorantStabCompact.Statement h v) (h₄ : LineStabHaar.Statement h v) :
    HaarParabolicCoordinates.Statement h v := by
  intro M μ _ x₀ hx₀ hiso
  have : μ.IsMulRightInvariant := h₂ μ
  have : CompactSpace M.stab := isCompact_iff_compactSpace.mp (h₃ M)
  set κ : Measure M.stab := Measure.haarMeasure ⊤ with hκ
  have : IsProbabilityMeasure κ :=
    ⟨by simpa using Measure.haarMeasure_self (K₀ := (⊤ : TopologicalSpace.PositiveCompacts M.stab))⟩
  have hSK : Function.Surjective (HaarSK.mulMap (lineStab h v x₀) M.stab) := by
    intro g
    obtain ⟨p, k, hk, rfl, hp⟩ := h₁ M x₀ hx₀ hiso g
    exact ⟨(⟨p, hp⟩, ⟨k, hk⟩), rfl⟩
  obtain ⟨c, -, hc⟩ := HaarSK.exists_lintegral_eq μ (isClosed_lineStab h v x₀) (h₃ M) hSK
    (Measure.haar : Measure (lineStab h v x₀)) κ
  obtain ⟨ν, τ, hν, hτ, -, hτx, hP⟩ := h₄ x₀ hx₀ hiso Measure.haar
  have hc0 : (c : ℝ≥0∞) ≠ 0 := by
    intro h0
    have h1 := hc 1 measurable_const
    rw [h0, zero_mul] at h1
    simp only [Pi.one_apply, lintegral_const, one_mul] at h1
    exact (Measure.IsOpenPosMeasure.open_pos Set.univ isOpen_univ Set.univ_nonempty) h1
  have := hν
  refine ⟨(c : ℝ≥0∞) • ν, κ, τ, Measure.IsHaarMeasure.smul ν hc0 ENNReal.coe_ne_top, inferInstance,
    inferInstance, hτ, hτx, fun f hf => ?_⟩
  have hφ : Measurable fun g : archUnitary h v => ∫⁻ k : M.stab, f (g * k) ∂κ :=
    (hf.comp (measurable_fst.mul (measurable_subtype_coe.comp measurable_snd))).lintegral_prod_right'
  have hPφ := hP _ hφ
  rw [hc f hf, hPφ, ← lintegral_const_mul' _ _ ENNReal.coe_ne_top]
  refine lintegral_congr fun b => ?_
  have hswap : ∫⁻ x : vecFixGroup h v x₀, ∫⁻ k : M.stab, f ((x : archUnitary h v) * τ b * k) ∂κ ∂ν =
      ∫⁻ k : M.stab, ∫⁻ x : vecFixGroup h v x₀, f ((x : archUnitary h v) * (τ b * k)) ∂ν ∂κ := by
    rw [lintegral_lintegral_swap]
    · simp only [mul_assoc]
    · exact (hf.comp (((measurable_subtype_coe.comp measurable_fst).mul_const (τ b)).mul
        (measurable_subtype_coe.comp measurable_snd))).aemeasurable
  simp only [lintegral_smul_measure, smul_eq_mul]
  rw [lintegral_const_mul' _ _ ENNReal.coe_ne_top, hswap]
  ring

end

end GroundTheory.Heights₂.Heights.FiniteCovolume
