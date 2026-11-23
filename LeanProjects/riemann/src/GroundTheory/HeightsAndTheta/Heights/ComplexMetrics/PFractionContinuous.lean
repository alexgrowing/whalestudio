import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexMetrics.Statements
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial GroundTheory.Arith.SchemeCoh
open scoped LinearAlgebra.Projectivization

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

namespace ComplexMetric

theorem FractionContinuous.proof : FractionContinuous.Statement.{u} := by
  intro A _ N ρ d a b ha hb

  have hrep : ∀ (w : Fin (N + 1) → ℂ) (hw : w ≠ 0),
      ∃ c : ℂ, c ≠ 0 ∧ (Projectivization.mk ℂ w hw).rep = c • w := by
    intro w hw
    obtain ⟨c, hc⟩ := (Projectivization.mk_eq_mk_iff ℂ _ _ (Projectivization.rep_nonzero _) hw).1
      (Projectivization.mk_rep (Projectivization.mk ℂ w hw))
    exact ⟨c, c.ne_zero, hc.symm⟩

  have hSo : IsOpen {v : CP N | evalAt ρ v.rep b ≠ 0} := by
    have e : {v : CP N | evalAt ρ v.rep b ≠ 0} =
        {v : CP N | b ∈ (projPoint ρ v).asHomogeneousIdeal}ᶜ := by
      ext v
      exact (not_congr (mem_projPointOf ρ v.rep_nonzero hb)).symm
    rw [e]
    exact (isClosed_setOf_mem_projPoint ρ hb).isOpen_compl
  have hq : Topology.IsQuotientMap
      (Projectivization.mk' ℂ : {w : Fin (N + 1) → ℂ // w ≠ 0} → CP N) := by
    refine ⟨⟨rfl⟩, fun v => ?_⟩
    exact ⟨⟨v.rep, v.rep_nonzero⟩, Projectivization.mk_rep v⟩
  rw [hq.continuousOn_isOpen_iff hSo]

  have hval : ∀ w : {w : Fin (N + 1) → ℂ // w ≠ 0},
      evalAt ρ (Projectivization.mk' ℂ w).rep a / evalAt ρ (Projectivization.mk' ℂ w).rep b =
        evalAt ρ w.1 a / evalAt ρ w.1 b := by
    intro w
    obtain ⟨c, hc, e⟩ := hrep w.1 w.2
    change evalAt ρ (Projectivization.mk ℂ w.1 w.2).rep a /
      evalAt ρ (Projectivization.mk ℂ w.1 w.2).rep b = _
    rw [e, evalAt_smul ρ ha, evalAt_smul ρ hb]
    exact mul_div_mul_left _ _ (pow_ne_zero _ hc)
  have hne : ∀ w : {w : Fin (N + 1) → ℂ // w ≠ 0},
      w ∈ (Projectivization.mk' ℂ) ⁻¹' {v : CP N | evalAt ρ v.rep b ≠ 0} →
        evalAt ρ w.1 b ≠ 0 := by
    intro w hw h0
    obtain ⟨c, _, e⟩ := hrep w.1 w.2
    apply hw
    change evalAt ρ (Projectivization.mk ℂ w.1 w.2).rep b = 0
    rw [e, evalAt_smul ρ hb, h0, mul_zero]
  have hfun : ((fun v : CP N => evalAt ρ v.rep a / evalAt ρ v.rep b) ∘
      Projectivization.mk' ℂ) = fun w => evalAt ρ w.1 a / evalAt ρ w.1 b := by
    funext w
    exact hval w
  rw [hfun]
  exact ContinuousOn.div ((continuous_evalAt ρ a).comp continuous_subtype_val).continuousOn
    ((continuous_evalAt ρ b).comp continuous_subtype_val).continuousOn hne

end ComplexMetric

end GroundTheory.Heights₂.Heights
