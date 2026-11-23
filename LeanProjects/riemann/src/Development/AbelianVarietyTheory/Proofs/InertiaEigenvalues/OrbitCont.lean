import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TwistStep
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.FiltrationZeroMembership
import Development.AbelianVarietyTheory.CrystallinePeriods.RingBasics

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.Pst

namespace GlobalTheory.LTChar

variable {l : ℕ} [Fact l.Prime]

theorem orbit_cont (y : ℂ_[l]) : Continuous fun g : GQ l => Formalism.Per.σC g y := by
  refine continuous_iff_continuousAt.2 fun g₀ => ?_
  refine Metric.tendsto_nhds.2 fun ε hε => ?_
  obtain ⟨z, hz⟩ : ∃ z : Om l, dist y (z : ℂ_[l]) < ε / 2 :=
    UniformSpace.Completion.denseRange_coe.exists_dist_lt y (half_pos hε)
  let F := adjExt (z : Om l)
  haveI := F.2
  have hH : IsOpen ((F.1.fixingSubgroup : Subgroup (GQ l)) : Set (GQ l)) :=
    IntermediateField.fixingSubgroup_isOpen F.1
  have hU : IsOpen {g : GQ l | g₀⁻¹ * g ∈ F.1.fixingSubgroup} :=
    hH.preimage (continuous_const.mul continuous_id)
  have hg₀ : g₀ ∈ {g : GQ l | g₀⁻¹ * g ∈ F.1.fixingSubgroup} := by
    simp only [Set.mem_setOf_eq, inv_mul_cancel]
    exact Subgroup.one_mem _
  filter_upwards [hU.mem_nhds hg₀] with g hg
  have hgz : g z = g₀ z := by
    have h := (IntermediateField.mem_fixingSubgroup_iff _ _).1 hg z (mem_adjExt z)
    rw [AlgEquiv.mul_apply] at h
    have h' := congrArg g₀ h
    rwa [← AlgEquiv.mul_apply, mul_inv_cancel, AlgEquiv.one_apply] at h'
  have e : Formalism.Per.σC g y - Formalism.Per.σC g₀ y =
      Formalism.Per.σC g (y - z) + Formalism.Per.σC g₀ ((z : ℂ_[l]) - y) := by
    rw [map_sub, map_sub, GlobalTheory.RingBasics.σC_coe, GlobalTheory.RingBasics.σC_coe, hgz]
    ring
  rw [dist_eq_norm, e]
  calc _ ≤ ‖Formalism.Per.σC g (y - z)‖ + ‖Formalism.Per.σC g₀ ((z : ℂ_[l]) - y)‖ := norm_add_le _ _
    _ = ‖y - z‖ + ‖y - z‖ := by rw [GlobalTheory.RingBasics.norm_σC, GlobalTheory.RingBasics.norm_σC, norm_sub_rev (z : ℂ_[l]) y]
    _ < ε := by rw [← dist_eq_norm]; linarith

end GlobalTheory.LTChar
