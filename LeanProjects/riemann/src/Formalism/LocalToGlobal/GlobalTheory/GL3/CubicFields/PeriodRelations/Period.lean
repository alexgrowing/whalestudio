import Formalism.LocalToGlobal.GlobalTheory.GL3.CubicFields.PeriodRelations.LeadingConstantNeZero
import Formalism.LocalToGlobal.GlobalTheory.GL3.CubicFields.PeriodRelations.NormSum

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5

open NumberField Classical
open scoped Pointwise
open Formalism.BasicNotions (D7)
open Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity (IsLat jL Uniformization CMTransitive LinkPer KroneckerLimit DedekindFactor)
open Formalism.MainNotions.TaylorLogMetric (lamConj lamOf embT meanLogOm DataIn tor0 IsCurveIdeal IsDiscriminantTwelfthRootOfIdealLattice per22 logOmVal)

theorem br_ellT_eq (D : D7) (M : IntermediateField ℚ ℂ) [NumberField M] (τ : D.what₂.Tau) :
    Formalism.MainNotions.TaylorLogMetric.ellT D M τ = lineR M (embT D) D.host.AA0 τ := rfl

theorem br_brN_eq (D : D7) : brN D = ((FractionalIdeal.absNorm (D.host.AA0 *
    ((differentIdeal (𝓞 D.host.K) (𝓞 D.host.E) : Ideal (𝓞 D.host.E)) :
      FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E)) : ℚ) : ℝ) := rfl

theorem br_exists_ellT (D : D7) (M : IntermediateField ℚ ℂ) [NumberField M]
    (hemb : ∀ τ x, embT D τ x ∈ M) (τ : D.what₂.Tau) :
    ∃ s : M, s ≠ 0 ∧ s ∈ Formalism.MainNotions.TaylorLogMetric.ellT D M τ := by
  rw [br_ellT_eq, lineR_eq D.host.K D.host.E (brPhi D) M D.what₂.Tau (embT D) (br_embT_injective D)
    (br_embT_res D) (br_card_tau D) hemb]
  have hJ : D.host.AA0 * ((differentIdeal (𝓞 D.host.K) (𝓞 D.host.E) : Ideal (𝓞 D.host.E)) :
      FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) ≠ 0 :=
    mul_ne_zero (leading_constant_ne_zero D) (coeIdeal_different_ne_zero _ _)
  obtain ⟨a, ha, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot
    (FractionalIdeal.coeToSubmodule_ne_bot.mpr hJ)
  refine ⟨liftM M (embT D τ a), ?_, Submodule.subset_span ⟨a, ha, rfl⟩⟩
  have hm := hemb τ a
  unfold liftM
  rw [dif_pos hm]
  intro h
  have : embT D τ a = 0 := congrArg Subtype.val h
  exact ha0 ((map_eq_zero (embT D τ)).mp this)

theorem br_meanLogOm_eq (D : D7) (Λ : AddSubgroup ℂ) (M : IntermediateField ℚ ℂ) [NumberField M]
    (hemb : ∀ τ x, embT D τ x ∈ M) (τ : D.what₂.Tau)
    (hpos : ∀ ρ : M →ₐ[ℚ] ℂ, 0 < area (lamConj M ρ Λ)) :
    meanLogOm D Λ M τ =
      -(2 / (Module.finrank ℚ D.host.E : ℝ)) * Real.log (brN D) +
        (∑ ρ : M →ₐ[ℚ] ℂ, Real.log (area (lamConj M ρ Λ) / Real.pi)) /
          (Module.finrank ℚ M : ℝ) := by
  have hex := br_exists_ellT D M hemb τ
  unfold meanLogOm
  dsimp only
  set s : M := Classical.epsilon (fun s : M => s ≠ 0 ∧ s ∈ Formalism.MainNotions.TaylorLogMetric.ellT D M τ) with hsdef
  have hs : s ≠ 0 ∧ s ∈ Formalism.MainNotions.TaylorLogMetric.ellT D M τ := Classical.epsilon_spec hex
  rw [br_ellT_eq] at hs ⊢
  have hidx := index_lineR D.host.K D.host.E (brPhi D) M D.what₂.Tau (embT D) (br_embT_injective D)
    (br_embT_res D) (br_card_tau D) hemb D.host.AA0 (leading_constant_ne_zero D) τ s hs.1 hs.2
  rw [← br_brN_eq] at hidx
  set x : ℝ := ((((Submodule.span (𝓞 M) {s}).toAddSubgroup.addSubgroupOf
        (lineR M (embT D) D.host.AA0 τ).toAddSubgroup).index : ℕ) : ℝ) with hxdef
  set e : ℕ := Module.finrank ℚ D.host.E with he
  set m : ℕ := Module.finrank ℚ M with hm
  set ns : ℝ := |((Algebra.norm ℚ s : ℚ) : ℝ)| with hns
  have hns0 : ns ≠ 0 := by
    rw [hns, abs_ne_zero, Rat.cast_ne_zero]
    exact (Algebra.norm_ne_zero_iff).mpr hs.1
  have hrhs : ns ^ e ≠ 0 := pow_ne_zero _ hns0
  have hl : x ^ e * brN D ^ m ≠ 0 := hidx ▸ hrhs
  have hx0 : x ^ e ≠ 0 := left_ne_zero_of_mul hl
  have hN0 : brN D ^ m ≠ 0 := right_ne_zero_of_mul hl
  have hlog : (e : ℝ) * Real.log x + (m : ℝ) * Real.log (brN D) = (e : ℝ) * Real.log ns := by
    have := congrArg Real.log hidx
    rw [Real.log_mul hx0 hN0, Real.log_pow, Real.log_pow, Real.log_pow] at this
    exact this
  have he0 : (e : ℝ) ≠ 0 := by
    rw [he]; exact_mod_cast (Module.finrank_pos : 0 < Module.finrank ℚ D.host.E).ne'
  have hm0 : (m : ℝ) ≠ 0 := by
    rw [hm]; exact_mod_cast (Module.finrank_pos : 0 < Module.finrank ℚ M).ne'
  have hterm : ∀ ρ : M →ₐ[ℚ] ℂ, Formalism.MainNotions.TaylorLogMetric.logMet M Λ ρ s =
      Real.log Real.pi + Real.log (‖ρ s‖ ^ 2) - Real.log (area (lamConj M ρ Λ)) := by
    intro ρ
    unfold Formalism.MainNotions.TaylorLogMetric.logMet
    rw [br_area_eq]
    have hρ : ‖ρ s‖ ^ 2 ≠ 0 := pow_ne_zero _ (norm_ne_zero_iff.mpr ((map_ne_zero ρ).mpr hs.1))
    rw [Real.log_div (mul_ne_zero Real.pi_ne_zero hρ) (hpos ρ).ne', Real.log_mul Real.pi_ne_zero hρ]
  have hsum : ∑ ρ : M →ₐ[ℚ] ℂ, Formalism.MainNotions.TaylorLogMetric.logMet M Λ ρ s =
      (m : ℝ) * Real.log Real.pi + 2 * Real.log ns -
        ∑ ρ : M →ₐ[ℚ] ℂ, Real.log (area (lamConj M ρ Λ)) := by
    rw [Finset.sum_congr rfl (fun ρ _ => hterm ρ), Finset.sum_sub_distrib, Finset.sum_add_distrib,
      br_sum_log_norm_sq M s hs.1, Finset.sum_const, Finset.card_univ, AlgHom.card, nsmul_eq_mul]
  have hsum2 : ∑ ρ : M →ₐ[ℚ] ℂ, Real.log (area (lamConj M ρ Λ) / Real.pi) =
      ∑ ρ : M →ₐ[ℚ] ℂ, Real.log (area (lamConj M ρ Λ)) - (m : ℝ) * Real.log Real.pi := by
    rw [Finset.sum_congr rfl (fun ρ _ => Real.log_div (hpos ρ).ne' Real.pi_ne_zero),
      Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, AlgHom.card, nsmul_eq_mul]
  rw [hsum, hsum2]
  field_simp
  linear_combination 2 * hlog

end Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5

end
