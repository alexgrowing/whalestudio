import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CosetRefinement
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.TopPlaceLogTheta
import Formalism.LocalToGlobal.GlobalTheory.GL3.CubicFields.PeriodRelations.Period
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MeanLogPeriodConjugatesEqChowlaSelberg
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.InducedTypeThetaGenusOnePermutes
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ExistsPowPrincipalFractionalIdeal

noncomputable section

namespace GlobalTheory.MeanPeriodClosed

open NumberField Formalism.BasicNotions
open Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5 (brN br_meanLogOm_eq br_b_spec absNorm_inv_mul_different natAbs_discr_eq
  discr_K discriminant_mod_four br_sqrt_sq br_finrank_K br_finrank_E)

theorem two_log_brN (D : D7) :
    (2 / (Module.finrank ℚ D.host.E : ℝ)) * Real.log (brN D) =
      Real.log D.host.rdE - Real.log (Real.sqrt (D.host.d : ℝ)) := by
  haveI : Fact D.host.d.Prime := ⟨D.host.hyp.2.1⟩
  have hd0 : (0 : ℝ) < D.host.d := by exact_mod_cast D.host.hyp.2.1.pos
  have hdK : NumberField.discr D.host.K = -(D.host.d : ℤ) :=
    discr_K D.host.K D.host.d (discriminant_mod_four D) _ (br_sqrt_sq D) (br_finrank_K D)
  have h1 := absNorm_inv_mul_different D.host.K D.host.E D.host.conj D.host.𝔟 (br_b_spec D)
  have h2 := natAbs_discr_eq D.host.K D.host.E D.host.d hdK
  set A : ℝ := (Ideal.absNorm (differentIdeal (𝓞 D.host.K) (𝓞 D.host.E)) : ℝ) with hA
  have hsq : brN D ^ 2 = A := by
    have := congrArg (fun q : ℚ => (q : ℝ)) h1
    simp only [Rat.cast_pow, Rat.cast_natCast] at this
    rw [hA, ← this]
    rfl
  set m : ℕ := Module.finrank D.host.K D.host.E with hm
  have hE : Module.finrank ℚ D.host.E = 2 * m := br_finrank_E D
  have hm0 : (m : ℝ) ≠ 0 := by
    have : 0 < m := Module.finrank_pos
    exact_mod_cast this.ne'
  have hdisc : |(NumberField.discr D.host.E : ℝ)| = A * (D.host.d : ℝ) ^ m := by
    have := congrArg (fun n : ℕ => (n : ℝ)) h2
    simp only [Nat.cast_mul, Nat.cast_pow, Nat.cast_natAbs, Int.cast_abs] at this
    rw [hA, ← this]
  have hdisc0 : |(NumberField.discr D.host.E : ℝ)| ≠ 0 := by
    simpa using NumberField.discr_ne_zero D.host.E
  have hA0 : A ≠ 0 := fun h => hdisc0 (by rw [hdisc, h, zero_mul])
  have hlogA : 2 * Real.log (brN D) = Real.log A := by
    rw [← hsq, Real.log_pow]; push_cast; ring
  have hrd : Real.log D.host.rdE =
      (Real.log A + (m : ℝ) * Real.log D.host.d) / (2 * (m : ℝ)) := by
    unfold Formalism.BasicNotions.Host.rdE
    rw [Real.log_rpow (abs_pos.2 (by simpa using NumberField.discr_ne_zero D.host.E)), hdisc,
      Real.log_mul hA0 (pow_ne_zero _ hd0.ne'), Real.log_pow, hE]
    push_cast
    field_simp
  rw [hrd, Real.log_sqrt hd0.le, hE]
  push_cast
  field_simp
  linear_combination hlogA

theorem meanPeriodAt (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (hcc : Formalism.MainNotions.TaylorLogMetric.IsCurveIdeal D cc)
    (hδ : Formalism.MainNotions.TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ) : GlobalTheory.IndefiniteRowSideFullHecke.MeanPeriodLogarithms.MeanPeriodAt D cc δ := by
  intro M _ hM τ
  have hc : Formalism.MainNotions.StandardLatticesGL3.Crv D cc δ := ⟨hcc, hδ⟩
  have hpos : ∀ ρ : M →ₐ[ℚ] ℂ,
      0 < Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5.area (Formalism.MainNotions.TaylorLogMetric.lamConj M ρ (Formalism.MainNotions.TaylorLogMetric.lamOf D cc δ)) :=
    fun ρ => GlobalTheory.Glob.area_lamConj_pos hc hM ρ
  have hmean := GlobalTheory.PeriodMean.mean_log_period D (GlobalTheory.InducedType.induced_type D).1 cc δ hc M
    hM.2.1 hM.2.2
  have e := br_meanLogOm_eq D (Formalism.MainNotions.TaylorLogMetric.lamOf D cc δ) M hM.1 τ hpos
  have hN := two_log_brN D
  show Formalism.MainNotions.TaylorLogMetric.meanLogOm D (Formalism.MainNotions.TaylorLogMetric.lamOf D cc δ) M τ = Formalism.MainNotions.TaylorLogMetric.logOmVal D
  rw [e, GlobalTheory.IndefiniteRowSideFullHecke.MeanPeriodLogarithms.logOmVal_eq]
  have hmean' : (∑ ρ : M →ₐ[ℚ] ℂ, Real.log (Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5.area
      (Formalism.MainNotions.TaylorLogMetric.lamConj M ρ (Formalism.MainNotions.TaylorLogMetric.lamOf D cc δ)) / Real.pi)) / (Module.finrank ℚ M : ℝ) =
      Real.eulerMascheroniConstant + Real.log (2 * Real.pi / Real.sqrt D.host.d) -
        Formalism.MainNotions.TaylorLogMetric.logDerivativeAtOne D := hmean
  rw [hmean']
  have hd0 : (0 : ℝ) < Real.sqrt D.host.d := Real.sqrt_pos.2 (by exact_mod_cast D.host.hyp.2.1.pos)
  have hr0 : 0 < D.host.rdE := by
    unfold Formalism.BasicNotions.Host.rdE
    exact Real.rpow_pos_of_pos (abs_pos.2 (by simpa using NumberField.discr_ne_zero D.host.E)) _
  rw [Real.log_div (by positivity) hd0.ne', Real.log_div (by positivity) hr0.ne']
  rw [neg_mul, hN]
  ring

theorem meanPeriod : GlobalTheory.IndefiniteRowSideFullHecke.MeanPeriodLogarithms.MeanPeriod :=
  fun D cc δ hcc hδ => meanPeriodAt D cc δ hcc hδ

end GlobalTheory.MeanPeriodClosed
