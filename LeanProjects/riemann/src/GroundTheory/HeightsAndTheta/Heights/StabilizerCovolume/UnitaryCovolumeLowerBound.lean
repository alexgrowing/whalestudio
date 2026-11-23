import Mathlib
import GroundTheory.HeightsAndTheta.Heights.StabilizerCovolume.ImportsBis
import GroundTheory.HeightsAndTheta.Heights.StabilizerCovolume.ImportsFurther
import GroundTheory.HeightsAndTheta.Heights.StabilizerCovolume.ImportsMore
import GroundTheory.HeightsAndTheta.Heights.StabilizerCovolume.ImportsTer
import GroundTheory.HeightsAndTheta.Heights.StabilizerCovolume.ULogBound
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.NineStatements

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo NumberField GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped Matrix

def UnitaryCovolumeLowerBound.Statement : Prop :=
  ∀ {II : IntersectionSystem} {Ψ : Type} [Fintype Ψ] {K : Type} [Fintype K] {ι : K → Type}
    [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω] [Algebra ℚ Ω] {E : Ψ → Type} [∀ τ, AddCommGroup (E τ)]
    [∀ τ, Module Ω (E τ)] {Em : Type} [Field Em] [NumberField Em] [IsCMField Em] (D : FullerData II Ψ K ι Ω E Em),
    ULamOne.Statement D

theorem UnitaryCovolumeLowerBound.neg_log_le {f ρ j' : ℕ} {lam rd nz c : ℝ} (hlam : 0 < lam) (hrd : 1 ≤ rd) (hρ : 1 ≤ ρ)
    (hρj : ρ ≤ j') (hc : c = nz * rd ^ (f * ρ)) (hmin : (lam / Real.sqrt (2 * f * ρ)) ^ (2 * f * ρ) ≤ c) :
    -Real.log nz ≤ (f * j' : ℝ) * (2 * Real.posLog (1 / lam) + Real.log (2 * f * j' * rd)) := by
  rcases Nat.eq_zero_or_pos f with rfl | hf
  · simp only [mul_zero, zero_mul, pow_zero, mul_one, Nat.cast_zero] at hmin hc ⊢
    subst hc
    linarith [Real.log_nonneg hmin]
  have hF : (0 : ℝ) < f := by exact_mod_cast hf
  have hR : (0 : ℝ) < ρ := by exact_mod_cast hρ
  have hJ : (ρ : ℝ) ≤ j' := by exact_mod_cast hρj
  have hrd0 : 0 < rd := by linarith
  have hm : (0 : ℝ) < 2 * f * ρ := by positivity
  have hA : 0 < (lam / Real.sqrt (2 * f * ρ)) ^ (2 * f * ρ) := by positivity
  have hpow : 0 < rd ^ (f * ρ) := by positivity
  have hnz : 0 < nz := by
    by_contra hn
    push Not at hn
    have := mul_le_mul_of_nonneg_right hn hpow.le
    rw [zero_mul, ← hc] at this
    linarith
  have hlog := Real.log_le_log hA (hmin.trans_eq hc)
  rw [Real.log_pow, Real.log_div hlam.ne' (Real.sqrt_pos.2 hm).ne', Real.log_sqrt hm.le,
    Real.log_mul hnz.ne' hpow.ne', Real.log_pow] at hlog
  push_cast at hlog
  have h1 : -Real.log lam ≤ Real.posLog (1 / lam) := by
    have : Real.posLog (1 / lam) = max 0 (Real.log (1 / lam)) := rfl
    rw [this, one_div, Real.log_inv]
    exact le_max_right _ _
  have h2 : Real.log (2 * f * ρ) + Real.log rd ≤ Real.log (2 * f * j' * rd) := by
    rw [← Real.log_mul hm.ne' hrd0.ne']
    refine Real.log_le_log (by positivity) ?_
    gcongr
  have h3 : 0 ≤ 2 * Real.posLog (1 / lam) + Real.log (2 * f * j' * rd) := by
    have hJ1 : (1 : ℝ) ≤ j' := by linarith [(by exact_mod_cast hρ : (1 : ℝ) ≤ ρ)]
    have hF1 : (1 : ℝ) ≤ f := by exact_mod_cast hf
    have h4 : (1 : ℝ) ≤ 2 * f * j' := by
      have := one_le_mul_of_one_le_of_one_le hF1 hJ1
      linarith
    have : (1 : ℝ) ≤ 2 * f * j' * rd := one_le_mul_of_one_le_of_one_le h4 hrd
    linarith [Real.posLog_nonneg (x := 1 / lam), Real.log_nonneg this]
  have e1 : -Real.log nz ≤ f * ρ * (2 * -Real.log lam + (Real.log (2 * f * ρ) + Real.log rd)) := by
    linear_combination hlog
  have e2 : (f : ℝ) * ρ * (2 * -Real.log lam + (Real.log (2 * f * ρ) + Real.log rd)) ≤
      f * ρ * (2 * Real.posLog (1 / lam) + Real.log (2 * f * j' * rd)) :=
    mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  have e3 : (f : ℝ) * ρ * (2 * Real.posLog (1 / lam) + Real.log (2 * f * j' * rd)) ≤
      f * j' * (2 * Real.posLog (1 / lam) + Real.log (2 * f * j' * rd)) :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hJ hF.le) h3
  linarith

theorem UnitaryCovolumeLowerBound.proof (hE : UnitaryCovolume.Statement) (hM : UnitaryMinkowskiBound.Statement) (hR : UnitaryIsotropicRank.Statement)
    (hP : UnitaryFirstMinimumPositive.Statement) : UnitaryCovolumeLowerBound.Statement := by
  intro II Ψ _ K _ ι _ Ω _ _ E _ _ Em _ _ _ D z hz
  have hlam := hP D z hz
  have hrd := UnitaryCovolumeLowerBound.one_le_rootDiscr Em
  have hcast : ((Fintype.card Ψ * (D.N - D.j) : ℕ) : ℝ) = (D.f * D.j' : ℝ) := by
    push_cast
    rfl
  rw [hcast, ← one_div]
  have hrhs : 0 ≤ (D.f * D.j' : ℝ) *
      (2 * Real.posLog (1 / D.lam1 z) + Real.log (2 * (D.f * D.j' : ℝ) * rootDiscr Em)) := by
    rcases Nat.eq_zero_or_pos (D.f * D.j') with h0 | h0
    · have : (D.f * D.j' : ℝ) = 0 := by exact_mod_cast h0
      rw [this, zero_mul]
    · have h1 : (1 : ℝ) ≤ D.f * D.j' := by exact_mod_cast h0
      have : (1 : ℝ) ≤ 2 * (D.f * D.j' : ℝ) * rootDiscr Em := by
        have h2 : (1 : ℝ) ≤ 2 * (D.f * D.j' : ℝ) := by linarith
        exact one_le_mul_of_one_le_of_one_le h2 hrd
      have := Real.log_nonneg this
      have := Real.posLog_nonneg (x := 1 / D.lam1 z)
      positivity
  unfold FullerData.cuspU
  refine max_le hrhs (Real.iSup_le (fun s => ?_) hrhs)
  by_cases h : ∃ ρ v, IsNzFamily (D.torLat s) ρ v
  · obtain ⟨ρ, v, hv⟩ := h
    rw [← mul_assoc 2]
    exact UnitaryCovolumeLowerBound.neg_log_le hlam hrd hv.1 (hR D.herm (D.torLat s) (D.torLat_iso s) ρ v hv)
      (hE D z hz (D.torLat s) (D.torLat_le s) (D.torLat_iso s) (D.torLat_sat s) ρ v hv)
      (hM D z hz (D.torLat s) (D.torLat_le s) ρ v hv)
  · have : D.nz z (D.torLat s) = 1 := by
      unfold FullerData.nz HermDatum.nz
      rw [dif_neg h]
    rw [this, Real.log_one, neg_zero]
    exact hrhs

end GroundTheory.Heights₂.Heights.NineStatements
