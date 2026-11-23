import Mathlib
import Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.StatementB
import Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.LogarithmicSubstitution.OneAddMulDerivLogSubst
import Formalism.GL3MeanSquares.HookFormulaTorsion.ExpSeries

noncomputable section

namespace Formalism.L2.Th1.B.Sim

open Finset
open Formalism.DworkPowerSeriesWeights (Integral mvExp)
open Formalism.InvariantFactorPaths.G7 (Simeq)
open Formalism.HermitianLattices.ExpSeriesBivariate (InLam)
open Formalism.HermitianLattices.ExpSeriesBivariate.ExpSeriesAddition (inLam_zero inLam_add inLam_neg inLam_nsmul integral_of_mul_eq_one)

variable {K ι : Type} [NormedField K] [CharZero K]

theorem simeq_iff (f g : MvPowerSeries ι K) : Simeq f g ↔ InLam (f - g) := Iff.rfl

theorem inLam_zsmul [IsUltrametricDist K] {f : MvPowerSeries ι K} (hf : InLam f) (n : ℤ) :
    InLam (n • f) := by
  obtain ⟨m, rfl | rfl⟩ := n.eq_nat_or_neg
  · rw [natCast_zsmul]; exact inLam_nsmul hf m
  · rw [neg_zsmul, natCast_zsmul]; exact inLam_neg (inLam_nsmul hf m)

theorem integral_of_sq [IsUltrametricDist K] {y : MvPowerSeries ι K} (h2 : ‖(2 : K)‖ = 1)
    (hy0 : MvPowerSeries.constantCoeff y = 1) (hy : Integral (y * y)) : Integral y := by
  classical
  have main : ∀ (m : ℕ) (d : ι →₀ ℕ), d.degree = m → ‖MvPowerSeries.coeff d y‖ ≤ 1 := by
    intro m
    induction m using Nat.strong_induction_on with
    | _ m ih =>
      intro d hd
      by_cases hd0 : d = 0
      · subst hd0
        rw [MvPowerSeries.coeff_zero_eq_constantCoeff_apply, hy0, norm_one]
      have hmem : ((d, 0) : (ι →₀ ℕ) × (ι →₀ ℕ)) ∈ (antidiagonal d).erase ((0 : ι →₀ ℕ), d) := by
        refine Finset.mem_erase.mpr ⟨fun h => hd0 (congrArg Prod.fst h), by simp⟩
      have h1 : MvPowerSeries.coeff d (y * y) = _ := MvPowerSeries.coeff_mul d y y
      rw [← Finset.add_sum_erase _ _ (show ((0 : ι →₀ ℕ), d) ∈ antidiagonal d by simp),
        ← Finset.add_sum_erase _ _ hmem] at h1
      simp only [MvPowerSeries.coeff_zero_eq_constantCoeff_apply, hy0, one_mul, mul_one] at h1
      have h3 : 2 * MvPowerSeries.coeff d y = MvPowerSeries.coeff d (y * y) +
          - ∑ p ∈ ((antidiagonal d).erase ((0 : ι →₀ ℕ), d)).erase (d, 0),
            MvPowerSeries.coeff p.1 y * MvPowerSeries.coeff p.2 y := by
        rw [h1]; ring
      have h4 : ‖MvPowerSeries.coeff d y‖ = ‖2 * MvPowerSeries.coeff d y‖ := by
        rw [norm_mul, h2, one_mul]
      rw [h4, h3]
      refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hy d) ?_)
      rw [norm_neg]
      refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun p hp => ?_
      rw [norm_mul]
      have hpa := Finset.mem_erase.mp hp
      have hpb := Finset.mem_erase.mp hpa.2
      have hp1 : p.1 + p.2 = d := by simpa using hpb.2
      have hdeg : p.1.degree + p.2.degree = d.degree := by rw [← map_add, hp1]
      have hne1 : p.1 ≠ 0 := by
        intro h0
        apply hpb.1
        ext1
        · exact h0
        · simpa [h0] using hp1
      have hne2 : p.2 ≠ 0 := by
        intro h0
        apply hpa.1
        ext1
        · simpa [h0] using hp1
        · exact h0
      have hpos1 : p.1.degree ≠ 0 := fun h => hne1 ((Finsupp.degree_eq_zero_iff _).mp h)
      have hpos2 : p.2.degree ≠ 0 := fun h => hne2 ((Finsupp.degree_eq_zero_iff _).mp h)
      exact mul_le_one₀ (ih p.1.degree (by omega) p.1 rfl) (norm_nonneg _)
        (ih p.2.degree (by omega) p.2 rfl)
  exact fun d => main _ d rfl

theorem inLam_of_two_mul [IsUltrametricDist K] {f : MvPowerSeries ι K} (h2 : ‖(2 : K)‖ = 1)
    (hf : InLam (2 * f)) : InLam f := by
  have h0 : MvPowerSeries.constantCoeff f = 0 := by
    have h := hf.1
    rw [map_mul, map_ofNat] at h
    exact (mul_eq_zero.mp h).resolve_left two_ne_zero
  refine ⟨h0, integral_of_sq h2 (constantCoeff_fExp h0) ?_⟩
  have h := hf.2
  rw [two_mul] at h
  have e : fExp (f + f) = fExp f * fExp f := fExp_add h0 h0
  exact e ▸ h

theorem inLam_fLog {g : MvPowerSeries ι K} (hg0 : MvPowerSeries.constantCoeff g = 1)
    (hg : Integral g) : InLam (fLog g) := by
  refine ⟨constantCoeff_fLog hg0, ?_⟩
  have e : fExp (fLog g) = g := fExp_fLog hg0
  have h : Integral (fExp (fLog g)) := by rw [e]; exact hg
  exact h

end Formalism.L2.Th1.B.Sim

namespace Formalism.L2.Th1.B.Sim

open Formalism.HermitianLattices.ExpSeriesBivariate.ExpSeriesAddition (inLam_add inLam_neg)

theorem simeq_integral_series : SimeqInt := by
  intro K ι _ _ _ f g f' g' h h'
  rw [simeq_iff] at h h'
  refine ⟨?_, ?_, fun n => ?_⟩
  · rw [simeq_iff]
    have e : f - f' - (g - g') = (f - g) + -(f' - g') := by ring
    rw [e]; exact inLam_add h (inLam_neg h')
  · rw [simeq_iff]
    have e : -f - -g = -(f - g) := by ring
    rw [e]; exact inLam_neg h
  · rw [simeq_iff]
    have e : (n : MvPowerSeries ι K) * f - n * g = n • (f - g) := by
      rw [zsmul_eq_mul]; ring
    rw [e]; exact inLam_zsmul h n

theorem simeq_halving : SimeqHalf := by
  intro K ι _ _ _ f g h2 h
  rw [simeq_iff] at h ⊢
  rw [← mul_sub] at h
  exact inLam_of_two_mul h2 h

theorem simeq_formal_log : SimeqLog := by
  intro K ι _ _ _ g hg0 hg
  have h := inLam_fLog hg0 hg
  refine ⟨?_, ?_⟩
  · rw [simeq_iff, sub_zero]; exact h
  · rw [simeq_iff, sub_zero]; exact inLam_neg h

end Formalism.L2.Th1.B.Sim
