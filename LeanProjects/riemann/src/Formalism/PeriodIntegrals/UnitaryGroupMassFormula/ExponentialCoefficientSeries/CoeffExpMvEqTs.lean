import Mathlib
import Formalism.PeriodIntegrals.SimeqPdInt
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CubeFormalIdentities.CoeffPowMulPowEqZero

noncomputable section

open MvPowerSeries

namespace PI.UnitaryGroupMassFormula.SimeqPdInt

variable {p : ℕ} [Fact p.Prime] {σ : Type*}

theorem pd_eq [DecidableEq σ] (k : σ) (F : MvPowerSeries σ ℂ_[p]) :
    PI.SimeqPdInt.pd k F = pderiv ℂ_[p] k F := by
  ext n
  rw [coeff_pderiv]
  change ((n k : ℂ_[p]) + 1) * coeff (n + Finsupp.single k 1) F = _
  ring

def ts (f : MvPowerSeries σ ℂ_[p]) (N : ℕ) : MvPowerSeries σ ℂ_[p] :=
  ∑ n ∈ Finset.range N, ((n.factorial : ℂ_[p])⁻¹) • f ^ n

theorem coeff_ts (f : MvPowerSeries σ ℂ_[p]) (N : ℕ) (a : σ →₀ ℕ) :
    coeff a (ts f N) = ∑ n ∈ Finset.range N, coeff a (f ^ n) / (n.factorial : ℂ_[p]) := by
  simp only [ts, map_sum, coeff_smul]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [div_eq_inv_mul]

theorem coeff_expMv_eq_ts {f : MvPowerSeries σ ℂ_[p]} (hf : constantCoeff f = 0)
    {a : σ →₀ ℕ} {N : ℕ} (h : a.degree ≤ N) :
    coeff a (PI.FglGram.expMv f) = coeff a (ts f (N + 1)) := by
  rw [coeff_ts]
  exact PI.UnitaryGroupMassFormula.CubeRelationOfParallelogram.coeff_expMv_of_le hf N h

theorem pderiv_ts (k : σ) (f : MvPowerSeries σ ℂ_[p]) (N : ℕ) :
    pderiv ℂ_[p] k (ts f (N + 1)) = ts f N * pderiv ℂ_[p] k f := by
  simp only [ts, map_sum, Finset.sum_mul]
  rw [Finset.sum_range_succ']
  rw [pow_zero, Derivation.map_smul, pderiv_one, smul_zero, add_zero]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [Derivation.map_smul, pderiv_pow, Nat.add_sub_cancel, Algebra.smul_def, Algebra.smul_def]
  have h1 : ((n + 1 : ℕ) : ℂ_[p]) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
  have h2 : (n.factorial : ℂ_[p]) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
  have hc : (n.factorial : ℂ_[p])⁻¹ =
      ((n + 1).factorial : ℂ_[p])⁻¹ * ((n + 1 : ℕ) : ℂ_[p]) := by
    rw [Nat.factorial_succ, Nat.cast_mul]
    field_simp
  rw [hc, map_mul, map_natCast]
  ring

theorem pderiv_expMv (k : σ) {f : MvPowerSeries σ ℂ_[p]} (hf : constantCoeff f = 0) :
    pderiv ℂ_[p] k (PI.FglGram.expMv f) = PI.FglGram.expMv f * pderiv ℂ_[p] k f := by
  classical
  ext α
  have hdeg : (α + Finsupp.single k 1).degree ≤ α.degree + 1 := by
    rw [map_add]
    simp
  rw [coeff_pderiv, coeff_expMv_eq_ts hf hdeg, ← coeff_pderiv, pderiv_ts, coeff_mul, coeff_mul]
  refine Finset.sum_congr rfl fun q hq => ?_
  have hq' : q.1 + q.2 = α := by simpa using hq
  have hle : q.1.degree ≤ α.degree := by
    rw [← hq', map_add]
    omega
  rw [coeff_expMv_eq_ts hf hle]

theorem int_pderiv (k : σ) {F : MvPowerSeries σ ℂ_[p]} (hF : PI.FglGram.IntegralMv F) :
    PI.FglGram.IntegralMv (pderiv ℂ_[p] k F) := by
  intro n
  have hn := hF (n + Finsupp.single k 1)
  unfold PI.FglGram.IsIntP at hn ⊢
  rw [coeff_pderiv, norm_mul]
  refine mul_le_one₀ hn (norm_nonneg _) ?_
  have := IsUltrametricDist.norm_natCast_le_one ℂ_[p] (n k + 1)
  push_cast at this
  exact this

theorem target : PI.SimeqPdInt.Target := by
  intro p _ σ _ f hf k
  obtain ⟨h0, hE⟩ := hf
  rw [sub_zero] at h0 hE
  have hE' : PI.FglGram.IntegralMv (PI.FglGram.expMv f) := hE
  have hinv := PI.UnitaryGroupMassFormula.CubeRelationOfParallelogram.int_expMv_neg h0 hE'
  have hWV : PI.FglGram.expMv (-f) * PI.FglGram.expMv f = 1 := by
    rw [← PI.UnitaryGroupMassFormula.CubeRelationOfParallelogram.expMv_add (by rw [map_neg, h0, neg_zero]) h0, neg_add_cancel,
      PI.UnitaryGroupMassFormula.CubeRelationOfParallelogram.expMv_zero]
  have key : PI.SimeqPdInt.pd k f =
      PI.FglGram.expMv (-f) * pderiv ℂ_[p] k (PI.FglGram.expMv f) := by
    rw [pd_eq, pderiv_expMv k h0, ← mul_assoc, hWV, one_mul]
  rw [key]
  exact PI.UnitaryGroupMassFormula.CubeRelationOfParallelogram.int_mul hinv (int_pderiv k hE')

end PI.UnitaryGroupMassFormula.SimeqPdInt
