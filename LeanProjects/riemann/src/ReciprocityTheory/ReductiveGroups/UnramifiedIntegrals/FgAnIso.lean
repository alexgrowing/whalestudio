import Mathlib
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.FgAnWp

noncomputable section

namespace ReciprocityTheory.ChartRestriction.L1

open PowerSeries Formalism.G Formalism.LT Formalism.L2.Th1.CM
open Formalism.L2.Th1

section MapLemmas

variable {K K' : Type} [Field K] [Field K'] (φ : K →+* K')

theorem anIso_map_dblInt (e : PowerSeries K) :
    PowerSeries.map φ (C.dblInt e) = C.dblInt (PowerSeries.map φ e) := by
  ext n
  simp only [C.dblInt, PowerSeries.coeff_map, PowerSeries.coeff_mk]
  split_ifs
  · simp
  · simp [map_div₀]

theorem anIso_constantCoeff_dblInt (e : PowerSeries K) :
    PowerSeries.constantCoeff (C.dblInt e) = 0 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
  simp [C.dblInt]

theorem anIso_map_lam (e : PowerSeries K) (s2 : K) :
    PowerSeries.map φ (C.lam e s2) = C.lam (PowerSeries.map φ e) (φ s2) := by
  simp only [C.lam, map_add, map_mul, map_pow, anIso_map_dblInt, PowerSeries.map_C, PowerSeries.map_X,
    map_div₀, map_ofNat]

theorem anIso_constantCoeff_lam (e : PowerSeries K) (s2 : K) :
    PowerSeries.constantCoeff (C.lam e s2) = 0 := by
  simp [C.lam, anIso_constantCoeff_dblInt]

theorem anIso_map_sgStar [CharZero K] [CharZero K'] (e : PowerSeries K) (s2 : K) :
    PowerSeries.map φ (C.sgStar e s2) = C.sgStar (PowerSeries.map φ e) (φ s2) := by
  have h0 : PowerSeries.constantCoeff (-(C.lam e s2)) = 0 := by
    simp [anIso_constantCoeff_lam]
  have h1 : PowerSeries.map φ (C.mvExp (-(C.lam e s2)))
      = C.mvExp (-(C.lam (PowerSeries.map φ e) (φ s2))) := by
    unfold C.mvExp
    have := PowerSeries.map_subst (h := φ) (PowerSeries.HasSubst.of_constantCoeff_zero' h0)
      (PowerSeries.exp K)
    rw [PowerSeries.map_exp] at this
    rw [← anIso_map_lam, ← map_neg]
    exact this
  rw [C.sgStar, map_mul, PowerSeries.map_X, h1, C.sgStar]

theorem anIso_map_wpShift (e : PowerSeries K) (c : K) :
    PowerSeries.map φ (C.wpShift e c) = C.wpShift (PowerSeries.map φ e) (φ c) := by
  simp only [C.wpShift, map_add, map_one, map_mul, map_pow, map_sub, PowerSeries.map_C,
    PowerSeries.map_X]

end MapLemmas

theorem isogenyFormula_map {K K' : Type} [Field K] [CharZero K] [Field K'] [CharZero K']
    (φ : K →+* K') (e : PowerSeries K) (s2 : K) {κ : Type} [Fintype κ] (c : κ → K) (al : K)
    (h : C.IsogenyFormula e s2 c al) :
    C.IsogenyFormula (PowerSeries.map φ e) (φ s2) (fun P => φ (c P)) (φ al) := by
  have h' := congrArg (PowerSeries.map φ) h
  unfold C.IsogenyFormula
  simp only [map_mul, map_pow, map_prod, PowerSeries.map_X, PowerSeries.map_C, anIso_map_wpShift,
    anIso_map_sgStar, ← PowerSeries.rescale_map] at h'
  rw [map_pow]
  exact h'

theorem iso_formula (l : ℕ) [Fact l.Prime] (L : PeriodPair) (ι : ℂ ≃+* ℂ_[l]) (α : ℂ)
    (S : Finset ℂ) (hα : α ≠ 0) (hst : F.MulStable L α) (hS : F.IsKerReps L α S) :
    C.IsogenyFormula (A.wpReg (A.shortW (ι L.g₂) (ι L.g₃))) (ι (F.s2 L))
      (fun P : S => ι (L.weierstrassP (P : ℂ))) (ι α) := by
  rw [wp_bridge]
  exact isogenyFormula_map (ι : ℂ →+* ℂ_[l]) (F.pSeries L) (F.s2 L)
    (fun P : S => L.weierstrassP (P : ℂ)) α (F.isogenyFormulaInstance L α S hα hst hS)

end ReciprocityTheory.ChartRestriction.L1
