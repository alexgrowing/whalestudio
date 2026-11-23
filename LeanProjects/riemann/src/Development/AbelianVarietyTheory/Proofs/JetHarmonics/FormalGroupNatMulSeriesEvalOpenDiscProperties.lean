import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.PowerSeriesHasSumAt
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.MvPowerSeriesIntegralBoundedClosure
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.PowerSeriesEvalTsumUnitDiscPropertiesStatement
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.FormalGroupNatMulSeriesProperties

open GlobalTheory.ConvSer

namespace GlobalTheory.ConvSer

theorem intg_nMul_for_point {K : Type} [NormedField K] [IsUltrametricDist K] (F : FormalGroup K)
    (hF : Intg F.toPowerSeries) (n : ℕ) : Intg (nMul F n) := by
  induction n with
  | zero =>
    rw [nMul_zero]
    exact GlobalTheory.BddAlg.intg_zero
  | succ n ih =>
    rw [nMul_succ]
    have hX : Intg (PowerSeries.X : PowerSeries K) := (GlobalTheory.BddAlg.small_X ()).1
    refine GlobalTheory.BddAlg.Le.subst (c := 1) (fun j => ?_) (fun j => ?_) hF
    · fin_cases j
      · exact ih
      · exact hX
    · fin_cases j
      · exact nMul_constantCoeff F n
      · exact PowerSeries.constantCoeff_X

private lemma ev1_zero {K : Type} [NormedField K] (y : K) : ev1 (0 : PowerSeries K) y = 0 := by
  simp [ev1]

theorem nMul_point : ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CompleteSpace K] (F : FormalGroup K), Intg F.toPowerSeries → (∀ n, Intg (nMul F n)) ∧ ∀ x : K, ‖x‖ < 1 → ev1 (nMul F 0) x = 0 ∧ ev1 (nMul F 1) x = x ∧ (∀ j, ‖ev1 (nMul F j) x‖ ≤ ‖x‖ ∧ (‖(j : K)‖ = 1 → ‖ev1 (nMul F j) x‖ = ‖x‖)) ∧ (∀ i j, ev F.toPowerSeries ![ev1 (nMul F i) x, ev1 (nMul F j) x] = ev1 (nMul F (i + j)) x) ∧ (∀ i j, ev1 (nMul F i) (ev1 (nMul F j) x) = ev1 (nMul F (i * j)) x) ∧ (∀ y : K, ‖y‖ < 1 → ev F.toPowerSeries ![0, y] = y ∧ ev F.toPowerSeries ![y, 0] = y) := by
  intro K _ _ _ F hF
  have hI : ∀ n, Intg (nMul F n) := intg_nMul_for_point F hF
  have hB : Bdd F.toPowerSeries := GlobalTheory.BddAlg.bdd_of_intg hF
  have hX : Intg (PowerSeries.X : PowerSeries K) := (GlobalTheory.BddAlg.small_X ()).1

  have hleft : MvPowerSeries.subst (![0, PowerSeries.X] : Fin 2 → MvPowerSeries Unit K)
      F.toPowerSeries = PowerSeries.X := by
    have h := nMul_succ F 0
    rw [nMul_zero, nMul_one] at h
    exact h.symm
  have hright : MvPowerSeries.subst (![PowerSeries.X, 0] : Fin 2 → MvPowerSeries Unit K)
      F.toPowerSeries = PowerSeries.X := by
    have h := nMul_add F 1 0
    rw [nMul_zero, nMul_one] at h
    simpa using h
  refine ⟨hI, fun x hx => ?_⟩
  obtain ⟨-, -, -, hevX, -, -, hnorm, hsub, hpair, -, -⟩ := _root_.GlobalTheory.T.powerSeriesEvalTsum_unitDisc_properties_alt K x hx
  refine ⟨by rw [nMul_zero]; exact ev1_zero x, by rw [nMul_one]; exact hevX, fun j => ?_,
    fun i j => ?_, fun i j => ?_, fun y hy => ?_⟩
  · obtain ⟨-, h1, h2⟩ := hnorm (nMul F j) (hI j)
    have h0 : PowerSeries.coeff 0 (nMul F j) = 0 := by
      rw [PowerSeries.coeff_zero_eq_constantCoeff_apply]
      exact nMul_constantCoeff F j
    rw [h0, sub_zero] at h1 h2
    rw [nMul_coeff_one] at h2
    refine ⟨h1, fun hj => ?_⟩
    rcases eq_or_ne x 0 with rfl | hx0
    · simpa using h1
    · have hpos : 0 < ‖x‖ := norm_pos_iff.mpr hx0
      have hsq : ‖x‖ ^ 2 < ‖x‖ := by nlinarith
      have hjx : ‖(j : K) * x‖ = ‖x‖ := by rw [norm_mul, hj, one_mul]
      set v := ev1 (nMul F j) x
      have hlt : ‖v - (j : K) * x‖ < ‖(j : K) * x‖ := by rw [hjx]; exact lt_of_le_of_lt h2 hsq
      have hdecomp : v = (j : K) * x + (v - (j : K) * x) := by ring
      rw [hdecomp, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm hlt.ne',
        max_eq_left hlt.le, hjx]
  · rw [← hpair F.toPowerSeries (nMul F i) (nMul F j) hB (hI i) (hI j)
      (nMul_constantCoeff F i) (nMul_constantCoeff F j), nMul_add]
  · rw [← hsub (nMul F i) (nMul F j) (hI j) (nMul_constantCoeff F j)
      (GlobalTheory.BddAlg.bdd_of_intg (hI i)), nMul_subst_nMul]
  · obtain ⟨-, -, -, hevXy, -, -, -, -, hpairy, -, -⟩ := _root_.GlobalTheory.T.powerSeriesEvalTsum_unitDisc_properties_alt K y hy
    have hz : Intg (0 : PowerSeries K) := GlobalTheory.BddAlg.intg_zero
    have hc0 : PowerSeries.constantCoeff (0 : PowerSeries K) = 0 := by simp
    have hcX : PowerSeries.constantCoeff (PowerSeries.X : PowerSeries K) = 0 := by simp
    constructor
    · have h := hpairy F.toPowerSeries 0 PowerSeries.X hB hz hX hc0 hcX
      rw [hleft, hevXy, ev1_zero] at h
      exact h.symm
    · have h := hpairy F.toPowerSeries PowerSeries.X 0 hB hX hz hcX hc0
      rw [hright, hevXy, ev1_zero] at h
      exact h.symm

end GlobalTheory.ConvSer
