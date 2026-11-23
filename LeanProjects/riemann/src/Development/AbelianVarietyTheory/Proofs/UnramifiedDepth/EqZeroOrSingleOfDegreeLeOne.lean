import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.ChartChg
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.FormalCompApplyEqMvPowerSeriesSubst
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.PderivSecondEvFirstPointEqZero

open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB

namespace GlobalTheory.FormalLog

theorem eq_zero_or_single_of_degree_le_one {σ : Type} (μ : σ →₀ ℕ) (h : μ.degree ≤ 1) :
    μ = 0 ∨ ∃ s, μ = Finsupp.single s 1 := by
  classical
  by_cases h0 : μ = 0
  · exact Or.inl h0
  · right
    obtain ⟨s, hs⟩ := Finsupp.ne_iff.1 h0
    have hs' : 1 ≤ μ s := Nat.one_le_iff_ne_zero.2 hs
    have hle : Finsupp.single s 1 ≤ μ := Finsupp.single_le_iff.2 hs'
    obtain ⟨ν, rfl⟩ := exists_add_of_le hle
    rw [map_add, Finsupp.degree_single] at h
    have : ν = 0 := (Finsupp.degree_eq_zero_iff ν).1 (by omega)
    exact ⟨s, by rw [this, add_zero]⟩

theorem exists_log_exp :
    ∀ (k : Type) [CommRing k] [Algebra ℚ k] (d : ℕ) (G : FGLaw k d), ∃ lg ex : Pt k 1 d, (∀ i (μ : Fin 1 × Fin d →₀ ℕ), μ.degree ≤ 1 → MvPowerSeries.coeff μ (lg i) = MvPowerSeries.coeff μ (MvPowerSeries.X ((0 : Fin 1), i) : PS k 1 d)) ∧ (∀ i, ev (n := 2) ![addOf G.F (pt k d 0) (pt k d 1)] (lg i) = ev (n := 2) ![pt k d 0] (lg i) + ev (n := 2) ![pt k d 1] (lg i)) ∧ (∀ i, MvPowerSeries.constantCoeff (ex i) = 0) ∧ comp1 lg ex = pt k d 0 ∧ comp1 ex lg = pt k d 0 := by
  intro k _ _ d G
  obtain ⟨lg, h0, h1, hadd⟩ := logSt_and_logDerivSt.1 k d G
  obtain ⟨ex, -, he, ha, hb⟩ := GlobalTheory.ChartInv.exists_isInvPair k d lg h0 (by rw [h1]; simp)
  refine ⟨lg, ex, ?_, fun i => congrFun hadd i, he, ha, hb⟩
  intro i μ hμ
  rcases eq_zero_or_single_of_degree_le_one μ hμ with rfl | ⟨⟨a, j⟩, rfl⟩
  · rw [MvPowerSeries.coeff_zero_eq_constantCoeff_apply, h0, MvPowerSeries.coeff_zero_X]
  · obtain rfl : a = 0 := Subsingleton.elim _ _
    have hc := congrFun (congrFun h1 i) j
    simp only [dLin] at hc
    rw [hc, MvPowerSeries.coeff_X, Matrix.one_apply]
    by_cases hij : i = j
    · simp [hij]
    · have : Finsupp.single ((0 : Fin 1), j) 1 ≠ Finsupp.single ((0 : Fin 1), i) 1 := by
        intro h
        have := Finsupp.single_left_injective (one_ne_zero (α := ℕ)) h
        exact hij (Prod.mk.inj this).2.symm
      rw [if_neg hij, if_neg this]

end GlobalTheory.FormalLog
