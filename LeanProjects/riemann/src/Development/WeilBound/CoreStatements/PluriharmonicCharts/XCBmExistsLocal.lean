import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GlobalPairSumGramBoundStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.PeriodGramSmoothPuncturedStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.PeriodGramComparisonBoundStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GramMatrixChangeFrameStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.InteriorPointPolarisedStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LocalRingPointsExistsUniqueStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ComplexPointsIffCentresStatement
import Development.WeilBound.CoreStatements.PluriharmonicCharts.XCBmExistsSumframe
import Development.WeilBound.CoreStatements.PluriharmonicCharts.AnalyticRecentre
import Development.WeilBound.CoreStatements.PluriharmonicCharts.InBlockChartOfInChart
import Development.AutomorphicSpectrum.Statements.TowerExistence.GoodTowerExistsX
import Development.AutomorphicSpectrum.Statements.MetricStatements.ExistsFlagModelBaseMetric
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.RootOnFund
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ContDiffUncentre
import Development.AutomorphicSpectrum.Proofs.MetricProofs.OmHeightslockG

open AlgebraicGeometry CategoryTheory NumberField Matrix ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.BMx ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P
open ReciprocityTheory.ChartRestriction.G.Semi
open scoped ComplexOrder

namespace PositivityTheory.Xgp.c_bm_exists_local

open GlobalTheory.CompanionTheory.Ar.HodgeMetric Filter Topology

theorem logR_le {n a : ℕ} {w₀ w : Fin n → ℂ} {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) {π : Equiv.Perm (Fin n)}
    {S : Finset (Fin n)} {m : Fin n → ℕ} (hm : ∀ i ∈ S, 1 ≤ m i) (hw : ‖w‖ ≤ 2) (hS : ∀ i ∈ S, w i ≠ 0)
    (ha : ∀ i : Fin n, (i : ℕ) < a → π.symm i ∈ S ∧ w₀ (π.symm i) = 0) :
    (Real.exp 1 + ∑ i : Fin n, if (i : ℕ) < a then Real.log (1 / ‖uncentre w₀ ρ π w i‖ ^ 2) else 0) ≤ rLoc S m w := by
  have hg : ∀ j ∈ S, 0 ≤ Real.log (4 / ‖w j‖ ^ 2) := by
    intro j hj
    apply Real.log_nonneg
    have h0 : 0 < ‖w j‖ := norm_pos_iff.2 (hS j hj)
    have h2 : ‖w j‖ ≤ 2 := (norm_le_pi_norm w j).trans hw
    rw [le_div_iff₀ (by positivity)]
    nlinarith
  have hinv : 1 ≤ ρ⁻¹ := (one_le_inv₀ hρ).2 hρ1
  have hterm : ∀ i : Fin n, (i : ℕ) < a →
      Real.log (1 / ‖uncentre w₀ ρ π w i‖ ^ 2) ≤ Real.log (4 / ‖w (π.symm i)‖ ^ 2) := by
    intro i hi
    obtain ⟨hS', h0'⟩ := ha i hi
    have hpos : 0 < ‖w (π.symm i)‖ := norm_pos_iff.2 (hS _ hS')
    have hu : ‖uncentre w₀ ρ π w i‖ = ρ⁻¹ * ‖w (π.symm i)‖ := by
      simp [uncentre, h0', norm_mul, abs_of_pos hρ]
    have hx : ‖w (π.symm i)‖ ≤ ρ⁻¹ * ‖w (π.symm i)‖ := by nlinarith
    apply Real.log_le_log
    · rw [hu]
      positivity
    · rw [hu, div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith
  unfold rLoc
  refine add_le_add le_rfl ?_
  calc (∑ i : Fin n, if (i : ℕ) < a then Real.log (1 / ‖uncentre w₀ ρ π w i‖ ^ 2) else 0)
      ≤ ∑ i : Fin n, if (i : ℕ) < a then Real.log (4 / ‖w (π.symm i)‖ ^ 2) else 0 := by
        refine Finset.sum_le_sum fun i _ => ?_
        split_ifs with h
        · exact hterm i h
        · exact le_rfl
    _ = ∑ j : Fin n, if ((π j : Fin n) : ℕ) < a then Real.log (4 / ‖w j‖ ^ 2) else 0 := by
        rw [← Equiv.sum_comp π]
        simp
    _ = ∑ j ∈ Finset.univ.filter (fun j => ((π j : Fin n) : ℕ) < a), Real.log (4 / ‖w j‖ ^ 2) :=
        (Finset.sum_filter _ _).symm
    _ ≤ ∑ j ∈ S, Real.log (4 / ‖w j‖ ^ 2) := by
        refine Finset.sum_le_sum_of_subset_of_nonneg (fun j hj => ?_) (fun j hj _ => hg j hj)
        have := (ha (π j) (Finset.mem_filter.1 hj).2).1
        simpa using this
    _ ≤ ∑ j ∈ S, (m j : ℝ) * Real.log (4 / ‖w j‖ ^ 2) := by
        refine Finset.sum_le_sum fun j hj => ?_
        exact le_mul_of_one_le_left (hg j hj) (by exact_mod_cast hm j hj)

theorem exists_hasFDerivAt_uncentre {n : ℕ} (w₀ : Fin n → ℂ) (ρ : ℝ) (π : Equiv.Perm (Fin n)) :
    ∃ A : (Fin n → ℂ) →L[ℝ] (Fin n → ℂ), ∀ w, HasFDerivAt (uncentre w₀ ρ π) A w := by
  let L : (Fin n → ℂ) →L[ℂ] (Fin n → ℂ) :=
    ContinuousLinearMap.pi fun i => (ρ : ℂ)⁻¹ • ContinuousLinearMap.proj (R := ℂ) (π.symm i)
  refine ⟨L.restrictScalars ℝ, fun w => ?_⟩
  have hf : uncentre w₀ ρ π = fun t => L.restrictScalars ℝ t - L.restrictScalars ℝ w₀ := by
    funext t i
    simp [uncentre, L, mul_sub]
  rw [hf]
  exact (L.restrictScalars ℝ).hasFDerivAt.sub_const _

theorem posDef_of_inv {N : ℕ} {Γ : Matrix (Fin N) (Fin N) ℂ} {c : ℝ} (hc : 0 < c)
    (h : (Γ⁻¹ - (c : ℂ) • (1 : Matrix (Fin N) (Fin N) ℂ)).PosSemidef) : Γ.PosDef := by
  have h1 : ((c : ℂ) • (1 : Matrix (Fin N) (Fin N) ℂ)).PosDef :=
    Matrix.PosDef.smul Matrix.PosDef.one (by exact_mod_cast hc)
  have h2 := h1.add_posSemidef h
  rw [add_sub_cancel] at h2
  exact Matrix.posDef_inv_iff.1 h2

theorem psd_mono {N : ℕ} {A : Matrix (Fin N) (Fin N) ℂ} {r r' : ℝ} (hr : r ≤ r')
    (h : (((r : ℝ) : ℂ) • (1 : Matrix (Fin N) (Fin N) ℂ) - A).PosSemidef) :
    (((r' : ℝ) : ℂ) • (1 : Matrix (Fin N) (Fin N) ℂ) - A).PosSemidef := by
  have hI : ((((r' - r : ℝ)) : ℂ) • (1 : Matrix (Fin N) (Fin N) ℂ)).PosSemidef :=
    Matrix.PosSemidef.one.smul (by exact_mod_cast sub_nonneg.2 hr)
  have h2 := h.add hI
  convert h2 using 1
  simp only [Complex.ofReal_sub, sub_smul]
  abel

end PositivityTheory.Xgp.c_bm_exists_local
