import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsRegAboveWeight
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsBdPtsNull
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsDivisorPreimageNull
import GroundTheory.HeightsAndTheta.Heights.Regularisation.PTruncPsh
import GroundTheory.HeightsAndTheta.Heights.Regularisation.PChartMollifiedBounds
import GroundTheory.HeightsAndTheta.Heights.Regularisation.ChartFun
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo Filter Topology

theorem RegAboveWeight.proof (hBd : BdPtsNull.Statement) (hDiv : DivisorPreimageNull.Statement) :
    RegAboveWeight.Statement := by
  intro II Ψ _ _ K _ ι _ Ω _ _ E _ _ D O Lt _ _ _ X
  obtain ⟨C, t₀, ht₀, hb⟩ := GroundTheory.Heights₂.Heights.Regular.ChartMollifiedBounds.proof
    GroundTheory.Heights₂.Heights.Regular.TruncPsh.proof X.M.Xc D.n X.M.atlas X.S.R X.S.ρ
  have hev : ∀ᶠ t in 𝓝[>] (0 : ℝ), t < t₀ ∧ 0 ≤ X.S.K t :=
    (eventually_nhdsWithin_of_eventually_nhds (eventually_lt_nhds ht₀)).and
      (X.S_tied.K_tendsto.eventually_ge_atTop 0)
  obtain ⟨t₂, ht₂, hsub⟩ := mem_nhdsGT_iff_exists_Ioc_subset.1 hev
  refine ⟨t₂, ht₂, D.Bd ∪ {z | X.M.proj z ∉ X.S.R.Yo}, ?_, fun t ht htt z hz hzN => ?_⟩
  ·
    intro Ψ' hΨ'
    refine measure_mono_null (fun y hy => ?_)
      (measure_union_null (hBd II Ψ K ι Ω E D Ψ' hΨ') (hDiv K ι _ _ X.M X.S.R Ψ' hΨ'))
    obtain ⟨z, hz, hzN, hzy⟩ := hy
    rcases hzN with h | h
    · exact Or.inl ⟨z, hz, h, hzy⟩
    · exact Or.inr ⟨z, hz, h, hzy⟩
  obtain ⟨htt₀, hK⟩ : t < t₀ ∧ 0 ≤ X.S.K t := hsub ⟨ht, htt⟩
  have hBdz : z ∉ D.Bd := fun h => hzN (Or.inl h)
  have hY : X.M.proj z ∈ X.S.R.Yo := by
    by_contra h
    exact hzN (Or.inr h)
  have hXo : z ∈ D.Xo := Set.mem_sdiff_of_mem hz hBdz

  obtain ⟨k, hk⟩ := X.S.R.cover (X.M.proj z)
  have hkm := X.S.R.inner_subset_mid k hk
  have hε : 0 ≤ X.S.e1 t := ht.le.trans (X.S.e1_ge t ht)

  have h1 := ((hb t ht htt₀).2 (X.S.K t) hK k (X.M.proj z) hkm).2.2 hY

  have h2 := GroundTheory.Heights₂.Heights.Regular.LogLogRegularisation.le_glue X.S.R.toPotentialCharts
    (fun j x => X.S.R.phReg X.S.ρ (X.S.K t) t j x + 4 * X.S.e1 t * X.S.η j x) hε hkm
  have h3 : X.S.regWeight t (X.M.proj z) = X.S.R.glue
      (fun j x => X.S.R.phReg X.S.ρ (X.S.K t) t j x + 4 * X.S.e1 t * X.S.η j x) (X.S.e1 t) (X.M.proj z) := rfl
  have hη := X.S.cutoff.eq_zero k (X.M.proj z) hk
  simp only [hη, mul_zero, add_zero] at h2

  have h4 := X.S.ph_eq z ⟨hXo, hz⟩ hY
  have h5 : phMu X.H z = Real.log ((muLine X.H).h z) := rfl
  rw [h3, h5]
  linarith

end GroundTheory.Heights₂.Heights.LowerBoundFree
