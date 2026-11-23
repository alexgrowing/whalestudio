import Mathlib
import ReciprocityTheory.AnalyticForms.LeviForms.IsRegFamilyInhabitStatement
import ReciprocityTheory.AnalyticForms.LeviForms.TailBoundA
import ReciprocityTheory.AnalyticForms.PotentialTheory.ContDiffAtOfIsPotential
import Development.AutomorphicSpectrum.Proofs.MetricProofs.CompChartEventuallyEq
import Development.AutomorphicSpectrum.Proofs.MetricProofs.LoglogQuotNonneg
import Development.AutomorphicSpectrum.Proofs.MetricProofs.RegularFamilyC2PullbackOfSection
open MeasureTheory Metric Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.AnForm.M.FinHolAtlas
open scoped ContDiff

namespace GlobalTheory.CompanionTheory.Ar.Giv

section PullTop

variable {e : ℕ} {X : Type} [TopologicalSpace X]

theorem isPsh_of_phi_eq {A : FinHolAtlas e X} {P Q : LocPot X} (hQ : IsPotential A Q)
    (hφ : P.φ = Q.φ) (hP : IsPsh A P) : IsPsh A Q := by
  intro x j y hy w
  obtain ⟨W, hW, hzW, G, hG, hGe⟩ :=
    hQ.2 x ((A.chart j).symm y) ((A.chart j).symm y) ⟨hy.2, Q.mem_U _⟩
  have hGa : AnalyticAt ℂ (G ∘ (A.chart j).symm) y := hG j y ⟨hy.1, hzW⟩
  have ho : IsOpen ((A.chart j).target ∩
      (A.chart j).symm ⁻¹' (W ∩ Q.U x ∩ Q.U ((A.chart j).symm y))) :=
    (A.chart j).isOpen_inter_preimage_symm ((hW.inter (Q.isOpen_U x)).inter (Q.isOpen_U _))
  have hev : (Q.φ x ∘ (A.chart j).symm) =ᶠ[𝓝 y] fun v =>
      (Q.φ ((A.chart j).symm y) ∘ (A.chart j).symm) v + 1 * ((G ∘ (A.chart j).symm) v).re := by
    filter_upwards [ho.mem_nhds ⟨hy.1, ⟨hzW, hy.2⟩, Q.mem_U _⟩] with v hv
    have := hGe _ hv.2
    simp only [Function.comp_apply]
    linarith
  have ho2 : IsOpen ((A.chart j).target ∩ (A.chart j).symm ⁻¹' Q.U ((A.chart j).symm y)) :=
    (A.chart j).isOpen_inter_preimage_symm (Q.isOpen_U _)
  have h2 : ContDiffAt ℝ 2 (Q.φ ((A.chart j).symm y) ∘ (A.chart j).symm) y :=
    ((hQ.1 _ j).contDiffAt (ho2.mem_nhds ⟨hy.1, Q.mem_U _⟩)).of_le
      (WithTop.coe_le_coe.2 (le_top : (2 : ℕ∞) ≤ ⊤))
  have hRe : ContDiffAt ℝ 2 (fun v => ((G ∘ (A.chart j).symm) v).re) y :=
    Complex.reCLM.contDiff.contDiffAt.comp y (hGa.restrictScalars (𝕜 := ℝ)).contDiffAt
  rw [levi_congr hev, levi_add_smul 1 h2 hRe, levi_re_analytic hGa, mul_zero, add_zero, ← hφ]
  exact hP _ j y ⟨hy.1, P.mem_U _⟩ w

end PullTop

end GlobalTheory.CompanionTheory.Ar.Giv

namespace GlobalTheory.CompanionTheory.Ar.Giv

theorem pullbackStatement : PullbackStatement := by
  intro e e' X X' _ _ _ _ _ _ A A' h hh Θ L Θ' s n n' m W m' W' hΘ hΘp hΘ' hΘ'p hL hs hsnc hs0
    hsnc' th ph phT C₅ C t₀ hSW hF hC2
  obtain ⟨hth, hSm, hPshOn, hbd⟩ := hSW
  have hΘpsh : IsPsh A Θ := TailBoundAlt.isPsh_of_isPosPot A Θ hΘp
  have hΘ'psh : IsPsh A' Θ' := TailBoundAlt.isPsh_of_isPosPot A' Θ' hΘ'p
  have hΘpb : IsPotential A' (Θ.pullback h hh.1) := isPotentialPullback A A' h hh Θ hΘ
  obtain ⟨K, hK0, -, hKpsh⟩ := TailBoundAlt.exists_psh_chern_bound A' Θ' (Θ.pullback h hh.1) hΘ' hΘ'p hΘpb
  have ht₀ : 0 < t₀ := hF.1
  have hU : IsOpen (bdry s)ᶜ := (LeviFormBoundaryTopology.isClosed_bdry hs).isOpen_compl
  set M : ℝ := max 1 K with hM
  have hM1 : 1 ≤ M := le_max_left _ _
  have hMK : K ≤ M := le_max_right _ _
  set C' : ℝ := |C| * M with hC'
  set t₁ : ℝ := min t₀ (Real.exp (-Real.exp 1)) with ht₁
  have ht₁0 : 0 < t₁ := lt_min ht₀ (Real.exp_pos _)
  have ht₁t₀ : t₁ ≤ t₀ := min_le_left _ _
  have ht₁e : t₁ ≤ Real.exp (-Real.exp 1) := min_le_right _ _
  have hCC' : |C| ≤ C' := le_mul_of_one_le_right (abs_nonneg C) hM1
  have F1 := isRegFamily_mono A Θ L s th ph phT C t₀ |C| t₁ hΘ hΘpsh hth hs0 hF le_rfl ht₁0 ht₁t₀ ht₁e
  have F2 := isRegFamily_mono A Θ L s th ph phT C t₀ C' t₁ hΘ hΘpsh hth hs0 hF hCC' ht₁0 ht₁t₀ ht₁e
  refine ⟨C', t₁, ⟨isPotentialPullback A A' h hh th hth, ?_, ?_, fun y hy => hbd (h y) hy⟩, ?_, ?_⟩
  · have := smoothOn_pull hh hU hSm
    rwa [Set.preimage_compl] at this
  · have := isPshOn_pull hh hU hth hSm hPshOn
    rwa [Set.preimage_compl] at this
  · obtain ⟨-, -, F1⟩ := F1
    obtain ⟨h1, h2, F2⟩ := F2
    refine ⟨h1, h2, fun t ht htt => ?_⟩
    obtain ⟨a1, a2, a3, a4, -, a6, a7, a8⟩ := F2 t ht htt
    obtain ⟨b1, -, -, -, b5, -⟩ := F1 t ht htt
    have hsm : A'.Smooth (phT t ∘ h) := by
      have := smoothOn_pull hh isOpen_univ a1
      rwa [Set.preimage_univ] at this
    refine ⟨hsm, fun y => a2 (h y), fun y hy => a3 (h y) hy, fun y => a4 (h y), ?_,
      fun y hy hyr => a6 (h y) hy hyr, fun y hy => a7 (h y) hy,
      fun t' h1 h2 y => a8 t' h1 h2 (h y)⟩

    set ε : ℝ := epsT |C| t with hε
    have hq := loglog_quot_nonneg ht (htt.trans ht₁e)
    have hε0 : 0 ≤ ε := by
      rw [hε, epsT_eq_mul]; exact mul_nonneg (abs_nonneg C) hq
    have hε' : epsT C' t = M * ε := by
      rw [hε, epsT, epsT, hC']; ring
    have hεK : 0 ≤ M * ε - K * ε := by nlinarith
    have hP0 : IsPotential A (th + LocPot.ofFun (phT t) + Θ.rsmul ε) :=
      isPotentialAdd A _ _ (isPotentialAdd A _ _ hth (isPotential_ofFun A _ b1))
        (isPotentialRsmul A ε Θ hΘ)
    have hD : IsPotential A' (Θ'.rsmul K + (Θ.pullback h hh.1).rsmul (-1)) :=
      isPotentialAdd A' _ _ (isPotentialRsmul A' K Θ' hΘ') (isPotentialRsmul A' (-1) _ hΘpb)
    have hS1 := isPotentialPullback A A' h hh _ hP0
    have hS1p := isPsh_pull hh hP0 b5
    have hS2 := isPotentialRsmul A' ε _ hD
    have hS2p := isPshRsmul A' ε _ hε0 hD hKpsh
    have hS3 := isPotentialRsmul A' (M * ε - K * ε) Θ' hΘ'
    have hS3p := isPshRsmul A' (M * ε - K * ε) Θ' hεK hΘ' hΘ'psh
    have hS := isPshAdd A' _ _ (isPotentialAdd A' _ _ hS1 hS2) hS3
      (isPshAdd A' _ _ hS1 hS2 hS1p hS2p) hS3p
    have hT : IsPotential A' (th.pullback h hh.1 + LocPot.ofFun (phT t ∘ h) + Θ'.rsmul (epsT C' t)) :=
      isPotentialAdd A' _ _ (isPotentialAdd A' _ _ (isPotentialPullback A A' h hh th hth)
        (isPotential_ofFun A' _ hsm)) (isPotentialRsmul A' _ Θ' hΘ')
    refine isPsh_of_phi_eq hT ?_ hS
    funext x y
    show th.φ (h x) (h y) + phT t (h y) + ε * Θ.φ (h x) (h y) +
        ε * (K * Θ'.φ x y + -1 * Θ.φ (h x) (h y)) + (M * ε - K * ε) * Θ'.φ x y =
      th.φ (h x) (h y) + phT t (h y) + epsT C' t * Θ'.φ x y
    rw [hε']
    ring
  · have hev : ∀ᶠ t in nhdsWithin (0 : ℝ) (Set.Ioi 0), A.Smooth (phT t) :=
      Filter.mem_of_superset (Ioc_mem_nhdsGT ht₀) fun t ht => (hF.2.2 t ht.1 ht.2).1
    exact regular_family_C2_pullback_of_open A A' h hh s ph phT hU hSm hev hC2

end GlobalTheory.CompanionTheory.Ar.Giv
