import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.IsFibreChartIff
import Development.AutomorphicSpectrum.Proofs.MetricProofs.LogResolutionFunctorialHolomorphic
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib

namespace GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib

open GlobalTheory.CompanionTheory.Ar.PB.Proj in

theorem holo_of_lift_orbit_top :
    ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P J : Ideal (MRing ι)) (D e : ℕ) (R : AnLogRes P J D) (V : Set (Fin e → ℂ)) (zex : (Fin e → ℂ) → (Σ k, ι k) → ℂ) (h : (Fin e → ℂ) → R.X), J = ⊤ → IsOpen V → (∀ q, AnalyticOnNhd ℂ (fun u => zex u q) V) → (∀ u ∈ V, zex u ∈ mcPts P) → (∀ u ∈ V, SameOrbit (R.lift (h u) (h u)) (zex u)) → ContinuousOn h V ∧ ∀ k, AnalyticOnNhd ℂ (R.A.chart k ∘ h) (V ∩ h ⁻¹' (R.A.chart k).source) := by
  intro K _ ι _ P J D e R V zex h hJ hV han hmc horb
  subst hJ
  have hloc : ∀ x, ∀ u ∈ V, h u ∈ R.U x → SameOrbit (R.lift x (h u)) (zex u) := fun x u hu hx =>
    orbit_trans (R.compat x (h u) (h u) ⟨hx, R.mem_U (h u)⟩) (horb u hu)
  have hcont : ∀ u0 ∈ V, ContinuousAt h u0 := by
    intro u0 hu0
    refine isCompact_univ.tendsto_nhds_of_unique_mapClusterPt
      (Filter.Eventually.of_forall fun _ => Set.mem_univ _) ?_
    intro x _ hx
    obtain ⟨𝒰, h𝒰, hx𝒰⟩ := mapClusterPt_iff_ultrafilter.1 hx
    have hev : ∀ᶠ u in (𝒰 : Filter (Fin e → ℂ)), u ∈ V ∧ h u ∈ R.U x := by
      have e1 : ∀ᶠ u in (𝒰 : Filter (Fin e → ℂ)), u ∈ V := h𝒰 (hV.mem_nhds hu0)
      have e2 : ∀ᶠ u in (𝒰 : Filter (Fin e → ℂ)), h u ∈ R.U x :=
        hx𝒰 ((R.isOpen_U x).mem_nhds (R.mem_U x))
      exact e1.and e2
    have hlim : ∀ q, Filter.Tendsto (fun u => R.lift x (h u) q) 𝒰 (𝓝 (R.lift x x q)) := fun q =>
      (continuousAt_of_holoOn R.A (R.holo x q) (R.mem_U x)).tendsto.comp hx𝒰
    have hzlim : ∀ q, Filter.Tendsto (fun u => zex u q) 𝒰 (𝓝 (zex u0 q)) := fun q =>
      (han q u0 hu0).continuousAt.tendsto.comp (Filter.tendsto_id'.2 h𝒰)
    have horb0 : SameOrbit (R.lift x x) (zex u0) := by
      refine orbit_of_cross (R.mem x x (R.mem_U x)).1 (hmc u0 hu0).1 ?_
      intro k i i'
      have h1 := ((hlim ⟨k, i⟩).mul (hzlim ⟨k, i'⟩)).sub ((hlim ⟨k, i'⟩).mul (hzlim ⟨k, i⟩))
      have h2 : ∀ᶠ u in (𝒰 : Filter (Fin e → ℂ)),
          (0 : ℂ) = R.lift x (h u) ⟨k, i⟩ * zex u ⟨k, i'⟩ - R.lift x (h u) ⟨k, i'⟩ * zex u ⟨k, i⟩ :=
        hev.mono fun u hu => (sub_eq_zero.2 (orbit_cross (hloc x u hu.1 hu.2) k i i')).symm
      have h3 := tendsto_nhds_unique h1 (tendsto_const_nhds.congr' h2)
      exact sub_eq_zero.1 h3
    exact R.inj x (h u0) (not_mem_mcPts_top _) (orbit_trans horb0 (orbit_symm (horb u0 hu0)))
  refine ⟨fun u hu => (hcont u hu).continuousWithinAt, ?_⟩
  rintro k u0 ⟨hu0, hs0⟩
  have hs0' : h u0 ∈ (R.A.chart k).source := hs0
  choose p hp using (R.mem (h u0) (h u0) (R.mem_U (h u0))).1
  have hsym : (R.A.chart k).symm (R.A.chart k (h u0)) = h u0 := (R.A.chart k).left_inv hs0'
  have ha : AnalyticAt ℂ (fun w => affCoord p (R.lift (h u0) ((R.A.chart k).symm w))) (R.A.chart k (h u0)) :=
    analyticAt_affCoord R.A (R.holo (h u0)) k ((R.A.chart k).map_source hs0')
      (by rw [hsym]; exact R.mem_U (h u0)) p (by rw [hsym]; exact hp)
  have hker := R.immersion (h u0) (not_mem_mcPts_top _) p hp k hs0'
  obtain ⟨G, hG, hGa⟩ := exists_analytic_retraction ha hker
  have hzp : ∀ k', zex u0 ⟨k', p k'⟩ ≠ 0 := fun k' => orbit_ne (horb u0 hu0) (hp k')
  have hb : AnalyticAt ℂ (fun u => affCoord p (zex u)) u0 := by
    rw [analyticAt_pi_iff]
    intro q
    exact (han q u0 hu0).div (han ⟨q.1, p q.1⟩ u0 hu0) (hzp q.1)
  have hG' : AnalyticAt ℂ G (affCoord p (zex u0)) := by
    have hab : affCoord p (R.lift (h u0) ((R.A.chart k).symm (R.A.chart k (h u0)))) = affCoord p (zex u0) := by
      rw [hsym]; exact affCoord_eq (horb u0 hu0) p
    rw [← hab]; exact hG
  refine (AnalyticAt.comp (g := G) (f := fun u => affCoord p (zex u)) hG' hb).congr ?_
  filter_upwards [hV.mem_nhds hu0,
    (hcont u0 hu0).eventually (((R.isOpen_U (h u0)).inter (R.A.chart k).open_source).mem_nhds ⟨R.mem_U (h u0), hs0'⟩),
    (((R.A.chart k).continuousAt hs0').tendsto.comp (hcont u0 hu0)).eventually hGa] with u hu hhu hGu
  simp only [Function.comp_apply] at hGu ⊢
  rw [← hGu, (R.A.chart k).left_inv hhu.2, affCoord_eq (hloc (h u0) u hu hhu.1) p]

end GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib
