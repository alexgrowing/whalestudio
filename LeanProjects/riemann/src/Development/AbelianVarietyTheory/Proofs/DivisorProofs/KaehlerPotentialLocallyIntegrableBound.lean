import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousAndSmul
import Development.AbelianVarietyTheory.Definitions.Divisors.AnalyticOnNhdFinChartIff
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsClosedImmersionGenericPoint
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChartMatrixSmoothInvertible
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExponentialChartSmoothFormStatement
open CategoryTheory AlgebraicGeometry Filter Topology Set MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.CxPts GlobalTheory.ShFam GlobalTheory.ChernReg
open scoped ContDiff

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ChernReg.RhoSmooth

open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory.FinChart

open Matrix in

theorem mean_congr_cutoff {d : ℕ} (q f g : (Fin d → ℂ) → ℝ) (h : ∀ ξ, q ξ < 1 → f ξ = g ξ) :
    mean q f = mean q g := by
  unfold mean
  congr 1
  refine integral_congr_ae (Filter.Eventually.of_forall fun ξ => ?_)
  by_cases h0 : cutoff (q ξ) = 0
  · simp only [h0, mul_zero]
  · show f ξ * _ = g ξ * _
    rw [h ξ (cutoff_pos_iff.1 ((cutoff_nonneg _).lt_of_ne' h0))]

open Matrix in

theorem rho_cInfAt : ∀ (k : Type) [CommRing k] (Y : Scheme.{0}) (p : Y ⟶ Sp k) (σ : k →+* ℂ) (d : ℕ) [SmoothOfRelativeDimension d p] [CompactSpace (CxPts p σ)] (R : AnRead p σ d) (a : ChartForm p σ d) (E : ChartMap p σ d) (ψ : CxPts p σ → ℝ), IsKaehlerForm R a → IsExph a E → (∀ y, ∃ c : AlgChart p σ d, y ∈ c.e.source ∧ MeasureTheory.LocallyIntegrableOn (ψ ∘ c.finChart.symm) c.finChart.target MeasureTheory.volume) → ∃ δ : ℝ, 0 < δ ∧ ∀ t : ℝ, 0 < t → t < δ → ∀ y, CxPts.CInfAt (fun z => rho a E ψ z t) y := by
  intro k _ Y p σ d _ _ R a E ψ ha hE hψ
  have key : ∀ y, ∃ W : Set (CxPts p σ), IsOpen W ∧ y ∈ W ∧
      ∀ᶠ t in 𝓝[>] (0 : ℝ), ∀ y' ∈ W, CxPts.CInfAt (fun z => rho a E ψ z t) y' := by
    intro y
    obtain ⟨c, hy, hloc⟩ := hψ y
    let N : Set ((Fin d → ℂ) × (Fin d → ℂ)) :=
      {q | q.1 ∈ c.finChart.target ∧ E c (c.finChart.symm q.1) q.2 ∈ c.e.source}
    let G : (Fin d → ℂ) × (Fin d → ℂ) → Fin d → ℂ := fun q => c.finChart (E c (c.finChart.symm q.1) q.2)
    let q : (Fin d → ℂ) → (Fin d → ℂ) → ℝ := fun z ξ => a c (c.finChart.symm z) ξ
    let L : (Fin d → ℂ) × (Fin d → ℂ) →L[ℝ] V d × V d :=
      (toV d).toContinuousLinearMap.prodMap (toV d).toContinuousLinearMap
    have hU : IsOpen c.finChart.target := c.finChart.open_target
    have hz₀ : c.finChart y ∈ c.finChart.target := c.finChart.map_source hy
    have hFy : c.finChart.symm (c.finChart y) = y := c.finChart.left_inv hy
    have hN : IsOpen N := by
      have hc : ContinuousOn (fun q : (Fin d → ℂ) × (Fin d → ℂ) => E c (c.finChart.symm q.1) q.2)
          (c.finChart.target ×ˢ univ) :=
        (hE.cont c).comp L.continuous.continuousOn fun q hq => ⟨hq.1, mem_univ _⟩
      have := hc.isOpen_inter_preimage (hU.prod isOpen_univ) c.e.open_source
      convert this using 1
      exact Set.ext fun q => ⟨fun h => ⟨⟨h.1, trivial⟩, h.2⟩, fun h => ⟨h.1.1, h.2⟩⟩
    have h0N : (c.finChart y, (0 : Fin d → ℂ)) ∈ N := ⟨hz₀, by
      show E c (c.finChart.symm (c.finChart y)) 0 ∈ c.e.source
      rw [hFy, hE.zero c y hy]; exact hy⟩
    have hGs : ContDiffOn ℝ ∞ G N :=
      (toV d).symm.contDiff.comp_contDiffOn ((hE.smooth c c).comp L.contDiff.contDiffOn fun q hq => ⟨hq.1, hq.2⟩)
    have hG0 : G (c.finChart y, 0) = c.finChart y := by
      show c.finChart (E c (c.finChart.symm (c.finChart y)) 0) = c.finChart y
      rw [hFy, hE.zero c y hy]
    have hder : HasFDerivAt (fun ξ => G (c.finChart y, ξ)) (ContinuousLinearMap.id ℝ (Fin d → ℂ)) 0 := by
      have hd : DifferentiableAt ℝ (fun ξ => G (c.finChart y, ξ)) 0 :=
        ((hGs.contDiffAt (hN.mem_nhds h0N)).differentiableAt (by simp)).comp (0 : Fin d → ℂ)
          (differentiableAt_const _ |>.prodMk differentiableAt_id)
      convert hd.hasFDerivAt using 1
      refine (ContinuousLinearMap.ext fun ξ => ?_).symm
      have h1 := hd.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) ((hasDerivAt_id (0 : ℝ)).smul_const ξ) (by simp)
      have h2 := (toV d).hasFDerivAt.comp_hasDerivAt (0 : ℝ) h1
      have hj := hE.jets c y hy (toV d ξ) 1
      rw [iteratedDeriv_one, jet_one] at hj
      have e : (fun t : ℝ => c.e (E c y (t • (toV d ξ).ofLp))) =
          (toV d) ∘ (fun ξ => G (c.finChart y, ξ)) ∘ (fun t : ℝ => id t • ξ) := by
        funext t
        show _ = toV d (c.finChart (E c (c.finChart.symm (c.finChart y)) (t • ξ)))
        rw [hFy]
        rfl
      rw [e, h2.deriv] at hj
      simpa using (toV d).injective hj
    obtain ⟨hM, -, hform⟩ := MatSmooth.matIn_smooth_unit_form k Y p σ d R a ha c
    have hq : ContDiffOn ℝ ∞ (fun p : (Fin d → ℂ) × (Fin d → ℂ) => q p.1 p.2) (c.finChart.target ×ˢ univ) := by
      have hexpr : ContDiffOn ℝ ∞ (fun p : (Fin d → ℂ) × (Fin d → ℂ) =>
          ((p.2 ᵥ* matIn a c (toV d p.1)) ⬝ᵥ star p.2).re) (c.finChart.target ×ˢ univ) := by
        simp only [Matrix.vecMul, dotProduct, Pi.star_apply]
        refine Complex.reCLM.contDiff.comp_contDiffOn (ContDiffOn.sum fun i _ => (ContDiffOn.sum fun j _ => ?_).mul ?_)
        · exact ((contDiff_apply ℝ ℂ j).comp contDiff_snd).contDiffOn.mul
            ((hM j i).comp ((toV d).contDiff.comp contDiff_fst).contDiffOn fun p hp => hp.1)
        · exact (Complex.conjCLE.contDiff.comp ((contDiff_apply ℝ ℂ i).comp contDiff_snd)).contDiffOn
      refine hexpr.congr fun p hp => ?_
      have := hform (toV d p.1) hp.1 (toV d p.2)
      rw [← Complex.ofReal_re (q p.1 p.2)]
      exact congrArg Complex.re this
    have hhom : ∀ z ∈ c.finChart.target, ∀ (t : ℝ) ξ, q z (t • ξ) = t ^ 2 * q z ξ := fun z hz =>
      (continuous_and_smul ha (c.finChart.map_target hz)).2
    have hpos : ∀ z ∈ c.finChart.target, ∀ ξ, ξ ≠ 0 → 0 < q z ξ := fun z hz ξ hξ =>
      ha.2 c _ (c.finChart.map_target hz) ξ hξ
    obtain ⟨δ, hδ, U', hU'o, hzU', hU'U, hmem, hsm⟩ :=
      GlobalTheory.T.exponential_chart_smooth_form d c.finChart.target N G q (c.finChart y) hU hz₀ hN h0N hGs hG0 hder hq hhom hpos
    refine ⟨c.e.source ∩ c.finChart ⁻¹' U', c.finChart.isOpen_inter_preimage hU'o, ⟨hy, hzU'⟩, ?_⟩
    filter_upwards [Ioo_mem_nhdsGT hδ] with t ht y' hy'
    refine cInfAt_of_chart (c.finChart.isOpen_inter_preimage hU'o) c ?_ hy'.1 hy'
    refine (c.contDiffOn_finChart_iff ∞ _ _).1 (((hsm _ hloc t ht.1 ht.2).mono ?_).congr ?_)
    · intro z hz
      have := hz.2.2
      rwa [mem_preimage, c.finChart.right_inv hz.1] at this
    · intro z hz
      have hzU : z ∈ U' := by
        have := hz.2.2
        rwa [mem_preimage, c.finChart.right_inv hz.1] at this
      show rho a E ψ (c.finChart.symm z) t = _
      rw [rho_eq ha hE ψ hz.2.1 t, rhoIn]
      refine mean_congr_cutoff _ _ _ fun ξ hξ => ?_
      have hm := (hmem z hzU t ht.1 ht.2 ξ hξ).2
      show _ = ψ (c.finChart.symm (c.finChart (E c (c.finChart.symm z) (t • ξ))))
      rw [c.finChart.left_inv hm]
  choose W hWo hyW hev using key
  obtain ⟨s, -, hs⟩ := (isCompact_univ (X := CxPts p σ)).elim_nhds_subcover W
    fun y _ => (hWo y).mem_nhds (hyW y)
  have hall : ∀ᶠ t in 𝓝[>] (0 : ℝ), ∀ y ∈ s, ∀ y' ∈ W y, CxPts.CInfAt (fun z => rho a E ψ z t) y' :=
    (eventually_all_finset s).2 fun y _ => hev y
  obtain ⟨δ, hδ, hδs⟩ := (nhdsGT_basis_of_exists_gt ⟨1, one_pos⟩).eventually_iff.1 hall
  refine ⟨δ, hδ, fun t ht0 htδ y => ?_⟩
  obtain ⟨i, hi, hyi⟩ := mem_iUnion₂.1 (hs (mem_univ y))
  exact hδs ⟨ht0, htδ⟩ i hi y hyi

end GlobalTheory.ChernReg.RhoSmooth
