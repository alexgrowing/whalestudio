import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsResolutionDegree
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsPullFSExtension
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.ResolutionPotentials
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.AnResBridge
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsProjFSMass
import ReciprocityTheory.AnalyticForms.PotentialTheory.Stokes
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.AnForm.M Filter Topology
open scoped ContDiff

noncomputable section

namespace ResolutionDegree

theorem hessC_congr {n : ℕ} {φ ψ : (Fin n → ℂ) → ℝ} {z : Fin n → ℂ} (h : φ =ᶠ[𝓝 z] ψ) :
    ReciprocityTheory.AnForm.hessC φ z = ReciprocityTheory.AnForm.hessC ψ z := by
  unfold ReciprocityTheory.AnForm.hessC
  rw [(h.fderiv (𝕜 := ℝ)).fderiv_eq]

theorem maDens_congr {n : ℕ} {φ ψ : Fin n → (Fin n → ℂ) → ℝ} {z : Fin n → ℂ} (h : ∀ i, φ i =ᶠ[𝓝 z] ψ i) :
    ReciprocityTheory.AnForm.maDens φ z = ReciprocityTheory.AnForm.maDens ψ z := by
  have hH : (fun k => ReciprocityTheory.AnForm.hessC (φ k) z) = fun k => ReciprocityTheory.AnForm.hessC (ψ k) z :=
    funext fun k => hessC_congr (h k)
  unfold ReciprocityTheory.AnForm.maDens
  rw [hH]

theorem mInt_congr_of_locDens {e : ℕ} {X : Type*} [TopologicalSpace X] (A : FinHolAtlas e X)
    {Φ Ψ : Fin e → LocPot X} (h : ∀ j, ∀ y ∈ (A.chart j).target, locDens A Φ j y = locDens A Ψ j y)
    (g : X → ℝ) : mInt A Φ g = mInt A Ψ g := by
  unfold mInt
  split_ifs with hP
  · unfold integralWith
    refine Finset.sum_congr rfl fun j _ => ?_
    refine MeasureTheory.setIntegral_congr_fun (A.chart j).open_target.measurableSet fun y hy => ?_
    simp only [h j y hy]
  · rfl

variable {D : ℕ} {Ω : Type} [Field Ω] [CharZero Ω] {κ : Type} [Fintype κ]

theorem smooth_logRatio_resPt (d : HSMDatum D Ω κ) {m₀ m₁ : ConeMetric ℂ (Ix κ)}
    (h₀ : IsSmoothMetric m₀) (h₁ : IsSmoothMetric m₁) :
    d.R.A.Smooth (fun y => logRatio m₀ m₁ (resPt d y)) := fun j => by
  refine contDiffOn_of_locally_contDiffOn fun y hy => ?_
  refine ⟨(d.R.A.chart j).target ∩ (d.R.A.chart j).symm ⁻¹' d.R.U ((d.R.A.chart j).symm y),
    (d.R.A.chart j).isOpen_inter_preimage_symm (d.R.isOpen_U _), ⟨hy.1, d.R.mem_U _⟩, ?_⟩
  have hsm : ContDiffOn ℝ ∞
      (fun y' => logRatio m₀ m₁ (d.R.lift ((d.R.A.chart j).symm y) ((d.R.A.chart j).symm y')))
      ((d.R.A.chart j).target ∩ (d.R.A.chart j).symm ⁻¹' d.R.U ((d.R.A.chart j).symm y)) :=
    (gbamix_smooth_logRatio h₀ h₁).comp (resLift_contDiffOn d _ j)
      fun y' hy' => gaamix_ne_zero_of_mcPts (d.R.mem _ _ hy'.2)
  refine (hsm.mono Set.inter_subset_right).congr fun y' hy' => ?_
  obtain ⟨c, hc, hcy⟩ := d.R.compat ((d.R.A.chart j).symm y') ((d.R.A.chart j).symm y)
    ((d.R.A.chart j).symm y') ⟨d.R.mem_U _, hy'.2.2⟩
  change logRatio m₀ m₁ (d.R.lift ((d.R.A.chart j).symm y') ((d.R.A.chart j).symm y')) = _
  rw [hcy, gbamix_logRatio_deg c _ hc]

theorem mInt_resPot_eq (d : HSMDatum D Ω κ) {m₀ m₁ : ConeMetric ℂ (Ix κ)} (g : d.R.X → ℝ) :
    mInt d.R.A (fun _ => resPot d m₁) g =
      mInt d.R.A (fun _ => resPot d m₀ + LocPot.ofFun (fun y => logRatio m₀ m₁ (resPt d y))) g := by
  refine mInt_congr_of_locDens _ (fun j y hy => ?_) g
  unfold locDens
  refine maDens_congr fun _ => ?_
  have hmem : (d.R.A.chart j).target ∩ (d.R.A.chart j).symm ⁻¹' d.R.U ((d.R.A.chart j).symm y) ∈ 𝓝 y :=
    ((d.R.A.chart j).isOpen_inter_preimage_symm (d.R.isOpen_U _)).mem_nhds ⟨hy, d.R.mem_U _⟩
  filter_upwards [hmem] with y' hy'
  obtain ⟨c, hc, hcy⟩ := d.R.compat ((d.R.A.chart j).symm y') ((d.R.A.chart j).symm y)
    ((d.R.A.chart j).symm y') ⟨d.R.mem_U _, hy'.2⟩
  have hz := gaamix_ne_zero_of_mcPts (d.R.mem ((d.R.A.chart j).symm y) _ hy'.2)
  have h₀ := m₀.pos _ hz
  have h₁ := m₁.pos _ hz
  change Real.log (m₁.ρ (d.R.lift ((d.R.A.chart j).symm y) ((d.R.A.chart j).symm y'))) =
    Real.log (m₀.ρ (d.R.lift ((d.R.A.chart j).symm y) ((d.R.A.chart j).symm y'))) +
      logRatio m₀ m₁ (d.R.lift ((d.R.A.chart j).symm y') ((d.R.A.chart j).symm y'))
  rw [hcy, gbamix_logRatio_deg c _ hc, logRatio, Real.log_div h₁.ne' h₀.ne']
  ring

theorem mass_eq (d : HSMDatum D Ω κ) {m₀ m₁ : ConeMetric ℂ (Ix κ)} (h₀ : IsSmoothMetric m₀)
    (h₁ : IsSmoothMetric m₁) :
    mInt d.R.A (fun _ => resPot d m₁) (fun _ => 1) = mInt d.R.A (fun _ => resPot d m₀) (fun _ => 1) := by
  rw [mInt_resPot_eq d (m₀ := m₀)]
  exact massIndep d.R.A (fun _ => resPot d m₀) (fun _ y => logRatio m₀ m₁ (resPt d y))
    (fun _ => isPotential_resPot d h₀) (fun _ => smooth_logRatio_resPt d h₀ h₁)

theorem mass_pullFS (hPM : ProjFSMass.Statement) (d : HSMDatum D Ω κ) {e : Fin (D + 1) → Ix κ}
    {m₀ : ConeMetric ℂ (Ix κ)} (hfr : IsProjFrame d.x e) (h₀ : IsSmoothMetric m₀) (hFS : IsPullFS d.x e m₀) :
    mInt d.R.A (fun _ => resPot d m₀) (fun _ => 1) = (projDeg d.x e : ℝ) := by
  obtain ⟨Ψ, hΨ, hmass⟩ := hPM D Ω κ d.x e m₀ hfr hFS
  let A : HermLine (GlobalTheory κ) := HermLine.ofWeight (fun _ => (1 : ℝ)) (fun _ _ _ => rfl)
  have hA : IsSmoothHerm A := contDiffOn_const
  have hlog : logNorm A 1 = fun _ => (1 : ℝ) := by
    funext z
    simp [A, logNorm, HermLine.ofWeight]
  have hsec : IsSectionOn (coordIdeal ℤ d.x) A 1 := by
    refine ⟨fun _ => 0, fun _ => rfl, ?_, ?_⟩
    · intro a ha k
      rw [support_one] at ha
      simp only [Finset.mem_singleton] at ha
      simp [ha]
    · exact (Ideal.ne_top_iff_one _).1 d.arith.2.1.1.ne_top
  have key := AnResBridge.bridge d.R Ψ (fun _ => HermLine.ofCone m₀) A 1 d.arith hΨ
    (fun _ => gbamix_smoothHerm_ofCone h₀) hA hsec
  rw [hlog] at key
  rw [← hmass]
  exact key.symm

end ResolutionDegree

theorem ResolutionDegree.proof (hPF : PullFSExtension.Statement) (hPM : ProjFSMass.Statement) :
    ResolutionDegree.Statement := by
  intro D Ω _ _ κ _ d e m hfr hm
  obtain ⟨m₀, h₀, -, -, hFS⟩ := hPF D Ω κ d.x e hfr
  rw [ResolutionDegree.mass_eq d h₀ hm]
  exact ResolutionDegree.mass_pullFS hPM d hfr h₀ hFS

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
