import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PStokesLimitTTop
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterNamed
import Development.AutomorphicSpectrum.Proofs.MetricProofs.LogRatio
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PVertFactorSmooth
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PVertFactorPos
import Development.AutomorphicSpectrum.Proofs.MetricProofs.HoloOnDivCongr

noncomputable section

open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar.Giv.Mix

namespace GlobalTheory.CompanionTheory.Ar.Giv.Mix

theorem log_vertFactor_eq_re_holo : ∀ (II : IntersectionSystem) (Ψ : Type) [Fintype Ψ] (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (E : Ψ → Type) [∀ τ, AddCommGroup (E τ)] [∀ τ, Module Ω (E τ)] (D : ComponentData II Ψ K ι Ω E) (p : ℕ) (M : XModel D) (U : Set M.Xc) (s : M.Xc → (Σ k, ι k) → ℂ), p ∈ D.S → IsOpen U → (∀ y ∈ U, s y ∈ mcPts (mCoordIdeal D.y)) → (∀ q, M.atlas.HoloOn U fun y => s y q) → ∀ y₀ ∈ U, ∃ V : Set M.Xc, IsOpen V ∧ y₀ ∈ V ∧ V ⊆ U ∧ ∃ G : M.Xc → ℂ, M.atlas.HoloOn V G ∧ ∀ y ∈ V, Real.log (D.vertFactor p (s y)) = (G y).re := by
  intro II Ψ _ K _ ι _ Ω _ _ E _ _ D p M U s hp hU hs hhol y₀ hy₀
  obtain ⟨dG, dH, G, H, hG, hH, hdeg, hrel, hHz⟩ := VertFactorSmooth.exists_forms D hp (hs y₀ hy₀)
  have hpos := VertFactorPos.proof II Ψ K ι Ω E D p hp (s y₀) (hs y₀ hy₀)
  rw [VertFactorSmooth.vertFactor_eq D hp (hs y₀ hy₀) hG hH hdeg hrel hHz] at hpos
  have hGz : eval (s y₀) (map (Int.castRingHom ℂ) G) ≠ 0 := by
    intro h
    rw [h, zero_div, norm_zero] at hpos
    exact lt_irrefl _ hpos
  set A := M.atlas with hA
  have HG := GlobalTheory.CompanionTheory.Ar.PB.StepW.ValHolo.holoOn_eval A hhol G
  have HH := GlobalTheory.CompanionTheory.Ar.PB.StepW.ValHolo.holoOn_eval A hhol H
  set Gf : M.Xc → ℂ := fun y => eval (s y) (map (Int.castRingHom ℂ) G) with hGf
  set Hf : M.Xc → ℂ := fun y => eval (s y) (map (Int.castRingHom ℂ) H) with hHf
  set W₁ : Set M.Xc := U ∩ {y | Hf y ≠ 0} with hW₁
  have hW₁o : IsOpen W₁ := GlobalTheory.CompanionTheory.Ar.PB.StepW.ValHolo.isOpen_inter_ne A hU HH
  have hsub : W₁ ⊆ U := Set.inter_subset_left
  have mono : ∀ {f : M.Xc → ℂ} {S T : Set M.Xc}, T ⊆ S → A.HoloOn S f → A.HoloOn T f := by
    intro f S T hTS hf j
    exact (hf j).mono (Set.inter_subset_inter_right _ (Set.preimage_mono hTS))
  set g : M.Xc → ℂ := fun y => Gf y / Hf y with hg
  have Hg : A.HoloOn W₁ g :=
    GlobalTheory.CompanionTheory.Ar.PB.StepW.ValHolo.holoOn_div_congr A hW₁o (mono hsub HG) (mono hsub HH)
      (fun y hy => hy.2) fun y _ => rfl
  set c : ℂ := g y₀ with hc
  have hc0 : c ≠ 0 := div_ne_zero hGz hHz
  set V : Set M.Xc := W₁ ∩ {y | g y / c ∈ Complex.slitPlane} with hV
  have hVo : IsOpen V := by
    rw [isOpen_iff_mem_nhds]
    rintro y ⟨hy, hsl⟩
    have hcont : ContinuousAt (fun y => g y / c) y :=
      (GlobalTheory.CompanionTheory.Ar.PB.StepW.ValHolo.continuousAt_of_holoOn A Hg hy).div_const c
    filter_upwards [hW₁o.mem_nhds hy, hcont (Complex.isOpen_slitPlane.mem_nhds hsl)] with u h1 h2
    exact ⟨h1, h2⟩
  have hy₀V : y₀ ∈ V := by
    refine ⟨⟨hy₀, hHz⟩, ?_⟩
    show g y₀ / c ∈ Complex.slitPlane
    rw [← hc, div_self hc0]
    exact Complex.one_mem_slitPlane
  refine ⟨V, hVo, hy₀V, fun y hy => hsub hy.1, fun y => Complex.log (g y / c) + (Real.log ‖c‖ : ℂ), ?_, ?_⟩
  · intro j u hu
    have hgu : AnalyticAt ℂ (g ∘ (A.chart j).symm) u :=
      Hg j u ⟨hu.1, hu.2.1⟩
    have hsl : (g ∘ (A.chart j).symm) u / c ∈ Complex.slitPlane := hu.2.2
    have h1 : AnalyticAt ℂ (fun v => (g ∘ (A.chart j).symm) v / c) u := hgu.div analyticAt_const hc0
    have h2 := (h1.clog hsl).add (analyticAt_const (v := ((Real.log ‖c‖ : ℝ) : ℂ)))
    exact h2
  · rintro y ⟨hy, hsl⟩
    have hsl' : g y / c ∈ Complex.slitPlane := hsl
    have hgy : g y ≠ 0 := by
      intro h
      rw [h, zero_div] at hsl'
      exact Complex.slitPlane_ne_zero hsl' rfl
    rw [VertFactorSmooth.vertFactor_eq D hp (hs y (hsub hy)) hG hH hdeg hrel hy.2]
    show Real.log ‖g y‖ = (Complex.log (g y / c) + ((Real.log ‖c‖ : ℝ) : ℂ)).re
    rw [Complex.add_re, Complex.ofReal_re, Complex.log_re, norm_div (g y) c,
      Real.log_div (norm_ne_zero_iff.2 hgy) (norm_ne_zero_iff.2 hc0)]
    ring

end GlobalTheory.CompanionTheory.Ar.Giv.Mix
