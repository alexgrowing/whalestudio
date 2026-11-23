import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsIsHodgeFrameIff
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UniformizedFamilyChartIndex
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PeriodFamilyChartDomainStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFramedComplexPointOfEigenFrameOffBoundaryStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PeriodFamilyChartHolomorphicStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RiemannFormFramePointStatement
open AlgebraicGeometry CategoryTheory Limits NumberField Matrix
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory GlobalTheory.CxPts GlobalTheory.Toroidal GlobalTheory.LieMet GlobalTheory.GradedNorm GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.ShFam GlobalTheory.ShFam.Pad
open GlobalTheory.ArcQ
open scoped ContDiff

set_option autoImplicit false

theorem GlobalTheory.ShFam.ToroidalCompactificationData.hodge_gram_smooth_near : ∀ (D : D7) (A : Amb D) (N j : ℕ) (S : Sig A N j) (κ : Lv A) (s : FinalTheorems S κ) (x : ToroidalCompactificationData s) (σ : κ.c.F →+* ℂ), Formalism.L2.PjFree.GoodEmb κ.c σ → ∀ (V : (gen s.T.Z).affineOpens) (φ : κ.c.F →+* Γ(gen s.T.Z, V.1)) (F : EigFrame s.T.Z φ (LogKS.chart V ≫ genι s.T.Z)) (τ : D.host.E →+* ℂ) (a b : Fin (S.Dw.mult τ)), LogKS.chart V ≫ genStr s.T.Z = spMap φ → ∀ y₀ : CxPts (genStr s.T.Z) σ, ¬ LiesIn y₀ (genBd s.T.Z) → y₀ ∈ ptsIn (genStr s.T.Z) σ V.1 → ∃ (T : Set (CxPts (genStr s.T.Z) σ)) (g : CxPts (genStr s.T.Z) σ → ℂ), IsOpen T ∧ y₀ ∈ T ∧ (manifold s.T.Z σ).SmoothOn T (fun y => (g y).re) ∧ (manifold s.T.Z σ).SmoothOn T (fun y => (g y).im) ∧ ∀ y ∈ T, ∀ (hy : y ∈ ptsIn (genStr s.T.Z) σ V.1) (f : EigFrame s.T.Z σ (y.1 ≫ genι s.T.Z)), F.IsMap (evHom hy) f → (x.hodge σ).gram y f τ a b = g y := by
  intro D A N j S κ s x σ hσ V φ F τ a b hstr y₀ hbd hV
  obtain ⟨ch, hch⟩ := AlgChart.exists_mem_source (p := genStr s.T.Z) (σ := σ) (D := S.Dw.dim) y₀
  obtain ⟨W⟩ := nonempty_unfWit_of_isUnf _ _ _ _ _ _ σ _ _ (s.unf σ hσ).1
  obtain ⟨f₀, -⟩ := (FinalTheorems.exists_isHodgeFrame_iff (s := s) (y := y₀)).2 hbd
  obtain ⟨q₀, hq₀, -⟩ := GlobalTheory.T.exists_framedComplexPoint_of_eigenFrame_off_boundary _ _ _ _ _ _ _ _ s.T.Z σ y₀ hbd f₀
  obtain ⟨i, B, P, hB, hb₀, hBt, hPer, hPhol, hPu⟩ :=
    GlobalTheory.ShFam.chart_lift_periods _ _ _ _ _ _ _ _ s.T.Z σ S.Dw.dim W.g _ W.F ch q₀ (hq₀ ▸ hch)
  rw [hq₀] at hb₀
  obtain ⟨Hm, hHm, hHs⟩ := GlobalTheory.T.period_family_chart_domain _ _ _ _ _ _ σ W.g _ W.F i S.Dw.dim B P hB hPer hPhol
  have hmono : Mono (genι s.T.Z) := by
    have : Epi (CommRingCat.ofHom (algebraMap (𝓞 κ.c.F) κ.c.F)) := IsLocalization.epi (nonZeroDivisors (𝓞 κ.c.F)) κ.c.F
    have : Mono (spMap (algebraMap (𝓞 κ.c.F) κ.c.F)) := Scheme.Spec.map_mono (CommRingCat.ofHom _).op
    infer_instance
  obtain ⟨z, hz, hzl⟩ := GlobalTheory.T.period_family_chart_holomorphic _ _ _ _ _ _ _ _ s.T.Z σ S.Dw.dim W.g _ W.F ch i B P hB hBt hPer hPhol hPu hmono V φ F hstr
  set B' : Set (ReciprocityTheory.L2DbarEstimates.V S.Dw.dim) := {c ∈ B | ch.e.symm c ∈ ptsIn (genStr s.T.Z) σ V.1 ∧
    ¬ LiesIn (ch.e.symm c) (genBd s.T.Z)} with hB'
  have hB'o : IsOpen B' := by
    have h1 := ch.e.continuousOn_symm.isOpen_inter_preimage ch.e.open_target
      ((isOpen_ptsIn (p := genStr s.T.Z) (σ := σ) V.1).inter (isOpen_not_liesIn (p := genStr s.T.Z) (σ := σ) (genBd s.T.Z)))
    have e : B' = B ∩ (ch.e.target ∩ ch.e.symm ⁻¹' (ptsIn (genStr s.T.Z) σ V.1 ∩ {y | ¬ LiesIn y (genBd s.T.Z)})) := by
      ext c
      constructor
      · rintro ⟨h1, h2, h3⟩
        exact ⟨h1, hBt h1, h2, h3⟩
      · rintro ⟨h1, -, h2, h3⟩
        exact ⟨h1, h2, h3⟩
    rw [e]
    exact hB.inter h1
  have hz' : ∀ τ k p, ContDiffOn ℝ ∞ (fun c => z c τ k p) B' := fun τ k p =>
    GlobalTheory.ChartGlue.contDiffOn_real hB'o ((differentiableOn_pi.1 (hz τ k)) p)
  let G : ReciprocityTheory.L2DbarEstimates.V S.Dw.dim → ℂ := fun c => (Real.pi : ℂ) * hermForm (Hm c) (z c τ b) (z c τ a)
  have hG : ContDiffOn ℝ ∞ G B' := by
    have hc : ∀ p, ContDiffOn ℝ ∞ (fun c => star (z c τ a p)) B' := fun p =>
      Complex.conjCLE.contDiff.comp_contDiffOn (hz' τ a p)
    have e : G = fun c => (Real.pi : ℂ) * ∑ p, z c τ b p * ∑ q, Hm c p q * star (z c τ a q) := by
      funext c
      simp only [G, hermForm, dotProduct, Matrix.mulVec, Pi.star_apply]
    rw [e]
    exact contDiffOn_const.mul (ContDiffOn.sum fun p _ => (hz' τ b p).mul
      (ContDiffOn.sum fun q _ => ((hHs p q).mono fun c hc => hc.1).mul (hc q)))
  refine ⟨ch.e.source ∩ ch.e ⁻¹' B', fun y => G (ch.e y), ch.e.isOpen_inter_preimage hB'o,
    ⟨hch, hb₀, by rw [ch.e.left_inv hch]; exact hV, by rw [ch.e.left_inv hch]; exact hbd⟩, ?_, ?_, ?_⟩
  · intro c'
    have ht : ContDiffOn ℝ ∞ (ch.e ∘ c'.e.symm) (c'.e.target ∩ c'.e.symm ⁻¹' ch.e.source) :=
      (contDiffOn_piLp 2).2 fun a => GlobalTheory.ChartGlue.contDiffOn_real (GlobalTheory.ChartGlue.isOpen_over c'.e ch.e.open_source)
        (differentiableOn_euclidean.1 (AlgChart.holo_trans c' ch) a)
    exact (Complex.reCLM.contDiff.comp_contDiffOn hG).comp (ht.mono fun v hv => ⟨hv.1, hv.2.1⟩) fun v hv => hv.2.2
  · intro c'
    have ht : ContDiffOn ℝ ∞ (ch.e ∘ c'.e.symm) (c'.e.target ∩ c'.e.symm ⁻¹' ch.e.source) :=
      (contDiffOn_piLp 2).2 fun a => GlobalTheory.ChartGlue.contDiffOn_real (GlobalTheory.ChartGlue.isOpen_over c'.e ch.e.open_source)
        (differentiableOn_euclidean.1 (AlgChart.holo_trans c' ch) a)
    exact (Complex.imCLM.contDiff.comp_contDiffOn hG).comp (ht.mono fun v hv => ⟨hv.1, hv.2.1⟩) fun v hv => hv.2.2
  · rintro y ⟨hys, hyB⟩ hy f hf
    show _ = G (ch.e y)
    obtain ⟨c0, hc0, rfl⟩ : ∃ c0 ∈ B', ch.e.symm c0 = y := ⟨ch.e y, hyB, ch.e.left_inv hys⟩
    rw [ch.e.right_inv (hBt hc0.1)]
    obtain ⟨q, hq, hw⟩ := GlobalTheory.T.exists_framedComplexPoint_of_eigenFrame_off_boundary _ _ _ _ _ _ _ _ s.T.Z σ _ hc0.2.2 f
    have hd := hzl c0 hc0.1 hy f hf q hq hw
    have hu := hPu c0 hc0.1 q hq.symm
    exact GlobalTheory.T.riemann_form_frame_point D A N j S κ s x σ hσ W i (P c0) (hPer c0 hc0.1) (Hm c0) (hHm c0 hc0.1) q (z c0) ⟨hu.symm, hd⟩ _ hq f hw τ a b
