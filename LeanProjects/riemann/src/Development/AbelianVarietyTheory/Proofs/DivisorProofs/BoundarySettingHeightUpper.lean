import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SecondChernDensity
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothOnNhdOffBoundary
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory Matrix NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Points GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.HermFrame GlobalTheory.ArInt GlobalTheory.CovTest GlobalTheory.VdmRec GlobalTheory.ArchLim
open GlobalTheory.MixDens (part IsDens chernMat emb)
open GlobalTheory.FlagFibre (Low uni)
open ReciprocityTheory.L2DbarEstimates (V cHess bas)
open ReciprocityTheory.AnForm.M (LocPot FinHolAtlas IsPotential IsSection)
open GlobalTheory.IndefiniteRowSideFullHecke.BoundaryPolynomialFunctions (IsProjective IsIrreducibleAnalytic IsIrreducibleComponent regularLocus regIntegral normSec absLogNorm boundary rFun poincarePot IsBoundarySetting)
open Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Hor GlobalTheory.Mean4O
open scoped ContDiff ComplexOrder ENNReal Classical

namespace GlobalTheory.ArchLim

theorem cHess_poincarePot_up_base_eq : ∀ (D : D7) (A : Amb D) (N j : ℕ) (S : Sig A N j) (κ : Lv A) (s : FinalTheorems S κ) (σ : κ.c.F →+* ℂ) [CompactSpace (CxPts (genStr s.T.Z) σ)] (m : ℕ) (α : LocPot (CxPts (genStr s.T.Z) σ)) (Λ : Fin m → LocPot (CxPts (genStr s.T.Z) σ)) (sg : Fin m → CxPts (genStr s.T.Z) σ → CxPts (genStr s.T.Z) σ → ℂ) (t : ℝ), IsBoundarySetting (manifold s.T.Z σ).finAtlas α Λ sg t → ∀ (Y : Scheme.{0}) (q : Y ⟶ Sp (𝓞 κ.c.F)) (jm : Y ⟶ s.T.Z.X) (hq : jm ≫ s.T.Z.s = q) (n : ℕ) (ch : AlgChart q (σ.comp (algebraMap (𝓞 κ.c.F) κ.c.F)) n), (∀ (W : (gen s.T.Z).Opens) (f : Γ(gen s.T.Z, W)), DifferentiableOn ℂ (ev (genStr s.T.Z) σ W f ∘ up jm hq σ ∘ ch.e.symm) (ch.e.target ∩ ch.e.symm ⁻¹' (up jm hq σ ⁻¹' ptsIn (genStr s.T.Z) σ W))) → (∀ (x : CxPts (genStr s.T.Z) σ) (y : CxPts q (σ.comp (algebraMap (𝓞 κ.c.F) κ.c.F))), y ∈ ch.e.source → up jm hq σ y ∉ boundary sg → up jm hq σ y ∈ α.U x → ∃ O : Set (V n), IsOpen O ∧ ch.e y ∈ O ∧ O ⊆ ch.e.target ∧ ContDiffOn ℝ ∞ (fun v => (poincarePot α Λ sg t).φ x (up jm hq σ (ch.e.symm v))) O) → ∀ (x x' : CxPts (genStr s.T.Z) σ) (y : CxPts q (σ.comp (algebraMap (𝓞 κ.c.F) κ.c.F))), y ∈ ch.e.source → up jm hq σ y ∉ boundary sg → up jm hq σ y ∈ α.U x → up jm hq σ y ∈ α.U x' → cHess n (fun v => ((poincarePot α Λ sg t).φ x (up jm hq σ (ch.e.symm v)) : ℂ)) (ch.e y) = cHess n (fun v => ((poincarePot α Λ sg t).φ x' (up jm hq σ (ch.e.symm v)) : ℂ)) (ch.e y) := by
  intro D A N j S κ s σ _ m α Λ sg t hB Y q jm hq n ch hholo hsmooth x x' y hy hyb hx hx'
  have hA := (manifold s.T.Z σ).isAlgAtlas_finAtlas
  obtain ⟨W, hW, hyW, G, hG, hdiff⟩ := hB.1.2 x x' (up jm hq σ y) ⟨hx, hx'⟩
  obtain ⟨jj, hjj⟩ := (manifold s.T.Z σ).finAtlas.cover (up jm hq σ y)
  have hce : (manifold s.T.Z σ).finAtlas.chart jj = (hA.anRead.chart jj).finChart := hA.chart_eq jj
  set c := hA.anRead.chart jj with hc_def
  rw [hce] at hjj
  have hGc : DifferentiableOn ℂ (G ∘ c.e.symm) (c.e.target ∩ c.e.symm ⁻¹' W) := by
    have h1 := hG jj
    rw [hce] at h1
    exact (c.analyticOnNhd_finChart_iff hW G).1 h1
  have hcu : Continuous (up jm hq σ) := continuous_up jm hq σ
  set O : Set (V n) := ch.e.target ∩ ch.e.symm ⁻¹' (up jm hq σ ⁻¹' (c.e.source ∩ W ∩ α.U x ∩ α.U x'))
    with hOdef
  have hO : IsOpen O := ch.e.isOpen_inter_preimage_symm
    ((((c.e.open_source.inter hW).inter (α.isOpen_U x)).inter (α.isOpen_U x')).preimage hcu)
  have hyO : ch.e y ∈ O := by
    refine ⟨ch.e.map_source hy, ?_⟩
    simp only [Set.mem_preimage, ch.e.left_inv hy]
    exact ⟨⟨⟨hjj, hyW⟩, hx⟩, hx'⟩
  have hτ : DifferentiableOn ℂ (c.e ∘ up jm hq σ ∘ ch.e.symm) O := by
    refine differentiableOn_euclidean.2 fun a => ?_
    refine ((hholo c.U (c.x a)).mono fun v hv => ⟨hv.1, c.source_subset hv.2.1.1.1⟩).congr
      fun v hv => ?_
    exact c.apply_eq _ hv.2.1.1.1 a
  have hgd : DifferentiableOn ℂ (fun v => G (up jm hq σ (ch.e.symm v))) O := by
    refine (hGc.comp hτ fun v hv => ⟨c.e.map_source hv.2.1.1.1, ?_⟩).congr fun v hv => ?_
    · show c.e.symm (c.e (up jm hq σ (ch.e.symm v))) ∈ W
      rw [c.e.left_inv hv.2.1.1.1]
      exact hv.2.1.1.2
    · show G (up jm hq σ (ch.e.symm v)) = G (c.e.symm (c.e (up jm hq σ (ch.e.symm v))))
      rw [c.e.left_inv hv.2.1.1.1]
  have hhd : DifferentiableOn ℂ (fun v => Complex.exp (G (up jm hq σ (ch.e.symm v)))) O := hgd.cexp
  have hh0 : ∀ v ∈ O, Complex.exp (G (up jm hq σ (ch.e.symm v))) ≠ 0 := fun v _ => Complex.exp_ne_zero _
  have hlog : ∀ v, Real.log (‖Complex.exp (G (up jm hq σ (ch.e.symm v)))‖ ^ 2) =
      2 * (G (up jm hq σ (ch.e.symm v))).re := by
    intro v
    rw [Complex.norm_exp, Real.log_pow, Real.log_exp]
    push_cast
    ring
  have hq' : ContDiffOn ℝ ∞ (fun v => Real.log (‖Complex.exp (G (up jm hq σ (ch.e.symm v)))‖ ^ 2)) O := by
    simp only [hlog]
    exact contDiffOn_const.mul (Complex.reCLM.contDiff.comp_contDiffOn
      ((((GlobalTheory.SCV.analyticOnNhd_iff_differentiableOn hO).2 hgd).contDiffOn
        hO.uniqueDiffOn).restrict_scalars ℝ))
  obtain ⟨O', hO', hyO', -, hp⟩ := hsmooth x' y hy hyb hx'
  have e := ReciprocityTheory.L2DbarEstimates.I.MongeAmpereIntegrability.cHess_add_smul (hO.inter hO') (hp.mono Set.inter_subset_right)
    (hq'.mono Set.inter_subset_left) (1 / 2) ⟨hyO, hyO'⟩
  have e₀ : cHess n (fun v => ((Real.log (‖Complex.exp (G (up jm hq σ (ch.e.symm v)))‖ ^ 2) : ℝ) : ℂ))
      (ch.e y) = 0 := by
    ext a b
    exact ReciprocityTheory.L2DbarEstimates.Y.cmpa_hess_log hO hyO hhd hh0 a b
  rw [e₀, smul_zero, add_zero] at e
  refine Eq.trans (ReciprocityTheory.L2DbarEstimates.Y.cmpb_cHess_congr ?_) e
  filter_upwards [hO.mem_nhds hyO] with v hv
  have hd := hdiff (up jm hq σ (ch.e.symm v)) ⟨⟨hv.2.1.1.2, hv.2.1.2⟩, hv.2.2⟩
  rw [hlog]
  congr 1
  change α.φ x _ + GlobalTheory.IndefiniteRowSideFullHecke.BoundaryPolynomialFunctions.pFun Λ sg t _ / 2 =
    α.φ x' _ + GlobalTheory.IndefiniteRowSideFullHecke.BoundaryPolynomialFunctions.pFun Λ sg t _ / 2 + 1 / 2 * (2 * _)
  linarith

end GlobalTheory.ArchLim
