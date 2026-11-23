import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PairBaseIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GradedMetricPullbackIsometric
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InducedMetricOfIsometric
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagGenericFibreIntegral
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagBundleExistsArithmeticVarietyAltBis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DimensionOfVarietyComponentStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PairCoverHodgeComparisonStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PairCoverHodgeMetricStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PairCoverHodgeDegreeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PairCoverHodgeHeightStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagPullbackGenericFibreStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrameAssignmentMorphismStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigenMetricComparisonNormalStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PairCoverCompatibilityStatement
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open Formalism.BasicNotions.DV Formalism.MainNotions.WeightThresholdDefs GlobalTheory.FlagAr GlobalTheory.ShFam.Pad GlobalTheory.VB GlobalTheory.ShFam GlobalTheory.TrueGeo Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ArLieBase
open GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.ProjVar GlobalTheory.TwoLat GlobalTheory.FlagCov
open scoped Classical

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.PairCov

theorem pairCover : GlobalTheory.CovTop.Hypotheses2 → GlobalTheory.CovHt.HypothesesH → GlobalTheory.Published.RegularAlteration → ∀ (D : D7) (O : Setup D),
    O.Core → ∀ R : ℝ, 2 ≤ R → ∀ (c : O.s.Comp) (B : Scheme.{0}) [IsIntegral B] (q : B ⟶ Sp (𝓞 D.what₂.LL))
    (E E' : (D.host.E →+* ℂ) → B.Modules) (h : ∀ σ, VMetric q (E σ) (O.S.Dw.mult σ))
    (h' : ∀ σ, VMetric q (E' σ) (O.S.Dw.mult σ)) (H : ∀ σ, (h σ).IsCInf) (H' : ∀ σ, (h' σ).IsCInf)
    (u : ∀ σ, E σ ⟶ E' σ), IsArithVar q (dimGr D.what₂.Tau O.N O.j) → ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme B →
    (∀ σ, IsoHom (h σ) (h' σ) (u σ)) → PairBase O R c q E E' h h' u → PairCover O R c q E E' H H' u := by
  intro p2 pH pRA D O hO R hR c B _ q E E' h h' H H' u hq hn hu hPB
  obtain ⟨Bg, jB, πB, t, t', G, hW⟩ := (pairBase_iff O R c q E E' h h' u).1 hPB
  obtain ⟨pbB, -, -, frE, frE', hmat, latE, latE', -, metE, metE'⟩ := id hW
  obtain ⟨Y, iY, π, fl, hfb, arY, nY⟩ := GlobalTheory.T.exists_normal_isFlagBundle_isArithVar (𝓞 D.what₂.LL) B q _ hq hn (D.host.E →+* ℂ) E O.S.Dw.mult
    (fun σ => (h σ).isVB)
  have arY' : IsArithVar (π ≫ q) (O.var c).dim := by
    rw [← GlobalTheory.T.dimension_of_variety_component D O hO c]
    exact arY
  obtain ⟨Gs, jY, s, pbY, iG⟩ : ∃ (Gs : Scheme.{0}) (jY : Gs ⟶ Y) (s : Gs ⟶ Sp D.what₂.LL),
      IsPullback jY s (π ≫ q) (spMap (algebraMap (𝓞 D.what₂.LL) D.what₂.LL)) ∧ IsIntegral Gs :=
    ⟨_, _, _, GlobalTheory.FlagGenFib.isPullback_f q π, GlobalTheory.FlagGenFib.isIntegral_Gf q π _ arY'⟩
  obtain ⟨X, iX, ρ, fl', j, ej, pbX, hcov, nX, hcomp⟩ := GlobalTheory.T.flag_pullback_generic_fibre D.what₂.LL Y (π ≫ q) _ arY' nY (D.host.E →+* ℂ)
    (fun σ => (Scheme.Modules.pullback π).obj (E σ)) (fun σ => (Scheme.Modules.pullback π).obj (E' σ)) O.S.Dw.mult
    (fun σ => (h' σ).isVB.pullback π) (fun σ => (Scheme.Modules.pullback π).map (u σ)) fl Gs jY s pbY
    (fun σ => GlobalTheory.T.frame_assignment_morphism D O B q Bg jB πB pbB σ (E σ) (E' σ) (h σ).isVB (h' σ).isVB (u σ) (t σ) (t' σ) (frE σ) (frE' σ)
      (hmat σ) Y Gs π jY s pbY.w)
  obtain ⟨πG, φ, jG, r, hcc, hr⟩ := GlobalTheory.T.eigen_metric_comparison_normal p2 pH pRA D O hO R hR c B q E E' h h' u hq hn hu Bg jB πB t t' G hW
    Y π fl hfb arY' nY X Gs ρ j s (ej ▸ pbY) pbX
  choose r' hr' using fun σ => GlobalTheory.T.pair_cover_compatibility D O R c B q Bg jB πB G Y X Gs π ρ j πG φ jG hcc σ (E σ) (E' σ) (h σ).isVB
    (h' σ).isVB (u σ) (t σ) (t' σ) (frE σ) (frE' σ) (hmat σ) ((fl σ).pull ρ) (fl' σ) (hcomp σ) (r σ) (hr σ)
  obtain ⟨-, -, -, -, pb, hfin, hsur, φs, -, -⟩ := id hcc
  let V : Cover (O.var c) :=
    { X := X, p := ρ ≫ π ≫ q, ar := hcov.1, normal := nX, G := Gs, j := j, π := πG, pb := pb, fin := hfin,
      surj := hsur, φ := φ, φ_spec := φs }
  refine ⟨V, Y, iY, π, ρ, rfl, fl, fl', arY', hcov, hfb, hcomp, fun z => ?_, fun k z hk => ?_⟩
  · have hl : letterOf O.S.Dw (.inl (z.1, (z.2 : ℕ))) = some ⟨z.1, z.2⟩ := by
      simp [letterOf, z.2.isLt]
    have hind : V.Induces (lineAdl O R c (.inl (z.1, (z.2 : ℕ))) 1)
        (VMetric.grLB ((fl z.1).pull ρ) z.2 (((H z.1).pull π rfl).pull ρ rfl)) 1 := by
      obtain ⟨h1, h2⟩ := GlobalTheory.T.pair_cover_hodge_comparison p2 pH pRA D O hO R hR c B q hq hn Bg jB πB G Y X Gs π ρ j πG φ jG hcov.1 nX hcc z.1 (E z.1) (h z.1) (H z.1) (t z.1)
        (frE z.1) ((fl z.1).pull ρ) z.2 (r z.1 z.2) (hr z.1 z.2) _ hl
      exact ⟨r z.1 z.2, h1, h2,
        fun τ zc y y' ch e1 e2 hc => GlobalTheory.T.pair_cover_hodge_metric p2 pH pRA D O hO R hR c B q hq hn Bg jB πB G Y X Gs π ρ j πG φ jG hcov.1 nX hcc z.1 (E z.1) (h z.1)
          (H z.1) (t z.1) (frE z.1) (metE z.1) ((fl z.1).pull ρ) z.2 (r z.1 z.2) (hr z.1 z.2) _ hl τ zc y y' ch e1 e2 hc,
        fun v e y zg yt ch e1 e2 hc => GlobalTheory.T.pair_cover_hodge_degree p2 pH pRA D O hO R hR c B q hq hn Bg jB πB G Y X Gs π ρ j πG φ jG hcov.1 nX hcc z.1 (E z.1) (h z.1)
          (H z.1) (t z.1) (frE z.1) (latE z.1) ((fl z.1).pull ρ) z.2 (r z.1 z.2) (hr z.1 z.2) v e y zg yt ch e1 e2 hc⟩
    exact GlobalTheory.InducesIsom.induces_of_isometric V _ _ _ 1 hind
      (VMetric.isometric_grLB_pull (𝓞 D.what₂.LL) Y X (π ≫ q) (ρ ≫ π ≫ q) _ _ ((h z.1).pull π rfl) ((H z.1).pull π rfl)
        (fl z.1) ρ rfl z.2)
  · have hl : letterOf O.S.Dw (.inr k) = some ⟨z.1, z.2⟩ := hk
    obtain ⟨h1, h2⟩ := GlobalTheory.T.pair_cover_hodge_comparison p2 pH pRA D O hO R hR c B q hq hn Bg jB πB G Y X Gs π ρ j πG φ jG hcov.1 nX hcc z.1 (E' z.1) (h' z.1) (H' z.1)
      (t' z.1) (frE' z.1) (fl' z.1) z.2 (r' z.1 z.2) (hr' z.1 z.2) _ hl
    exact ⟨r' z.1 z.2, h1, h2,
      fun τ zc y y' ch e1 e2 hc => GlobalTheory.T.pair_cover_hodge_metric p2 pH pRA D O hO R hR c B q hq hn Bg jB πB G Y X Gs π ρ j πG φ jG hcov.1 nX hcc z.1 (E' z.1) (h' z.1)
        (H' z.1) (t' z.1) (frE' z.1) (metE' z.1) (fl' z.1) z.2 (r' z.1 z.2) (hr' z.1 z.2) _ hl τ zc y y' ch e1 e2 hc,
      fun v e y zg yt ch e1 e2 hc => GlobalTheory.T.pair_cover_hodge_height p2 pH pRA D O hO R hR c B q hq hn Bg jB πB G Y X Gs π ρ j πG φ jG hcov.1 nX hcc z.1 (E' z.1) (h' z.1)
        (H' z.1) (t' z.1) (frE' z.1) (latE' z.1) (fl' z.1) z.2 (r' z.1 z.2) (hr' z.1 z.2) k hk v e y zg yt ch e1 e2 hc⟩

end GlobalTheory.PairCov

end
