import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PairCoverHodgeMetric
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PairBaseIff
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open Formalism.BasicNotions.DV Formalism.MainNotions.WeightThresholdDefs GlobalTheory.FlagAr GlobalTheory.ShFam.Pad GlobalTheory.VB GlobalTheory.ShFam GlobalTheory.TrueGeo Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ArLieBase
open GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.ProjVar GlobalTheory.TwoLat GlobalTheory.FlagCov
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pair_cover_hodge_metric : GlobalTheory.CovTop.Hypotheses2 → GlobalTheory.CovHt.HypothesesH → GlobalTheory.Published.RegularAlteration →
  ∀ (D : D7) (O : Setup D) (hO : O.Core) (R : ℝ) (hR : 2 ≤ R) (c : O.s.Comp) (Bs : Scheme.{0}) [IsIntegral Bs] (q : Bs ⟶ Sp (𝓞 D.what₂.LL))
    (arq : IsArithVar q (dimGr D.what₂.Tau O.N O.j)) (nBs : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme Bs)
    (Bg : Scheme.{0}) (jB : Bg ⟶ Bs) (πB : Bg ⟶ gen O.s.T.Z) (G : ∀ σ', EigMet O.s.T.Z σ')
    (Y X Gs : Scheme.{0}) [IsIntegral Y] [IsIntegral X] [IsIntegral Gs] (π : Y ⟶ Bs) (ρ : X ⟶ Y) (j : Gs ⟶ X)
    (πG : Gs ⟶ (O.var c).X) (φ : (O.var c).Fn →+* Gs.functionField) (jG : Gs ⟶ Bg),
    IsArithVar (ρ ≫ π ≫ q) (O.var c).dim → ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme X →
    GlobalTheory.PairCov.CovCommon O R c q jB πB G π ρ j πG φ jG →
    ∀ (σ : D.host.E →+* ℂ) (M : Bs.Modules) (hM : VMetric q M (O.S.Dw.mult σ)) (HM : hM.IsCInf)
      (t : FrAssign O.s.T.Z M (O.S.Dw.mult σ) jB), IsLieFrames O.s.T.Z O.κ.e jB πB M _ σ false t →
    IsLieMet O.s.T.Z O.κ.e q jB πB M _ σ false rfl G hM t →
    ∀ (F : Vert.Flag ((Scheme.Modules.pullback ρ).obj ((Scheme.Modules.pullback π).obj M)) (O.S.Dw.mult σ))
      (i : Fin (O.S.Dw.mult σ)) (r : ((F.root i).pull j).ι → Gs.functionFieldˣ),
      GlobalTheory.PairCov.IsFrameSecX (O := O) (c := c) σ hM.isVB jB πB t π ρ F j φ jG i r →
    ∀ st, letterOf O.S.Dw st = some ⟨σ, i⟩ →
    ∀ (τ : D.what₂.LL →+* ℂ) (z : CxPts (πG ≫ (O.var c).str) τ) (y : Pts (O.var c) τ)
      (y' : CxPts (ρ ≫ π ≫ q) (τ.comp (algebraMap (𝓞 D.what₂.LL) D.what₂.LL))) (ch : ((VMetric.grLB F i ((HM.pull π rfl).pull ρ rfl)).B.pull j).ι),
      y.1 = z.1 ≫ πG → y'.1 = z.1 ≫ j → under z ∈ ((VMetric.grLB F i ((HM.pull π rfl).pull ρ rfl)).B.pull j).U ch →
        (Real.exp (-(2 * ((lineAdl O R c st 1).n : ℕ) * (lineAdl O R c st 1).ci (InfinitePlace.mk τ))) *
          (cxSt D.what₂.LL).pn (O.var c) τ (lineAdl O R c st 1).D ((lineAdl O R c st 1).m τ)
            ((cxSt D.what₂.LL).cx (O.var c) τ (genAt (lineAdl O R c st 1).D (under y))) y) ^ 1 =
        ‖ratVal (φ (genAt (lineAdl O R c st 1).D (under y)) ^ 1 * (r ch : Gs.functionField)) z‖ ^ 2 *
          Real.exp (-((VMetric.grLB F i ((HM.pull π rfl).pull ρ rfl)).φ _).φ (ch PUnit.unit) y') := by
  first | exact @GlobalTheory.PairCovCx.frameSecX_norm_cx | exact GlobalTheory.PairCovCx.frameSecX_norm_cx | (intros; apply GlobalTheory.PairCovCx.frameSecX_norm_cx <;> assumption)
