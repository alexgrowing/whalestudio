import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PairCoverHodgeDegree
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PairBaseIff
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open Formalism.BasicNotions.DV Formalism.MainNotions.WeightThresholdDefs GlobalTheory.FlagAr GlobalTheory.ShFam.Pad GlobalTheory.VB GlobalTheory.ShFam GlobalTheory.TrueGeo Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ArLieBase
open GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.ProjVar GlobalTheory.TwoLat GlobalTheory.FlagCov
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pair_cover_hodge_degree : GlobalTheory.CovTop.Hypotheses2 → GlobalTheory.CovHt.HypothesesH → GlobalTheory.Published.RegularAlteration →
  ∀ (D : D7) (O : Setup D) (hO : O.Core) (R : ℝ) (hR : 2 ≤ R) (c : O.s.Comp) (Bs : Scheme.{0}) [IsIntegral Bs] (q : Bs ⟶ Sp (𝓞 D.what₂.LL))
    (arq : IsArithVar q (dimGr D.what₂.Tau O.N O.j)) (nBs : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme Bs)
    (Bg : Scheme.{0}) (jB : Bg ⟶ Bs) (πB : Bg ⟶ gen O.s.T.Z) (G : ∀ σ', EigMet O.s.T.Z σ')
    (Y X Gs : Scheme.{0}) [IsIntegral Y] [IsIntegral X] [IsIntegral Gs] (π : Y ⟶ Bs) (ρ : X ⟶ Y) (j : Gs ⟶ X)
    (πG : Gs ⟶ (O.var c).X) (φ : (O.var c).Fn →+* Gs.functionField) (jG : Gs ⟶ Bg),
    IsArithVar (ρ ≫ π ≫ q) (O.var c).dim → ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme X →
    GlobalTheory.PairCov.CovCommon O R c q jB πB G π ρ j πG φ jG →
    ∀ (σ : D.host.E →+* ℂ) (M : Bs.Modules) (hM : VMetric q M (O.S.Dw.mult σ)) (HM : hM.IsCInf)
      (t : FrAssign O.s.T.Z M (O.S.Dw.mult σ) jB), IsLieFrames O.s.T.Z O.κ.e jB πB M _ σ false t →
    IsLieLat O.s.T.Z O.κ.e jB πB M _ σ (ArIn.ind ∅) (fun _ => True) t →
    ∀ (F : Vert.Flag ((Scheme.Modules.pullback ρ).obj ((Scheme.Modules.pullback π).obj M)) (O.S.Dw.mult σ))
      (i : Fin (O.S.Dw.mult σ)) (r : ((F.root i).pull j).ι → Gs.functionFieldˣ),
      GlobalTheory.PairCov.IsFrameSecX (O := O) (c := c) σ hM.isVB jB πB t π ρ F j φ jG i r →
    ∀ (v : IsDedekindDomain.HeightOneSpectrum (𝓞 D.what₂.LL)) (e : Ext v) (y : AlgPt (O.var c))
      (z : Sp (AlgebraicClosure D.what₂.LL) ⟶ Gs) (yt : Sp e.O ⟶ X) (ch : ((VMetric.grLB F i ((HM.pull π rfl).pull ρ rfl)).B.pull j).ι),
      z ≫ πG = y.1 → spMap e.O.subtype ≫ yt = z ≫ j → ⊤ ≤ yt ⁻¹ᵁ (VMetric.grLB F i ((HM.pull π rfl).pull ρ rfl)).B.U (ch PUnit.unit) →
        ((1 : ℕ) : ℝ) * (lineAdl O R c (.inl (σ, (i : ℕ))) 1).lg v e y =
          Real.log (e.w (valAt z (φ (genAt (lineAdl O R c (.inl (σ, (i : ℕ))) 1).D (below y.1)) ^ 1 * (r ch : Gs.functionField)))) := by
  first | exact @GlobalTheory.PairCov.FinLine.lg_line_eq | exact GlobalTheory.PairCov.FinLine.lg_line_eq | (intros; apply GlobalTheory.PairCov.FinLine.lg_line_eq <;> assumption)
