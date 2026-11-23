import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PairCoverCompatibility
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PairBaseIff
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open Formalism.BasicNotions.DV Formalism.MainNotions.WeightThresholdDefs GlobalTheory.FlagAr GlobalTheory.ShFam.Pad GlobalTheory.VB GlobalTheory.ShFam GlobalTheory.TrueGeo Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ArLieBase
open GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.ProjVar GlobalTheory.TwoLat GlobalTheory.FlagCov
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pair_cover_compatibility : ∀ (D : D7) (O : Setup D) (R : ℝ) (c : O.s.Comp) (Bs : Scheme.{0}) [IsIntegral Bs] (q : Bs ⟶ Sp (𝓞 D.what₂.LL))
    (Bg : Scheme.{0}) (jB : Bg ⟶ Bs) (πB : Bg ⟶ gen O.s.T.Z) (G : ∀ σ', EigMet O.s.T.Z σ')
    (Y X Gs : Scheme.{0}) [IsIntegral Y] [IsIntegral X] [IsIntegral Gs] (π : Y ⟶ Bs) (ρ : X ⟶ Y) (j : Gs ⟶ X)
    (πG : Gs ⟶ (O.var c).X) (φ : (O.var c).Fn →+* Gs.functionField) (jG : Gs ⟶ Bg),
    GlobalTheory.PairCov.CovCommon O R c q jB πB G π ρ j πG φ jG →
    ∀ (σ : D.host.E →+* ℂ) (M M' : Bs.Modules) (hM : IsVB M (O.S.Dw.mult σ)) (hM' : IsVB M' (O.S.Dw.mult σ))
      (u : M ⟶ M') (t : FrAssign O.s.T.Z M (O.S.Dw.mult σ) jB) (t' : FrAssign O.s.T.Z M' (O.S.Dw.mult σ) jB),
    IsLieFrames O.s.T.Z O.κ.e jB πB M _ σ false t → IsLieFrames O.s.T.Z O.κ.e jB πB M' _ σ false t' →
    Matches O.s.T.Z jB πB u t t' →
    ∀ (F : Vert.Flag ((Scheme.Modules.pullback ρ).obj ((Scheme.Modules.pullback π).obj M)) (O.S.Dw.mult σ)) (F' : Vert.Flag ((Scheme.Modules.pullback ρ).obj ((Scheme.Modules.pullback π).obj M')) (O.S.Dw.mult σ)),
      Compat ((Scheme.Modules.pullback ρ).map ((Scheme.Modules.pullback π).map u)) F F' →
    ∀ r : ∀ i, ((F.root i).pull j).ι → Gs.functionFieldˣ,
      (∀ i, GlobalTheory.PairCov.IsFrameSecX (O := O) (c := c) σ hM jB πB t π ρ F j φ jG i (r i)) →
    ∀ i, ∃ r' : ((F'.root i).pull j).ι → Gs.functionFieldˣ,
      GlobalTheory.PairCov.IsFrameSecX (O := O) (c := c) σ hM' jB πB t' π ρ F' j φ jG i r' := by
  first | exact @GlobalTheory.PairCov.exists_isFrameSecX_of_compat | exact GlobalTheory.PairCov.exists_isFrameSecX_of_compat | (intros; apply GlobalTheory.PairCov.exists_isFrameSecX_of_compat <;> assumption)
