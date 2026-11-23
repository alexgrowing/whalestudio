import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PairBaseIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EvalPtTrCoPullback
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagMatOfIsFrameSecX
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUnitDetTrans
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open Formalism.BasicNotions.DV Formalism.MainNotions.WeightThresholdDefs GlobalTheory.FlagAr GlobalTheory.ShFam.Pad GlobalTheory.VB GlobalTheory.ShFam GlobalTheory.TrueGeo Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ArLieBase
open GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.ProjVar GlobalTheory.TwoLat GlobalTheory.FlagCov
open scoped Classical

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.PairCov

theorem exists_isFrameSecX_of_compat : ∀ (D : D7) (O : Setup D) (R : ℝ) (c : O.s.Comp) (Bs : Scheme.{0}) [IsIntegral Bs] (q : Bs ⟶ Sp (𝓞 D.what₂.LL))
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
  intro D O R c Bs _ q Bg jB πB G Y X Gs _ _ _ π ρ j πG φ jG hc σ M M' hM hM' u t t' ht ht' hu F F' hF r hr
  obtain ⟨-, -, -, -, -, -, -, h₁, h₂, h₃⟩ := hc
  exact GlobalTheory.PairCov.exists_isFrameSecX D O c Bs Bg jB πB Y X Gs π ρ j πG φ jG h₁ h₂ h₃ σ M' hM' t' ht' F'
    (GlobalTheory.FlagMove.flagMat_move D O c Bs Bg jB πB Y X Gs π ρ j πG φ jG h₁ h₂ h₃ σ M hM t ht F M' hM' t' ht' F' u hu hF
      (GlobalTheory.FlagCls.flagMat_of_isFrameSecX D O c Bs Bg jB πB Y X Gs π ρ j πG φ jG h₁ h₂ h₃ σ M hM t ht F r hr))

end GlobalTheory.PairCov

end
