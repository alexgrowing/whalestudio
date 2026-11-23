import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrameAssignmentMorphism
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PairBaseIff
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open Formalism.BasicNotions.DV Formalism.MainNotions.WeightThresholdDefs GlobalTheory.FlagAr GlobalTheory.ShFam.Pad GlobalTheory.VB GlobalTheory.ShFam GlobalTheory.TrueGeo Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ArLieBase
open GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.ProjVar GlobalTheory.TwoLat GlobalTheory.FlagCov
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frame_assignment_morphism : ∀ (D : D7) (O : Setup D) (B : Scheme.{0}) (q : B ⟶ Sp (𝓞 D.what₂.LL)) (Bg : Scheme.{0}) (jB : Bg ⟶ B) (πB : Bg ⟶ gen O.s.T.Z),
    IsPullback jB (πB ≫ genStr O.s.T.Z ≫ spMap O.κ.e.toRingHom) q (spMap (algebraMap (𝓞 D.what₂.LL) D.what₂.LL)) →
    ∀ (σ : D.host.E →+* ℂ) (M M' : B.Modules), IsVB M (O.S.Dw.mult σ) → IsVB M' (O.S.Dw.mult σ) →
    ∀ (u : M ⟶ M') (t : FrAssign O.s.T.Z M (O.S.Dw.mult σ) jB) (t' : FrAssign O.s.T.Z M' (O.S.Dw.mult σ) jB),
    IsLieFrames O.s.T.Z O.κ.e jB πB M _ σ false t → IsLieFrames O.s.T.Z O.κ.e jB πB M' _ σ false t' →
    Matches O.s.T.Z jB πB u t t' →
    ∀ (Y Gs : Scheme.{0}) (π : Y ⟶ B) (jY : Gs ⟶ Y) (s : Gs ⟶ Sp D.what₂.LL),
      jY ≫ π ≫ q = s ≫ spMap (algebraMap (𝓞 D.what₂.LL) D.what₂.LL) →
      IsIso ((Scheme.Modules.pullback jY).map ((Scheme.Modules.pullback π).map u)) := by
  first | exact @GlobalTheory.PairCov.isIso_pullback_of_matches | exact GlobalTheory.PairCov.isIso_pullback_of_matches | (intros; apply GlobalTheory.PairCov.isIso_pullback_of_matches <;> assumption)
