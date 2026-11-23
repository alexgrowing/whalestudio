import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieFramesPullbackGeneric
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagMat
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open Formalism.BasicNotions.DV Formalism.MainNotions.WeightThresholdDefs GlobalTheory.FlagAr GlobalTheory.ShFam.Pad GlobalTheory.VB GlobalTheory.ShFam GlobalTheory.TrueGeo Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ArLieBase
open GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.ProjVar
open GlobalTheory.FlagCls
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lie_frames_pullback_generic : ∀ (D : D7) (O : Setup D) (c : O.s.Comp) (Bs : Scheme.{0}) (E : D.what₂.Tau × Bool → Bs.Modules) (hE : ∀ a, IsVB (E a) (rkB D.what₂.Tau O.N O.j a)) (Bg : Scheme.{0}) (jB : Bg ⟶ Bs) (πB : Bg ⟶ gen O.s.T.Z) (u : ∀ a, FrAssign O.s.T.Z (E a) (rkB D.what₂.Tau O.N O.j a) jB), (∀ a, IsLieFrames O.s.T.Z O.κ.e jB πB (E a) _ (embB D a) (!a.2) (u a)) → ∀ (hr : ∀ a, rkB D.what₂.Tau O.N O.j a = O.S.Dw.mult (embB D a)) (Y₀ : Scheme.{0}) (π₀ : Y₀ ⟶ Bs) (fl₀ : ∀ a, Vert.Flag ((Scheme.Modules.pullback π₀).obj (E a)) (rkB D.what₂.Tau O.N O.j a)) (G : Scheme.{0}) [IsIntegral G] (j : G ⟶ Y₀) (jG : G ⟶ Bg) (φ : (O.var c).Fn →+* G.functionField) (χ : O.κ.c.F →+* G.functionField) (x : Sp G.functionField ⟶ O.s.T.Z.X) (g : EigFrame O.s.T.Z χ x), (O.Φ.C c).f0.IsMap φ g → Bears O.s.T.Z (embB D) (fun a => !a.2) hr hE jB πB u π₀ fl₀ (GlobalTheory.FlagCov.genPt G ≫ j) (GlobalTheory.FlagCov.genPt G ≫ jG) g → ∀ a, GlobalTheory.FlagCov.FlagAgree hE jB πB u π₀ fl₀ j φ jG a (hr a) := by
  first | exact @GlobalTheory.FlagCls.flagAgree_of_bears | exact GlobalTheory.FlagCls.flagAgree_of_bears | (intros; apply GlobalTheory.FlagCls.flagAgree_of_bears <;> assumption)
