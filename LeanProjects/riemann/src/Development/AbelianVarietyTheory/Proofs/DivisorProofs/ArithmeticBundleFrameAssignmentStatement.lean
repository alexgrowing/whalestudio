import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithmeticBundleFrameAssignment
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRingHomOfGeneric
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagInduces
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLieFrames
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieBaseIff
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ScholzeWeinsteinB
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsFlagBundleRankOne
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.RegularAlteration
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open Formalism.BasicNotions.DV Formalism.MainNotions.WeightThresholdDefs GlobalTheory.FlagAr GlobalTheory.ShFam.Pad GlobalTheory.VB GlobalTheory.ShFam GlobalTheory.TrueGeo Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ArLieBase
open GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.ProjVar
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.arithmetic_bundle_frame_assignment : ∀ (P2 : Hypotheses2) (PH : HypothesesH) (RA : RegularAlteration) (SW : ScholzeWeinsteinB)
    (D : D7) (O : Setup D) (hO : O.Core) (B : ℝ) (hB : 2 ≤ B) (R : ℝ) (hR : 2 ≤ R) (c : O.s.Comp)
    (Bs : Scheme.{0}) [IsIntegral Bs] (q : Bs ⟶ Sp (𝓞 D.what₂.LL)) (arq : IsArithVar q (dimGr D.what₂.Tau O.N O.j))
    (nBs : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme Bs) (E : D.what₂.Tau × Bool → Bs.Modules)
    (h : ∀ a, VMetric q (E a) (rkB D.what₂.Tau O.N O.j a)) (H : ∀ a, (h a).IsCInf)
    (Bg : Scheme.{0}) (jB : Bg ⟶ Bs) (πB : Bg ⟶ gen O.s.T.Z)
    (u : ∀ a, FrAssign O.s.T.Z (E a) (rkB D.what₂.Tau O.N O.j a) jB) (Gm : ∀ σ', EigMet O.s.T.Z σ')
    (hL : GlobalTheory.FlagCov.LieWit O B R c q E h jB πB u Gm)
    (Y₀ : Scheme.{0}) [IsIntegral Y₀] (π₀ : Y₀ ⟶ Bs)
    (fl₀ : ∀ a, Vert.Flag ((Scheme.Modules.pullback π₀).obj (E a)) (rkB D.what₂.Tau O.N O.j a))
    (hfb : IsFlagBundle π₀ E (rkB D.what₂.Tau O.N O.j) fl₀) (ar₀ : IsArithVar (π₀ ≫ q) (O.var c).dim)
    (n₀ : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme Y₀) [IsIntegral (GlobalTheory.FlagGenFib.Gf q π₀)], ∃ φ₀ : (O.var c).Fn →+* (GlobalTheory.FlagGenFib.Gf q π₀).functionField,
      (GlobalTheory.FlagGenFib.Gf q π₀).fromSpecStalk (genericPoint _) ≫ GlobalTheory.FlagGenFib.sf q π₀ =
        spMap φ₀ ≫ (O.var c).X.fromSpecStalk (genericPoint (O.var c).X) ≫ (O.var c).str ∧
      (GlobalTheory.FlagGenFib.Gf q π₀).fromSpecStalk (genericPoint _) ≫ GlobalTheory.FlagGenFib.jGf q π₀ jB _ hL.1 ≫ πB =
        spMap φ₀ ≫ (O.var c).X.fromSpecStalk (genericPoint (O.var c).X) ≫ (O.Φ.C c).π ∧
      ∀ a i (hr : rkB D.what₂.Tau O.N O.j a = O.S.Dw.mult (embB D a)),
          ∃ r : (((fl₀ a).root i).pull (GlobalTheory.FlagGenFib.jf q π₀)).ι → (GlobalTheory.FlagGenFib.Gf q π₀).functionFieldˣ,
            GlobalTheory.FlagCov.IsFrameSec (fun a => (h a).isVB) jB πB u π₀ fl₀ (GlobalTheory.FlagGenFib.jf q π₀) φ₀
              (GlobalTheory.FlagGenFib.jGf q π₀ jB _ hL.1) a i hr r := by
  first | exact @GlobalTheory.FlagGenPt.exists_fieldMap | exact GlobalTheory.FlagGenPt.exists_fieldMap | (intros; apply GlobalTheory.FlagGenPt.exists_fieldMap <;> assumption)
