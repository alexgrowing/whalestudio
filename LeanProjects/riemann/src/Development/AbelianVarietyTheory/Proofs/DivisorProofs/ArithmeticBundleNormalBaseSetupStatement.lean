import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithmeticBundleNormalBaseSetup
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagAgree
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open Formalism.BasicNotions.DV Formalism.MainNotions.WeightThresholdDefs GlobalTheory.FlagAr GlobalTheory.ShFam.Pad GlobalTheory.VB GlobalTheory.ShFam GlobalTheory.TrueGeo Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ArLieBase
open GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.ProjVar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.arithmetic_bundle_normal_base_setup : Hypotheses2 → HypothesesH → RegularAlteration →
  ∀ (D : D7) (O : Setup D) (hO : O.Core) (P : Finset ℕ) (R : ℝ) (hR : 2 ≤ R) (c : O.s.Comp)
    (Bs : Scheme.{0}) [IsIntegral Bs] (q : Bs ⟶ Sp (𝓞 D.what₂.LL)) (arq : IsArithVar q (dimGr D.what₂.Tau O.N O.j))
    (nBs : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme Bs) (E : D.what₂.Tau × Bool → Bs.Modules)
    (h : ∀ a, VMetric q (E a) (rkB D.what₂.Tau O.N O.j a)) (H : ∀ a, (h a).IsCInf)
    (Bg : Scheme.{0}) (jB : Bg ⟶ Bs) (πB : Bg ⟶ gen O.s.T.Z)
    (u : ∀ a, FrAssign O.s.T.Z (E a) (rkB D.what₂.Tau O.N O.j a) jB)
    (hG : GlobalTheory.BcRead.LieGen O c q E jB πB u) (hF : GlobalTheory.BcRead.LieFin O P E jB πB u)
    (hI : GlobalTheory.BcRead.LieInf O R c q E h jB πB u)
    (Y₀ : Scheme.{0}) [IsIntegral Y₀] (π₀ : Y₀ ⟶ Bs)
    (fl₀ : ∀ a, Vert.Flag ((Scheme.Modules.pullback π₀).obj (E a)) (rkB D.what₂.Tau O.N O.j a))
    (hfb : IsFlagBundle π₀ E (rkB D.what₂.Tau O.N O.j) fl₀) (ar₀ : IsArithVar (π₀ ≫ q) (O.var c).dim)
    (n₀ : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme Y₀)
    (G : Scheme.{0}) [IsIntegral G] (j : G ⟶ Y₀) (s : G ⟶ Sp D.what₂.LL)
    (_ : IsPullback j s (π₀ ≫ q) (spMap (algebraMap (𝓞 D.what₂.LL) D.what₂.LL)))
    (jG : G ⟶ Bg) (_ : jG ≫ jB = j ≫ π₀) (_ : jG ≫ πB ≫ genStr O.s.T.Z ≫ spMap O.κ.e.toRingHom = s),
  ∃ (πG : G ⟶ (O.var c).X) (φ : (O.var c).Fn →+* G.functionField),
    jG ≫ πB = πG ≫ (O.Φ.C c).π ∧ IsFinite πG ∧ Surjective πG ∧
    G.fromSpecStalk (genericPoint G) ≫ πG = spMap φ ≫ (O.var c).X.fromSpecStalk (genericPoint (O.var c).X) ∧
    ∀ a (hr : rkB D.what₂.Tau O.N O.j a = O.S.Dw.mult (embB D a)),
      GlobalTheory.FlagCov.FlagAgree (fun a => (h a).isVB) jB πB u π₀ fl₀ j φ jG a hr := by
  first | exact @GlobalTheory.BcRead.classifyingMap | exact GlobalTheory.BcRead.classifyingMap | (intros; apply GlobalTheory.BcRead.classifyingMap <;> assumption)
