import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithBaseHermitianBundlesFifth
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieBaseIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieBaseAt
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open Formalism.BasicNotions.DV Formalism.MainNotions.WeightThresholdDefs GlobalTheory.FlagAr GlobalTheory.ShFam.Pad GlobalTheory.VB GlobalTheory.ShFam GlobalTheory.TrueGeo Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ArLieBase
open GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.ProjVar
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.arith_base_hermitian_bundles_fifth : Hypotheses2 → HypothesesH → RegularAlteration →
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
    (n₀ : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme Y₀) (G : Scheme.{0}) [IsIntegral G] (j : G ⟶ Y₀) (πG : G ⟶ (O.var c).X)
    (pb : IsPullback j (πG ≫ (O.var c).str) (π₀ ≫ q) (spMap (algebraMap (𝓞 D.what₂.LL) D.what₂.LL)))
    [IsFinite πG] [Surjective πG] (φ : (O.var c).Fn →+* G.functionField)
    (φs : G.fromSpecStalk (genericPoint G) ≫ πG = spMap φ ≫ (O.var c).X.fromSpecStalk (genericPoint (O.var c).X))
    (jG : G ⟶ Bg) (r : ∀ a i, (((fl₀ a).root i).pull j).ι → G.functionFieldˣ)
    (hc : GlobalTheory.FlagCov.FlagCover (fun a => (h a).isVB) jB πB u π₀ fl₀ j πG φ jG r)
    (a : D.what₂.Tau × Bool) (i : Fin (rkB D.what₂.Tau O.N O.j a))
    (σ : D.what₂.LL →+* ℂ) (z : CxPts (πG ≫ (O.var c).str) σ) (y : Pts (O.var c) σ)
    (y' : CxPts (π₀ ≫ q) (σ.comp (algebraMap (𝓞 D.what₂.LL) D.what₂.LL))) (ch : ((VMetric.grLB (fl₀ a) i ((H a).pull π₀ rfl)).B.pull j).ι),
    y.1 = z.1 ≫ πG → y'.1 = z.1 ≫ j → under z ∈ ((VMetric.grLB (fl₀ a) i ((H a).pull π₀ rfl)).B.pull j).U ch →
      (Real.exp (-(2 * ((adlOf (O.Φ.C c) (O.met.hm c) (rootSym O.S.Dw (ArIn.ind P) (some R) (DV.tauEmb D a.1) (cond a.2 0 O.j + i))).n : ℕ) * (adlOf (O.Φ.C c) (O.met.hm c) (rootSym O.S.Dw (ArIn.ind P) (some R) (DV.tauEmb D a.1) (cond a.2 0 O.j + i))).ci (InfinitePlace.mk σ))) *
          (cxSt D.what₂.LL).pn (O.var c) σ (adlOf (O.Φ.C c) (O.met.hm c) (rootSym O.S.Dw (ArIn.ind P) (some R) (DV.tauEmb D a.1) (cond a.2 0 O.j + i))).D ((adlOf (O.Φ.C c) (O.met.hm c) (rootSym O.S.Dw (ArIn.ind P) (some R) (DV.tauEmb D a.1) (cond a.2 0 O.j + i))).m σ) ((cxSt D.what₂.LL).cx (O.var c) σ (genAt (adlOf (O.Φ.C c) (O.met.hm c) (rootSym O.S.Dw (ArIn.ind P) (some R) (DV.tauEmb D a.1) (cond a.2 0 O.j + i))).D (under y))) y) ^ 1 =
        ‖ratVal (φ (genAt (adlOf (O.Φ.C c) (O.met.hm c) (rootSym O.S.Dw (ArIn.ind P) (some R) (DV.tauEmb D a.1) (cond a.2 0 O.j + i))).D (under y)) ^ 1 * (r a i ch : G.functionField)) z‖ ^ 2 * Real.exp (-((VMetric.grLB (fl₀ a) i ((H a).pull π₀ rfl)).φ _).φ (ch PUnit.unit) y') := by
  first | exact @GlobalTheory.BcReadCx.frameSec_norm_cx | exact GlobalTheory.BcReadCx.frameSec_norm_cx | (intros; apply GlobalTheory.BcReadCx.frameSec_norm_cx <;> assumption)
