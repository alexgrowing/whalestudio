import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieGenericEigenMetricBound
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieBaseIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieBaseAt
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open Formalism.BasicNotions.DV Formalism.MainNotions.WeightThresholdDefs GlobalTheory.FlagAr GlobalTheory.ShFam.Pad GlobalTheory.VB GlobalTheory.ShFam GlobalTheory.TrueGeo Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ArLieBase
open GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.ProjVar
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lie_generic_eigen_metric_bound : ∀ (D : D7) (O : Setup D) (c : O.s.Comp) (Bs : Scheme.{0}) (q : Bs ⟶ Sp (𝓞 D.what₂.LL))
    (E : D.what₂.Tau × Bool → Bs.Modules) (h : ∀ a, VMetric q (E a) (rkB D.what₂.Tau O.N O.j a)) (H : ∀ a, (h a).IsCInf)
    (Bg : Scheme.{0}) (jB : Bg ⟶ Bs) (πB : Bg ⟶ gen O.s.T.Z)
    (u : ∀ a, FrAssign O.s.T.Z (E a) (rkB D.what₂.Tau O.N O.j a) jB) (_ : GlobalTheory.BcRead.LieGen O c q E jB πB u)
    (Gm : ∀ σ', EigMet O.s.T.Z σ')
    (_ : ∀ a, ∃ hr : rkB D.what₂.Tau O.N O.j a = O.S.Dw.mult (embB D a),
      IsLieMet O.s.T.Z O.κ.e q jB πB (E a) _ (embB D a) (!a.2) hr Gm (h a) (u a))
    (Y₀ : Scheme.{0}) [IsIntegral Y₀] (π₀ : Y₀ ⟶ Bs)
    (fl₀ : ∀ a, Vert.Flag ((Scheme.Modules.pullback π₀).obj (E a)) (rkB D.what₂.Tau O.N O.j a))
    (_ : IsFlagBundle π₀ E (rkB D.what₂.Tau O.N O.j) fl₀)
    (G : Scheme.{0}) [IsIntegral G] (j : G ⟶ Y₀) (πG : G ⟶ (O.var c).X)
    (_ : IsPullback j (πG ≫ (O.var c).str) (π₀ ≫ q) (spMap (algebraMap (𝓞 D.what₂.LL) D.what₂.LL)))
    [IsFinite πG] [Surjective πG] (φ : (O.var c).Fn →+* G.functionField)
    (_ : G.fromSpecStalk (genericPoint G) ≫ πG = spMap φ ≫ (O.var c).X.fromSpecStalk (genericPoint (O.var c).X))
    (jG : G ⟶ Bg) (r : ∀ a i, (((fl₀ a).root i).pull j).ι → G.functionFieldˣ)
    (_ : GlobalTheory.FlagCov.FlagCover (fun a => (h a).isVB) jB πB u π₀ fl₀ j πG φ jG r)
    (a : D.what₂.Tau × Bool), a.2 = false → ∀ (i : Fin (rkB D.what₂.Tau O.N O.j a))
    (σ : D.what₂.LL →+* ℂ) (z : CxPts (πG ≫ (O.var c).str) σ) (y : Pts (O.var c) σ)
    (y' : CxPts (π₀ ≫ q) (σ.comp (algebraMap (𝓞 D.what₂.LL) D.what₂.LL))) (ch : (((fl₀ a).root i).pull j).ι)
    (t : ∀ τ : D.host.E →+* ℂ, Fin (O.S.Dw.mult τ) → (O.var c).Fnˣ) (g : (O.Φ.C c).FrameAt y),
    (O.Φ.C c).Adapted y t g 1 → y.1 = z.1 ≫ πG → y'.1 = z.1 ≫ j → under z ∈ (((fl₀ a).root i).pull j).U ch →
    UnitAt (under z) ((((r a i ch)⁻¹ : G.functionFieldˣ) : G.functionField) *
        φ ((prodPow t (rootEx O.S.Dw (DV.tauEmb D a.1) (cond a.2 0 O.j + i)) : (O.var c).Fnˣ) : (O.var c).Fn)) ∧
      Real.exp (-((VMetric.grLB (fl₀ a) i ((H a).pull π₀ rfl)).φ (σ.comp (algebraMap (𝓞 D.what₂.LL) D.what₂.LL))).φ
          (ch PUnit.unit) y') =
        ‖ratVal ((((r a i ch)⁻¹ : G.functionFieldˣ) : G.functionField) *
          φ ((prodPow t (rootEx O.S.Dw (DV.tauEmb D a.1) (cond a.2 0 O.j + i)) : (O.var c).Fnˣ) : (O.var c).Fn)) z‖ ^ 2 *
          (O.Φ.C c).genSq (Gm (embOf O.κ.e σ)) (rootEx O.S.Dw (DV.tauEmb D a.1) (cond a.2 0 O.j + i)) g := by
  first | exact @GlobalTheory.FlagCovDualNorm.weight_dual | exact GlobalTheory.FlagCovDualNorm.weight_dual | (intros; apply GlobalTheory.FlagCovDualNorm.weight_dual <;> assumption)
