import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ScholzeWeinsteinB
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsFlagBundleRankOne
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.RegularAlteration
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagInduces
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagBundleAdelicMetricDataStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagBundleMetricBaseExistsStatement
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open scoped Classical
open Formalism.BasicNotions.DV Formalism.MainNotions.WeightThresholdDefs GlobalTheory.FlagAr GlobalTheory.ShFam.Pad GlobalTheory.VB

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CovTest

set_option maxHeartbeats 1000000 in

theorem exists_base_flagInduces : Hypotheses2 → HypothesesH → RegularAlteration → ScholzeWeinsteinB →
  ∀ (D : D7) (O : Setup D), O.Core → ∀ B : ℝ, 2 ≤ B → ∀ R : ℝ, 2 ≤ R → ∀ c : O.s.Comp,
  ∃ (Bs : Scheme.{0}) (_ : IsIntegral Bs) (q : Bs ⟶ Sp (𝓞 D.what₂.LL)) (_ : IsArithVar q (dimGr D.what₂.Tau O.N O.j))
    (_ : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme Bs) (E : D.what₂.Tau × Bool → Bs.Modules)
    (h : ∀ a, VMetric q (E a) (rkB D.what₂.Tau O.N O.j a)) (H : ∀ a, (h a).IsCInf),
    ∀ (Y : Scheme.{0}) (_ : IsIntegral Y) (π : Y ⟶ Bs)
      (fl : ∀ a, Vert.Flag ((Scheme.Modules.pullback π).obj (E a)) (rkB D.what₂.Tau O.N O.j a)),
      IsFlagBundle π E (rkB D.what₂.Tau O.N O.j) fl → ∀ (arY : IsArithVar (π ≫ q) (O.var c).dim)
      (nY : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme Y),
      ∃ (G : Scheme.{0}) (_ : IsIntegral G) (j : G ⟶ Y) (πG : G ⟶ (O.var c).X)
        (pb : IsPullback j (πG ≫ (O.var c).str) (π ≫ q) (spMap (algebraMap (𝓞 D.what₂.LL) D.what₂.LL)))
        (_ : IsFinite πG) (_ : Surjective πG) (φ : (O.var c).Fn →+* G.functionField)
        (φs : G.fromSpecStalk (genericPoint G) ≫ πG = spMap φ ≫ (O.var c).X.fromSpecStalk (genericPoint (O.var c).X)),
        ∀ (a : D.what₂.Tau × Bool) (i : Fin (rkB D.what₂.Tau O.N O.j a)),
          (@Cover.mk _ _ (O.var c) Y _ (π ≫ q) arY nY G _ j πG pb _ _ φ φs).Induces
            (adlOf (O.Φ.C c) (O.met.hm c)
              (rootSym O.S.Dw (ArIn.ind (setB O.Y B)) (some R) (DV.tauEmb D a.1) (cond a.2 0 O.j + i)))
            (VMetric.grLB (fl a) i ((H a).pull π rfl)) 1 := by
  intro p2 pH rA sw D O hO B hB R hR c
  obtain ⟨Bs, iB, q, aq, nB, E, h, H, Y₀, i₀, π₀, fl₀, u₀, ar₀, n₀, hI⟩ := GlobalTheory.T.flag_bundle_metric_base_exists p2 pH rA sw D O hO B hB R hR c
  refine ⟨Bs, iB, q, aq, nB, E, h, H, fun Y iY π fl u arY nY => ?_⟩
  exact GlobalTheory.T.flag_bundle_adelic_metric_data _ Bs q _ E _ h H _ Y₀ i₀ π₀ fl₀ u₀ ar₀ n₀ hI Y iY π fl u arY nY

end GlobalTheory.CovTest

end
