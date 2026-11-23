import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagInduces
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLieFrames
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieBaseIff
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ScholzeWeinsteinB
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsFlagBundleRankOne
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.RegularAlteration
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithBaseHermitianVectorBundlesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithBaseHermitianBundlesSecondStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithBaseHermitianBundlesThirdStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithBaseHermitianBundlesFourthStatement
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open Formalism.BasicNotions.DV Formalism.MainNotions.WeightThresholdDefs GlobalTheory.FlagAr GlobalTheory.ShFam.Pad GlobalTheory.VB GlobalTheory.ShFam GlobalTheory.TrueGeo Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ArLieBase
open GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.ProjVar
open scoped Classical

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FlagCov

theorem flagInduces_of_lieBase : Hypotheses2 → HypothesesH → RegularAlteration → ScholzeWeinsteinB →
  ∀ (D : D7) (O : Setup D), O.Core → ∀ B : ℝ, 2 ≤ B → ∀ R : ℝ, 2 ≤ R → ∀ c : O.s.Comp,
  ∀ (Bs : Scheme.{0}) [IsIntegral Bs] (q : Bs ⟶ Sp (𝓞 D.what₂.LL)), IsArithVar q (dimGr D.what₂.Tau O.N O.j) →
    ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme Bs → ∀ (E : D.what₂.Tau × Bool → Bs.Modules)
    (h : ∀ a, VMetric q (E a) (rkB D.what₂.Tau O.N O.j a)) (H : ∀ a, (h a).IsCInf), GlobalTheory.ArLieBase.LieBase O B R c q E h →
    ∀ (Y₀ : Scheme.{0}) [IsIntegral Y₀] (π₀ : Y₀ ⟶ Bs)
    (fl₀ : ∀ a, Vert.Flag ((Scheme.Modules.pullback π₀).obj (E a)) (rkB D.what₂.Tau O.N O.j a)),
    IsFlagBundle π₀ E (rkB D.what₂.Tau O.N O.j) fl₀ → ∀ (ar₀ : IsArithVar (π₀ ≫ q) (O.var c).dim)
    (n₀ : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme Y₀),
    GlobalTheory.FlagInd.FlagInduces (O.var c) q E (rkB D.what₂.Tau O.N O.j) h H
      (fun a i => adlOf (O.Φ.C c) (O.met.hm c)
        (rootSym O.S.Dw (ArIn.ind (setB O.Y B)) (some R) (DV.tauEmb D a.1) (cond a.2 0 O.j + i))) Y₀ π₀ fl₀ ar₀ n₀ := by
  intro p1 p2 p3 p4 D O hO B hB R hR c Bs _ q arq nBs E h H hLB Y₀ _ π₀ fl₀ hfb ar₀ n₀
  obtain ⟨Bg, jB, πB, u, Gm, hL⟩ := (lieBase_iff O B R c q E h).1 hLB
  obtain ⟨G, _, j, πG, pb, _, _, φ, φs, jG, r, hc⟩ := GlobalTheory.T.arith_base_hermitian_vector_bundles p1 p2 p3 p4 D O hO B hB R hR c Bs q arq nBs E h H Bg jB πB u Gm hL Y₀ π₀ fl₀ hfb ar₀ n₀
  refine ⟨G, inferInstance, j, πG, pb, inferInstance, inferInstance, φ, φs, fun a i => ⟨r a i, ?_, ?_, ?_, ?_⟩⟩
  · exact (GlobalTheory.T.arith_base_hermitian_bundles_second p1 p2 p3 p4 D O hO B hB R hR c Bs q arq nBs E h H Bg jB πB u Gm hL Y₀ π₀ fl₀ hfb ar₀ n₀ G j πG pb φ φs jG r hc a i).1
  · exact (GlobalTheory.T.arith_base_hermitian_bundles_second p1 p2 p3 p4 D O hO B hB R hR c Bs q arq nBs E h H Bg jB πB u Gm hL Y₀ π₀ fl₀ hfb ar₀ n₀ G j πG pb φ φs jG r hc a i).2
  · intro σ z y y' ch e1 e2 hz
    exact GlobalTheory.T.arith_base_hermitian_bundles_third p1 p2 p3 p4 D O hO B hB R hR c Bs q arq nBs E h H Bg jB πB u Gm hL Y₀ π₀ fl₀ hfb ar₀ n₀ G j πG pb φ φs jG r hc a i σ z y y' ch e1 e2 hz
  · intro v e y z yt ch e1 e2 hy
    exact GlobalTheory.T.arith_base_hermitian_bundles_fourth p1 p2 p3 p4 D O hO B hB R hR c Bs q arq nBs E h H Bg jB πB u Gm hL Y₀ π₀ fl₀ hfb ar₀ n₀ G j πG pb φ φs jG r hc a i v e y z yt ch e1 e2 hy

end GlobalTheory.FlagCov

end
