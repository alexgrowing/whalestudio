import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericRootTransitionFactorsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithmeticBundleGenericSetupStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithmeticBundleGenericFibreDataStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericFibreRationalFunctionRankStatement
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

set_option autoImplicit false

namespace GlobalTheory.FlagCovDiv

theorem isRatSec_and_unitAt : Hypotheses2 → HypothesesH → RegularAlteration → ScholzeWeinsteinB →
  ∀ (D : D7) (O : Setup D) (hO : O.Core) (B : ℝ) (hB : 2 ≤ B) (R : ℝ) (hR : 2 ≤ R) (c : O.s.Comp)
    (Bs : Scheme.{0}) [IsIntegral Bs] (q : Bs ⟶ Sp (𝓞 D.what₂.LL)) (arq : IsArithVar q (dimGr D.what₂.Tau O.N O.j))
    (nBs : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme Bs) (E : D.what₂.Tau × Bool → Bs.Modules)
    (h : ∀ a, VMetric q (E a) (rkB D.what₂.Tau O.N O.j a)) (H : ∀ a, (h a).IsCInf)
    (Bg : Scheme.{0}) (jB : Bg ⟶ Bs) (πB : Bg ⟶ gen O.s.T.Z)
    (u : ∀ a, FrAssign O.s.T.Z (E a) (rkB D.what₂.Tau O.N O.j a) jB) (Gm : ∀ σ', EigMet O.s.T.Z σ')
    (hL : GlobalTheory.FlagCov.LieWit O B R c q E h jB πB u Gm)
    (Y₀ : Scheme.{0}) [IsIntegral Y₀] (π₀ : Y₀ ⟶ Bs)
    (fl₀ : ∀ a, Vert.Flag ((Scheme.Modules.pullback π₀).obj (E a)) (rkB D.what₂.Tau O.N O.j a))
    (hfb : IsFlagBundle π₀ E (rkB D.what₂.Tau O.N O.j) fl₀) (ar₀ : IsArithVar (π₀ ≫ q) (O.var c).dim)
    (n₀ : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme Y₀) (G : Scheme.{0}) [IsIntegral G] (j : G ⟶ Y₀) (πG : G ⟶ (O.var c).X)
    (pb : IsPullback j (πG ≫ (O.var c).str) (π₀ ≫ q) (spMap (algebraMap (𝓞 D.what₂.LL) D.what₂.LL)))
    [IsFinite πG] [Surjective πG] (φ : (O.var c).Fn →+* G.functionField)
    (φs : G.fromSpecStalk (genericPoint G) ≫ πG = spMap φ ≫ (O.var c).X.fromSpecStalk (genericPoint (O.var c).X))
    (jG : G ⟶ Bg) (r : ∀ a i, (((fl₀ a).root i).pull j).ι → G.functionFieldˣ)
    (hc : GlobalTheory.FlagCov.FlagCover (fun a => (h a).isVB) jB πB u π₀ fl₀ j πG φ jG r)
    (a : D.what₂.Tau × Bool) (i : Fin (rkB D.what₂.Tau O.N O.j a)),
    IsRatSec ((VMetric.grLB (fl₀ a) i ((H a).pull π₀ rfl)).B.pull j) (r a i) ∧
    ∀ ch, ∀ x ∈ ((VMetric.grLB (fl₀ a) i ((H a).pull π₀ rfl)).B.pull j).U ch, UnitAt x (φ (genAt (adlOf (O.Φ.C c) (O.met.hm c) (rootSym O.S.Dw (ArIn.ind (setB O.Y B)) (some R) (DV.tauEmb D a.1) (cond a.2 0 O.j + i))).D (πG x)) ^ 1 * r a i ch) := by
  intro _ _ _ _ D O hO B hB R hR c Bs _ q arq nBs E h H Bg jB πB u Gm hL Y₀ _ π₀ fl₀ hfb ar₀ n₀ G _ j πG pb _ _ φ φs jG r hc a i
  obtain ⟨hr, -⟩ := hL.2.2.2.2.2.2 a
  refine ⟨GlobalTheory.T.generic_root_transition_factors j (fl₀ a) i (r a i)
    (GlobalTheory.T.arithmetic_bundle_generic_setup D O hO B hB R hR c Bs q arq nBs E h H Bg jB πB u Gm hL Y₀ π₀ fl₀ hfb ar₀ n₀ G j πG pb φ φs jG r hc a i), ?_⟩
  intro ch x hx
  exact GlobalTheory.T.generic_fibre_rational_function_rank D O B R c G πG φ φs a i hr x (r a i ch)
    (GlobalTheory.T.arithmetic_bundle_generic_fibre_data D O hO B hB R hR c Bs q arq nBs E h H Bg jB πB u Gm hL Y₀ π₀ fl₀ hfb ar₀ n₀ G j πG pb φ φs jG r hc a i hr ch
      x hx)

end GlobalTheory.FlagCovDiv
