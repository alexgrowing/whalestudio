import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRingHomOfGeneric
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagGenericFibreIntegralStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagBundleArithmeticMetricSetupStatement
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
open CategoryTheory.Limits
set_option autoImplicit false
noncomputable section

theorem GlobalTheory.FlagGenFib.flagCover_exists : Hypotheses2 → HypothesesH → RegularAlteration → ScholzeWeinsteinB →
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
    (n₀ : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme Y₀),
  ∃ (G : Scheme.{0}) (_ : IsIntegral G) (j : G ⟶ Y₀) (πG : G ⟶ (O.var c).X)
    (_ : IsPullback j (πG ≫ (O.var c).str) (π₀ ≫ q) (spMap (algebraMap (𝓞 D.what₂.LL) D.what₂.LL)))
    (_ : IsFinite πG) (_ : Surjective πG) (φ : (O.var c).Fn →+* G.functionField)
    (_ : G.fromSpecStalk (genericPoint G) ≫ πG = spMap φ ≫ (O.var c).X.fromSpecStalk (genericPoint (O.var c).X))
    (jG : G ⟶ Bg) (r : ∀ a i, (((fl₀ a).root i).pull j).ι → G.functionFieldˣ),
    GlobalTheory.FlagCov.FlagCover (fun a => (h a).isVB) jB πB u π₀ fl₀ j πG φ jG r := by
  intro P2 PH RA SW D O hO B hB R hR c Bs _ q arq nBs E h H Bg jB πB u Gm hL Y₀ _ π₀ fl₀ hfb ar₀ n₀
  haveI hGi : IsIntegral (GlobalTheory.FlagGenFib.Gf q π₀) := GlobalTheory.T.flag_generic_fibre_integral q π₀ _ ar₀
  obtain ⟨πG, hs, hbase, hfin, hgen, hrest⟩ :=
    GlobalTheory.T.flag_bundle_arithmetic_metric_setup P2 PH RA SW D O hO B hB R hR c Bs q arq nBs E h H Bg jB πB u Gm hL Y₀ π₀ fl₀ hfb ar₀ n₀
  haveI := hfin
  obtain ⟨φ, hφ⟩ := GlobalTheory.FlagGenFib.exists_ringHom_of_generic πG hgen
  have hsur : Surjective πG := GlobalTheory.FlagGenFib.surjective_of_generic πG hgen
  have hpb : IsPullback (GlobalTheory.FlagGenFib.jf q π₀) (πG ≫ (O.var c).str) (π₀ ≫ q)
      (spMap (algebraMap (𝓞 D.what₂.LL) D.what₂.LL)) := by
    rw [hs]; exact GlobalTheory.FlagGenFib.isPullback_f q π₀
  let r : ∀ a i, (((fl₀ a).root i).pull (GlobalTheory.FlagGenFib.jf q π₀)).ι →
      (GlobalTheory.FlagGenFib.Gf q π₀).functionFieldˣ := fun a i =>
    if hr : rkB D.what₂.Tau O.N O.j a = O.S.Dw.mult (embB D a) then Classical.choose (hrest φ hφ a i hr)
    else fun _ => 1
  refine ⟨GlobalTheory.FlagGenFib.Gf q π₀, hGi, GlobalTheory.FlagGenFib.jf q π₀, πG, hpb, hfin, hsur, φ, hφ,
    GlobalTheory.FlagGenFib.jGf q π₀ jB _ hL.1, r, GlobalTheory.FlagGenFib.jGf_jB q π₀ jB _ hL.1, hbase, ?_⟩
  intro a i hr
  have e : r a i = Classical.choose (hrest φ hφ a i hr) := by simp only [r, dif_pos hr]
  rw [e]
  exact Classical.choose_spec (hrest φ hφ a i hr)

end
