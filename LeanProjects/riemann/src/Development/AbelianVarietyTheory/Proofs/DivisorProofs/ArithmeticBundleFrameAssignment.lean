import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRingHomOfGeneric
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagInduces
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLieFrames
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieBaseIff
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ScholzeWeinsteinB
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsFlagBundleRankOne
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.RegularAlteration
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithmeticBundleNormalBaseSetupStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IndepOfIsEigBasis
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open Formalism.BasicNotions.DV Formalism.MainNotions.WeightThresholdDefs GlobalTheory.FlagAr GlobalTheory.ShFam.Pad GlobalTheory.VB GlobalTheory.ShFam GlobalTheory.TrueGeo Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ArLieBase
open GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.ProjVar
open scoped Classical

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FlagGenPt

theorem exists_fieldMap : ∀ (P2 : Hypotheses2) (PH : HypothesesH) (RA : RegularAlteration) (SW : ScholzeWeinsteinB)
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
  intro P2 PH RA _ D O hO B _ R hR c Bs _ q arq nBs E h H Bg jB πB u Gm hL Y₀ _ π₀ fl₀ hfb ar₀ n₀ _
  have hs : GlobalTheory.FlagGenFib.jGf q π₀ jB _ hL.1 ≫ πB ≫ genStr O.s.T.Z ≫ spMap O.κ.e.toRingHom =
      GlobalTheory.FlagGenFib.sf q π₀ := hL.1.lift_snd _ _ _
  have hj := GlobalTheory.FlagGenFib.jGf_jB q π₀ jB _ hL.1
  obtain ⟨πG, φ, hsq, -, -, hgen, hA⟩ := GlobalTheory.T.arithmetic_bundle_normal_base_setup P2 PH RA D O hO (FlagAr.setB O.Y B) R hR c Bs q arq nBs E h H
    Bg jB πB u ⟨hL.1, hL.2.1, hL.2.2.1, hL.2.2.2.1⟩ hL.2.2.2.2.1 ⟨Gm, hL.2.2.2.2.2.1, hL.2.2.2.2.2.2⟩ Y₀ π₀ fl₀ hfb
    ar₀ n₀ (GlobalTheory.FlagGenFib.Gf q π₀) (GlobalTheory.FlagGenFib.jf q π₀) (GlobalTheory.FlagGenFib.sf q π₀)
    (GlobalTheory.FlagGenFib.isPullback_f q π₀) (GlobalTheory.FlagGenFib.jGf q π₀ jB _ hL.1) hj hs
  obtain ⟨r, hr⟩ := GlobalTheory.FlagSec.exists_isFrameSec D O c Bs E (fun a => (h a).isVB) Bg jB πB u hL.2.2.2.1 Y₀ π₀ fl₀
    (GlobalTheory.FlagGenFib.Gf q π₀) (GlobalTheory.FlagGenFib.jf q π₀) πG φ hgen _ hj hsq hA
  have h2 : (GlobalTheory.FlagGenFib.Gf q π₀).fromSpecStalk (genericPoint _) ≫ GlobalTheory.FlagGenFib.jGf q π₀ jB _ hL.1 ≫ πB =
      spMap φ ≫ (O.var c).X.fromSpecStalk (genericPoint (O.var c).X) ≫ (O.Φ.C c).π := by
    rw [hsq, ← Category.assoc, hgen, Category.assoc]
  refine ⟨φ, ?_, h2, fun a i hr' => ⟨r a i, hr a i hr'⟩⟩
  have h3 := congrArg (· ≫ genStr O.s.T.Z ≫ spMap O.κ.e.toRingHom) h2
  simp only [Category.assoc] at h3
  rw [hs, (O.Φ.C c).π_str] at h3
  exact h3

end GlobalTheory.FlagGenPt

end
