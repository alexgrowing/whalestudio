import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRingHomOfGeneric
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagInduces
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLieFrames
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieBaseIff
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ScholzeWeinsteinB
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsFlagBundleRankOne
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.RegularAlteration
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithmeticBundleFrameAssignmentStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithmeticBundleHeightLimit
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithmeticBundleRankComparisonStatement
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open Formalism.BasicNotions.DV Formalism.MainNotions.WeightThresholdDefs GlobalTheory.FlagAr GlobalTheory.ShFam.Pad GlobalTheory.VB GlobalTheory.ShFam GlobalTheory.TrueGeo Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ArLieBase
open GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.ProjVar
open scoped Classical
open CategoryTheory.Limits
set_option autoImplicit false
noncomputable section

namespace GlobalTheory.FlagCovCore

theorem fieldMap_unique {K : Type} [Field K] {X : Scheme.{0}} [IsIntegral X] (φ φ' : X.functionField →+* K)
    (h : spMap φ ≫ X.fromSpecStalk (genericPoint X) = spMap φ' ≫ X.fromSpecStalk (genericPoint X)) : φ = φ' := by
  have h' := (cancel_mono _).1 h
  have := Spec.map_injective h'
  exact congrArg CommRingCat.Hom.hom this

set_option maxHeartbeats 1000000 in

theorem exists_finite_map : ∀ (P2 : Hypotheses2) (PH : HypothesesH) (RA : RegularAlteration) (SW : ScholzeWeinsteinB)
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
    (n₀ : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme Y₀) [IsIntegral (GlobalTheory.FlagGenFib.Gf q π₀)], ∃ πG : GlobalTheory.FlagGenFib.Gf q π₀ ⟶ (O.var c).X,
      πG ≫ (O.var c).str = GlobalTheory.FlagGenFib.sf q π₀ ∧
      GlobalTheory.FlagGenFib.jGf q π₀ jB _ hL.1 ≫ πB = πG ≫ (O.Φ.C c).π ∧
      IsFinite πG ∧ πG (genericPoint _) = genericPoint (O.var c).X ∧
      ∀ φ : (O.var c).Fn →+* (GlobalTheory.FlagGenFib.Gf q π₀).functionField,
        (GlobalTheory.FlagGenFib.Gf q π₀).fromSpecStalk (genericPoint _) ≫ πG =
          spMap φ ≫ (O.var c).X.fromSpecStalk (genericPoint (O.var c).X) →
        ∀ a i (hr : rkB D.what₂.Tau O.N O.j a = O.S.Dw.mult (embB D a)),
          ∃ r : (((fl₀ a).root i).pull (GlobalTheory.FlagGenFib.jf q π₀)).ι → (GlobalTheory.FlagGenFib.Gf q π₀).functionFieldˣ,
            GlobalTheory.FlagCov.IsFrameSec (fun a => (h a).isVB) jB πB u π₀ fl₀ (GlobalTheory.FlagGenFib.jf q π₀) φ
              (GlobalTheory.FlagGenFib.jGf q π₀ jB _ hL.1) a i hr r := by
  intro P2 PH RA SW D O hO B hB R hR c Bs _ q arq nBs E h H Bg jB πB u Gm hL Y₀ _ π₀ fl₀ hfb ar₀ n₀ _
  obtain ⟨φ₀, h₁, h₂, h₃⟩ := GlobalTheory.T.arithmetic_bundle_frame_assignment P2 PH RA SW D O hO B hB R hR c Bs q arq nBs E h H Bg jB πB u Gm hL Y₀ π₀ fl₀ hfb ar₀ n₀
  obtain ⟨πG, hs, hb, hg⟩ := GlobalTheory.T.arithmetic_bundle_height_limit P2 PH RA SW D O hO B hB R hR c Bs q arq nBs E h H Bg jB πB u Gm hL Y₀ π₀ fl₀ hfb ar₀ n₀ φ₀ h₁ h₂ h₃
  have hq := GlobalTheory.T.arithmetic_bundle_rank_comparison P2 PH RA SW D O hO B hB R hR c Bs q arq nBs E h H Bg jB πB u Gm hL Y₀ π₀ fl₀ hfb ar₀ n₀ φ₀ h₁ h₂ h₃ πG hs hb hg
  have hP : IsProper (π₀ ≫ q) := by
    obtain ⟨N, i, hi, he⟩ := ar₀.isProjOver
    have := isProper_str (𝓞 D.what₂.LL) N
    rw [← he]; infer_instance
  have hsf : IsProper (GlobalTheory.FlagGenFib.sf q π₀) := by
    unfold GlobalTheory.FlagGenFib.sf
    exact MorphismProperty.of_isPullback (IsPullback.of_hasPullback _ _) hP
  have hpr : IsProper πG := by
    rw [← hs] at hsf
    exact IsProper.of_comp πG (O.var c).str
  have hfin : IsFinite πG := IsFinite.of_isProper_of_locallyQuasiFinite πG
  have hd : πG (genericPoint _) = genericPoint (O.var c).X := by
    have e : πG.base ((GlobalTheory.FlagGenFib.Gf q π₀).fromSpecStalk (genericPoint _) |>.base (IsLocalRing.closedPoint _)) =
        ((O.var c).X.fromSpecStalk (genericPoint (O.var c).X)).base ((spMap φ₀).base (IsLocalRing.closedPoint _)) :=
      congrArg (fun f => f.base (IsLocalRing.closedPoint _)) hg
    rw [Scheme.fromSpecStalk_closedPoint] at e
    rw [e, show (spMap φ₀).base (IsLocalRing.closedPoint _) = IsLocalRing.closedPoint _ from Subsingleton.elim _ _]
    exact Scheme.fromSpecStalk_closedPoint
  refine ⟨πG, hs, hb, hfin, hd, fun φ hφ => ?_⟩
  have : φ = φ₀ := fieldMap_unique φ φ₀ (hφ.symm.trans hg)
  subst this
  exact h₃
end GlobalTheory.FlagCovCore
