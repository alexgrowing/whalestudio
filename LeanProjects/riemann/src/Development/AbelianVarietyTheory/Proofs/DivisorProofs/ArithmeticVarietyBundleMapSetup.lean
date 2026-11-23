import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RegFlagged
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagBundleSectionLiftsMetric
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicLineBundleInducedArith
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagBundleMetricSetupStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSplitting
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLieBase
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithmeticModelFlagHeightFifthStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithmeticModelSmoothFlagHeightStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLocGrLat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModelBaseChangeNumberFieldStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModelChangeOfFieldPointsA
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModelChangeOfFieldPointsBStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModelChangeOfFieldPointsCStatement
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open Formalism.BasicNotions.DV Formalism.MainNotions.WeightThresholdDefs GlobalTheory.FlagAr GlobalTheory.ShFam.Pad GlobalTheory.VB GlobalTheory.ShFam GlobalTheory.TrueGeo Formalism.L2.Pj GlobalTheory.Toroidal
open Formalism.MainNotions.DIV.Cons (intO)
open GlobalTheory.ArLieBase

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.TwoLat

theorem exists_pairBase : GlobalTheory.CovTop.Hypotheses2 → GlobalTheory.CovHt.HypothesesH → GlobalTheory.Published.RegularAlteration →
    ∀ (D : D7) (O : Setup D), O.Core → ∀ R : ℝ, 2 ≤ R → ∀ c : O.s.Comp,
    ∃ (B : Scheme.{0}) (_ : IsIntegral B) (q : B ⟶ Sp (𝓞 D.what₂.LL)) (E E' : (D.host.E →+* ℂ) → B.Modules)
      (h : ∀ σ, VMetric q (E σ) (O.S.Dw.mult σ)) (h' : ∀ σ, VMetric q (E' σ) (O.S.Dw.mult σ)) (u : ∀ σ, E σ ⟶ E' σ),
      IsArithVar q (dimGr D.what₂.Tau O.N O.j) ∧ ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme B ∧ (∀ σ, (h σ).IsCInf) ∧
      (∀ σ, (h' σ).IsCInf) ∧ (∀ σ, IsoHom (h σ) (h' σ) (u σ)) ∧ PairBase O R c q E E' h h' u := by
  intro _ _ _ D O ⟨x, P, hc⟩ R hR c
  have : IsGalois ℚ D.host.E := D.host.hostE_isGalois
  obtain ⟨V, _, j, hj, hdim, hr⟩ := exists_comp O c
  obtain ⟨X, W, q, jB, πB, ρ, ⟨hq, hpb, hfin, hrg, -⟩, hn, hloc⟩ := GlobalTheory.T.model_base_change_number_field O.s.T.Z O.κ.e j hj hdim
  choose E t hvb hfr hlat using fun σ : D.host.E →+* ℂ =>
    exists_bundle O.s.T.Z O.κ.e hq hn hpb (O.S.Dw.mult σ) σ (ArIn.ind ∅) false (fun y => (hloc σ y).1)
  choose E' t' hvb' hfr' hgr using fun σ : D.host.E →+* ℂ =>
    GlobalTheory.T.model_change_of_field_points_a O.s.T.Z O.κ.e hq hn hpb (O.S.Dw.mult σ) σ (fun y => (hloc σ y).2)
  choose g hg using fun σ : D.host.E →+* ℂ =>
    GlobalTheory.T.model_change_of_field_points_b O.s.T.Z O.κ.e hq hn hpb (E σ) (E' σ) _ σ (t σ) (t' σ) (hvb σ) (hvb' σ) (hfr σ) (hfr' σ) (hlat σ)
      (hgr σ)
  let G : ∀ σ', EigMet O.s.T.Z σ' := fun σ' => x.eigMetAt σ' (some R)
  have hG : EigConj O.s.T.Z G := fun σ σ' y y' g g' τ hσ e hg => GlobalTheory.ShFam.ConjMet.eigMetAt_conj x hσ e hg τ _
  choose h hh using fun σ : D.host.E →+* ℂ =>
    GlobalTheory.T.arithmetic_model_flag_height_fifth _ _ _ _ _ _ _ _ O.s.T.Z _ O.κ.e X W q jB πB hpb (E σ) _ σ false rfl (t σ) G (hvb σ) (hfr σ) hG
  choose h' hh' using fun σ : D.host.E →+* ℂ =>
    GlobalTheory.T.arithmetic_model_flag_height_fifth _ _ _ _ _ _ _ _ O.s.T.Z _ O.κ.e X W q jB πB hpb (E' σ) _ σ false rfl (t' σ) G (hvb' σ) (hfr' σ) hG
  have hsm := O.s.T.smooth
  have hGs : ∀ σ', (G σ').SmoothOn (manifold O.s.T.Z σ') Set.univ := fun σ' =>
    ToroidalCompactificationData.smoothOn_eigMetAt_some _ _ _ _ _ _ _ x σ' R hR (ToroidalCompactificationData.hodge_smoothOn _ _ _ _ _ _ _ x σ')
  refine ⟨X, hq.isIntegral, q, E, E', h, h', g, hq, hn,
    fun σ => GlobalTheory.T.arithmetic_model_smooth_flag_height _ _ _ _ _ _ _ _ O.s.T.Z _ O.κ.e X W q jB πB hpb (E σ) _ σ false rfl (t σ) G (h σ) (hfr σ)
      hGs (hh σ),
    fun σ => GlobalTheory.T.arithmetic_model_smooth_flag_height _ _ _ _ _ _ _ _ O.s.T.Z _ O.κ.e X W q jB πB hpb (E' σ) _ σ false rfl (t' σ) G (h' σ)
      (hfr' σ) hGs (hh' σ),
    fun σ => GlobalTheory.T.model_change_of_field_points_c O.s.T.Z O.κ.e hpb (E σ) (E' σ) _ σ rfl (t σ) (t' σ) (g σ) G (h σ) (h' σ) (hvb σ) (hvb' σ)
      (hfr σ) (hfr' σ) (hg σ) (hh σ) (hh' σ),
    W, jB, πB, hpb, t, t', G, hfin, hrg.trans hr, hfr, hfr', hg, hlat, hgr, fun σ n => ?_, hh, hh'⟩
  rw [hc.hm_eq]
  rfl

end GlobalTheory.TwoLat

end
