import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsFlagBundleRankOne
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.RegularAlteration
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OfSwap2
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SwapSumSwap
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetMetricShortExactIsometric
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetMetricIsometricOfIsometry
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NontrivialIsomClassInt
import Development.AbelianVarietyTheory.Definitions.Divisors.SecondChernDegreeFubiniStudyLine
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open GlobalTheory.Cartier GlobalTheory.CovTest.SwapLine
open scoped Classical
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.VMetric

theorem isometric_grLB_tens_grLB_det : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) (E : X.Modules)
    (h : VMetric p E 2) (H : h.IsCInf) (fl : Vert.Flag E 2),
    ((VMetric.grLB fl 0 H).tens (VMetric.grLB fl 1 H)).Isometric (VMetric.det H) := by
  intro k _ X p E h H fl
  have H₀ : (h.stepMet fl 0).IsCInf := H.restrict _ _
  have H₁ : (h.stepMet fl 1).IsCInf := H.restrict _ _
  have hS₀ := VMetric.stepSeq_shortExact fl 0
  have hS₁ := VMetric.stepSeq_shortExact fl 1

  have i₂ : IsIso (VMetric.stepSeq fl 0).g :=
    hS₀.isIso_g_iff.2 (VB.isVB_zero_iff.1 (fl.isVB (Fin.castSucc 0)))
  have e₂ : (VMetric.det H₀).Isometric (VMetric.grLB fl 0 H) :=
    CurveDens.det_isometric_of_isIsometry k X p _ _ 1 (h.stepMet fl 0) (h.grMet fl 0) H₀
      (H.grMet fl 0) (asIso (VMetric.stepSeq fl 0).g) ((VMetric.isIsometry_iff _).2 (VMetric.ext
        (funext fun σ => ChTwoModel.quot_eq_map ((h.stepMet fl 0).met σ) hS₀
          (fl.isVB (Fin.castSucc 0)) _)))

  have hf : VB.IsSubbundle (VMetric.stepSeq fl 1).f := ⟨inferInstance, 1, fl.isVB_gr 1⟩
  have e₁ := VMetric.isometric_det_tens_det k X p (VMetric.stepSeq fl 1) 1 1 (h.stepMet fl 1) H₁ hS₁
    (fl.isVB (Fin.castSucc 1)) (fl.isVB_gr 1) hf

  have e₀ : (VMetric.det (H₁.restrict hf (fl.isVB (Fin.castSucc 1)))).Isometric (VMetric.det H₀) :=
    CurveDens.det_isometric_of_isIsometry k X p _ _ 1 _ (h.stepMet fl 0) _ H₀ (Iso.refl _)
      fun σ V s t y hy => by
        refine ((h.met σ).form_restrict (fl.isSubbundle _) _ s t hy).trans ?_
        refine Eq.trans ?_ ((((h.met σ).restrict (fl.isSubbundle _) (fl.isVB _)).form_restrict hf
          (fl.isVB (Fin.castSucc 1)) s t hy).trans
          ((h.met σ).form_restrict (fl.isSubbundle _) _ _ _ hy)).symm
        congr 1
        · exact congr(($(fl.step_ι 1)).app V s).symm
        · exact congr(($(fl.step_ι 1)).app V t).symm

  have i₁ : IsIso (fl.ι (Fin.succ 1)) := fl.isIso_last
  have e₃ : (VMetric.det H₁).Isometric (VMetric.det H) :=
    CurveDens.det_isometric_of_isIsometry k X p _ _ 2 (h.stepMet fl 1) h H₁ H
      (asIso (fl.ι (Fin.succ 1))) fun σ V s t y hy =>
        ((h.met σ).form_restrict (fl.isSubbundle _) _ s t hy).symm
  exact ((((e₀.trans e₂).symm).tens_right _).trans e₁).trans e₃

end GlobalTheory.VMetric
