import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsFlagBundleRankOne
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.RegularAlteration
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OfSwap2
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SwapSumSwap
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TotalEqOfNonneg
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFlagCh2EqOfAdjacent
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GradedMetricPullbackIsometric
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsContinuousCosSqAngleFunction
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRatSecDetDualTensorSupport
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetMetricRestrictionVanishingLocus
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsoOfEqualSublinesShortExact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetMetricIsometricOfIsometry
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetMetricShortExactIsoIsometric
import Development.AbelianVarietyTheory.Definitions.Divisors.SecondChernDegreeFubiniStudyLine

set_option autoImplicit false

noncomputable section

open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open GlobalTheory.Cartier GlobalTheory.CovTest.SwapLine
open scoped Classical

namespace GlobalTheory.CovTest.SwapLine

open GlobalTheory.VB GlobalTheory.VMetric GlobalTheory.CurveDens GlobalTheory.CxPts

section TwoFlags

variable {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {V : X.Modules}

def lineQuot (fl : Vert.Flag V 2) : V ⟶ fl.gr 1 :=
  have : IsIso (fl.ι (Fin.succ 1)) := fl.isIso_last
  inv (fl.ι (Fin.succ 1)) ≫ fl.π 1

theorem ι_lineQuot (fl : Vert.Flag V 2) : fl.ι (Fin.succ 1) ≫ lineQuot fl = fl.π 1 := by
  have : IsIso (fl.ι (Fin.succ 1)) := fl.isIso_last
  exact IsIso.hom_inv_id_assoc _ _

theorem line_lineQuot (fl : Vert.Flag V 2) : fl.ι 1 ≫ lineQuot fl = 0 := by
  have e : fl.step 1 ≫ fl.ι (Fin.succ 1) = fl.ι 1 := fl.step_ι 1
  rw [← e]
  exact (Category.assoc _ _ _).trans ((congrArg (fl.step 1 ≫ ·) (ι_lineQuot fl)).trans
    (Limits.cokernel.condition _))

theorem shortExact_lineQuot (fl : Vert.Flag V 2) :
    (ShortComplex.mk (fl.ι 1) (lineQuot fl) (line_lineQuot fl)).ShortExact := by
  have : IsIso (fl.ι (Fin.succ 1)) := fl.isIso_last
  exact ShortComplex.shortExact_of_iso (ShortComplex.isoMk (S₁ := stepSeq fl 1)
    (S₂ := ShortComplex.mk (fl.ι 1) (lineQuot fl) (line_lineQuot fl)) (Iso.refl _)
    (asIso (fl.ι (Fin.succ 1))) (Iso.refl _) ((Category.id_comp _).trans (fl.step_ι 1).symm)
    ((ι_lineQuot fl).trans (Category.comp_id _).symm)) (stepSeq_shortExact fl 1)

variable {h : VMetric p V 2} (H : h.IsCInf)

theorem isometric_grLB_zero (fl : Vert.Flag V 2) :
    (VMetric.det (H.restrict (fl.isSubbundle 1) (fl.isVB 1))).Isometric (grLB fl 0 H) := by
  have hS₀ := stepSeq_shortExact fl 0
  have i₂ : IsIso (stepSeq fl 0).g := hS₀.isIso_g_iff.2 (isVB_zero_iff.1 (fl.isVB (Fin.castSucc 0)))
  exact det_isometric_of_isIsometry k X p _ _ 1 (h.stepMet fl 0) (h.grMet fl 0) (H.restrict _ _)
    (H.grMet fl 0) (asIso (stepSeq fl 0).g) ((isIsometry_iff _).2 (VMetric.ext
      (funext fun σ => ChTwoModel.quot_eq_map ((h.stepMet fl 0).met σ) hS₀
        (fl.isVB (Fin.castSucc 0)) _)))

theorem isometric_grLB_one (fl : Vert.Flag V 2) :
    (VMetric.det (IsCInf.quot (S := .mk _ _ (line_lineQuot fl)) (r := 1) (s := 1) (shortExact_lineQuot fl)
      (fl.isVB 1) (fl.isVB_gr 1) H)).Isometric (grLB fl 1 H) := by
  have : IsIso (fl.ι (Fin.succ 1)) := fl.isIso_last
  exact (isometric_detQuot_and_bcInt_eq_of_iso k X p (stepSeq fl 1) (.mk _ _ (line_lineQuot fl)) 1 1
    (h.stepMet fl 1) h (H.restrict _ _) H (stepSeq_shortExact fl 1) (shortExact_lineQuot fl)
    (fl.isVB (Fin.castSucc 1)) (fl.isVB_gr 1) (fl.isVB 1) (fl.isVB_gr 1) (Iso.refl _)
    (asIso (fl.ι (Fin.succ 1))) ((Category.id_comp _).trans (fl.step_ι 1).symm)
    fun σ U s t y hy => ((h.met σ).form_restrict (fl.isSubbundle _) _ s t hy).symm).1.symm

theorem sameStep_of_eq_zero (fl fl' : Vert.Flag V 2) (hs : fl.ι 1 ≫ lineQuot fl' = 0) (j : Fin 3) :
    fl.SameStep fl' j := by
  by_cases he : j = 0 ∨ j = Fin.last 2
  · exact AdjFlag.sameStep_of_end he
  obtain rfl : j = 1 := by
    fin_cases j
    · exact absurd (.inl rfl) he
    · rfl
    · exact absurd (.inr rfl) he
  exact SameLine.eq_line X V _ _ _ _ _ _ _ _ _ _ (shortExact_lineQuot fl') (shortExact_lineQuot fl)
    (fl'.isVB_gr 1) (fl.isVB_gr 1) hs

theorem exists_ratSec_two_flags [IsIntegral X] (fl fl' : Vert.Flag V 2) (hs : fl.ι 1 ≫ lineQuot fl' ≠ 0)
    {S M Q : HermLB p} (eS : (grLB fl 0 H).Isometric S) (eM : (grLB fl' 0 H).Isometric M)
    (eQ : (grLB fl' 1 H).Isometric Q) :
    ∃ (r : (S.dual.tens Q).B.ι → X.functionFieldˣ) (hr : IsRatSec (S.dual.tens Q).B r),
      (∀ z ∈ ((S.dual.tens Q).div hr).supp,
        ∀ (Z : Scheme.{0}) (i : Z ⟶ X) [IsIntegral Z], i (genericPoint Z) = z →
          (S.restr i).Isometric (M.restr i)) ∧
      ∀ σ : k →+* ℂ, ∃ v : CxPts p σ → ℝ, IsCosSq (h.met σ) (fl.ι 1) (fl'.ι 1) v ∧
        ∀ y ∈ offSupp p σ ((S.dual.tens Q).div hr), v y < 1 ∧
          logNorm ((S.dual.tens Q).φ σ) r y = Real.log (1 - v y) / 2 := by
  have hS := shortExact_lineQuot fl'
  have hL := fl'.isVB 1
  have hL' := fl.isVB 1
  have hQ := fl'.isVB_gr 1
  have hl := fl'.isSubbundle 1
  have hl' := fl.isSubbundle 1
  have HQ := IsCInf.quot (S := .mk _ _ (line_lineQuot fl')) (r := 1) (s := 1) hS hL hQ H
  have aS := (isometric_grLB_zero H fl).trans eS
  have aM := (isometric_grLB_zero H fl').trans eM
  have aQ := (isometric_grLB_one H fl').trans eQ
  obtain ⟨r₀, hr₀, hv, hn⟩ := LineHomSec.exists_ratSec k X p _ _ _ _ (H.restrict hl' hL') HQ _ hs
  obtain ⟨r, hr, hd, he⟩ := (aS.dual.tens aQ).exists_isRatSec hr₀
  refine ⟨r, hr, fun z hz Z i _ hi => ?_, fun σ => ?_⟩
  · rw [hd] at hz
    have e := isometric_restr_of_vanishesAt k X p V _ _ _ _ _ (line_lineQuot fl') _ hS hQ hL hL' hl hl' h H
      Z i (hi ▸ hv z hz)
    exact ((aS.pull i rfl).symm.trans e.symm).trans (aM.pull i rfl)
  · obtain ⟨v, hc, -, -⟩ := exists_isCosSq k X p σ V _ _ _ (h.met σ) _ _ (H σ) hl hl' hL hL'
    refine ⟨v, hc.symm, fun y hy => ?_⟩
    rw [hd] at hy
    obtain ⟨U, t, t', ht, ht', hU⟩ := AdjFlag.exists_frames hL hL' y
    obtain ⟨n₁, n₂⟩ := hn σ y hy U t' ht' hU
    have e := AdjFlag.div_eq_one_sub hS hL hQ hL' hl hl' (h.met σ) hc ht ht' hU
    have := (div_pos n₁ (AdjFlag.form_frame_pos ((h.met σ).restrict hl' hL') ht' hU)).trans_eq e
    exact ⟨by linarith, (he σ hy).trans (n₂.trans (congrArg (Real.log · / 2) e))⟩

end TwoFlags

theorem isIso_of_sameStep {B Y : Scheme.{0}} (π : Y ⟶ B) (E : B.Modules) (n : ℕ) (flB : Vert.Flag E n)
    (fl : Vert.Flag ((Scheme.Modules.pullback π).obj E) n)
    (hF : IsFlagBundle π (fun _ : Unit => E) (fun _ => n) (fun _ => fl))
    (hs : ∀ j, fl.SameStep (flB.pull π) j) : IsIso π := by
  have key (T : Scheme.{0}) (g₁ g₂ : T ⟶ Y) (e : g₁ ≫ π = g₂ ≫ π) : g₁ = g₂ := by
    have car (g' : T ⟶ Y) (w : g' ≫ π = g₂ ≫ π) (i : Fin (n + 1)) :
        ∃ e : (Scheme.Modules.pullback g').obj (fl.F i) ≅ (flB.pull (g₂ ≫ π)).F i,
          e.hom ≫ (flB.pull (g₂ ≫ π)).ι i = (Scheme.Modules.pullback g').map (fl.ι i) ≫
            (Scheme.Modules.pullbackComp g' π).hom.app E ≫ (Scheme.Modules.pullbackCongr w).hom.app E := by
      obtain ⟨a, ha⟩ := hs i
      refine ⟨(Scheme.Modules.pullback g').mapIso a ≪≫
        (Scheme.Modules.pullbackComp g' π ≪≫ Scheme.Modules.pullbackCongr w).app (flB.F i), ?_⟩
      have nat := (Scheme.Modules.pullbackComp g' π ≪≫ Scheme.Modules.pullbackCongr w).hom.naturality (flB.ι i)
      rw [← ha, Functor.map_comp, Category.assoc]
      exact (Category.assoc _ _ _).trans (congrArg ((Scheme.Modules.pullback g').map a.hom ≫ ·) nat.symm)
    exact (hF T (g₂ ≫ π) fun _ => flB.pull (g₂ ≫ π)).unique ⟨e, fun _ => car g₁ e⟩ ⟨rfl, fun _ => car g₂ rfl⟩
  obtain ⟨s, ⟨hσ, -⟩, -⟩ := hF B (𝟙 B) fun _ => flB.pull (𝟙 B)
  exact ⟨s, key Y _ _ (by rw [Category.assoc, hσ, Category.comp_id, Category.id_comp]), hσ⟩

theorem exists_ratSec_fam5 : ∀ (k : Type) [CommRing k] (B Y : Scheme.{0}) [IsIntegral B] [IsIntegral Y] (q : B ⟶ Sp k) (p : Y ⟶ Sp k) (d : ℕ),
    IsArithVar q d → IsArithVar p (d + 1) → (∀ b : B, IsRegularLocalRing (B.presheaf.stalk b)) →
    ∀ (π : Y ⟶ B) (w : π ≫ q = p) (E : B.Modules) (h : VMetric q E 2) (H : h.IsCInf) (flB : Vert.Flag E 2)
    (fl : Vert.Flag ((Scheme.Modules.pullback π).obj E) 2), IsFlagBundle π (fun _ : Unit => E) (fun _ => 2) (fun _ => fl) →
    ∀ (A : HermLB q),
    ∃ (r : ((fam5 π w H flB fl A 0).dual.tens (fam5 π w H flB fl A 4)).B.ι → Y.functionFieldˣ) (hr : IsRatSec ((fam5 π w H flB fl A 0).dual.tens (fam5 π w H flB fl A 4)).B r),
      (∀ z ∈ (((fam5 π w H flB fl A 0).dual.tens (fam5 π w H flB fl A 4)).div hr).supp,
        ∀ (Z : Scheme.{0}) (i : Z ⟶ Y) [IsClosedImmersion i] [IsIntegral Z], i (genericPoint Z) = z →
          ((fam5 π w H flB fl A 0).restr i).Isometric ((fam5 π w H flB fl A 3).restr i)) ∧
      ∀ σ : k →+* ℂ, ∃ v : CxPts p σ → ℝ,
        GlobalTheory.CurveDens.IsCosSq ((h.pull π w).met σ) (fl.ι 1) ((Scheme.Modules.pullback π).map (flB.ι 1)) v ∧
        ∀ y ∈ offSupp p σ (((fam5 π w H flB fl A 0).dual.tens (fam5 π w H flB fl A 4)).div hr), v y < 1 ∧ logNorm (((fam5 π w H flB fl A 0).dual.tens (fam5 π w H flB fl A 4)).φ σ) r y = Real.log (1 - v y) / 2 := by
  intro k _ B Y _ _ q p d hB hY _ π w E h H flB fl hF A
  have hs : fl.ι 1 ≫ lineQuot (flB.pull π) ≠ 0 := fun hs => by
    have := isIso_of_sameStep π E 2 flB fl hF (sameStep_of_eq_zero fl _ hs)
    have e := π.homeomorph.isHomeomorph.topologicalKrullDim_eq _
    rw [hB.dim_eq, hY.dim_eq] at e
    have e' : d + 1 + 1 = d + 1 := by exact_mod_cast e
    omega
  obtain ⟨r, hr, h₁, h₂⟩ := exists_ratSec_two_flags (H.pull π w) fl (flB.pull π) hs (.refl _)
    (isometric_grLB_pull k B Y q p E 2 h H flB π w 0) (isometric_grLB_pull k B Y q p E 2 h H flB π w 1)
  exact ⟨r, hr, fun z hz Z i _ _ hi => h₁ z hz Z i hi, h₂⟩

end GlobalTheory.CovTest.SwapLine

end
