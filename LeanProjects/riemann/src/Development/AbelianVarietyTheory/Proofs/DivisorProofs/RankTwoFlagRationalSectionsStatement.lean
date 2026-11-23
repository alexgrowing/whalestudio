import Mathlib
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsFlagBundleRankOne
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.RegularAlteration
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OfSwap2
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SwapSumSwap
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TotalEqOfNonneg
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFlagCh2EqOfAdjacent
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GradedMetricPullbackIsometric
import Development.AbelianVarietyTheory.Definitions.Divisors.SecondChernDegreeFubiniStudyLine
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open GlobalTheory.Cartier GlobalTheory.CovTest.SwapLine
open scoped Classical

private theorem isIso_of_sameStep {B Y : Scheme.{0}} (π : Y ⟶ B) (E : B.Modules) (n : ℕ) (flB : Vert.Flag E n)
    (fl : Vert.Flag ((Scheme.Modules.pullback π).obj E) n)
    (hF : IsFlagBundle π (fun _ : Unit => E) (fun _ => n) (fun _ => fl))
    (hs : ∀ i, fl.SameStep (flB.pull π) i) : IsIso π := by
  have key (T : Scheme.{0}) (g : T ⟶ B) (a : T ⟶ Y) (w : a ≫ π = g) (i : Fin (n + 1)) :
      ∃ e : (Scheme.Modules.pullback a).obj (fl.F i) ≅ (flB.pull g).F i,
        e.hom ≫ (flB.pull g).ι i = (Scheme.Modules.pullback a).map (fl.ι i) ≫
          (Scheme.Modules.pullbackComp a π).hom.app E ≫ (Scheme.Modules.pullbackCongr w).hom.app E := by
    obtain ⟨e, he⟩ := hs i
    refine ⟨(Scheme.Modules.pullback a).mapIso e ≪≫ (Scheme.Modules.pullbackComp a π).app (flB.F i) ≪≫
      (Scheme.Modules.pullbackCongr w).app (flB.F i), ?_⟩
    have n₁ := (Scheme.Modules.pullbackComp a π).hom.naturality (flB.ι i)
    have n₂ := (Scheme.Modules.pullbackCongr w).hom.naturality (flB.ι i)
    rw [← he, Functor.map_comp, Category.assoc]
    refine (Category.assoc _ _ _).trans (congrArg _ ?_)
    refine Eq.trans ?_ ((congrArg (· ≫ (Scheme.Modules.pullbackCongr w).hom.app E) n₁).symm.trans (Category.assoc _ _ _))
    refine (Category.assoc _ _ _).trans (Eq.trans ?_ (Category.assoc _ _ _).symm)
    exact congrArg _ n₂.symm
  have : Mono π := ⟨fun {T} a b hab => (hF T (b ≫ π) fun _ => flB.pull _).unique
    ⟨hab, fun _ i => key T _ a hab i⟩ ⟨rfl, fun _ i => key T _ b rfl i⟩⟩
  obtain ⟨s, ⟨hs, -⟩, -⟩ := hF B (𝟙 B) fun _ => flB.pull _
  have : IsSplitEpi π := ⟨⟨⟨s, hs⟩⟩⟩
  exact isIso_of_mono_of_isSplitEpi π

private theorem isometric_first {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {E : X.Modules}
    {h : VMetric p E 2} (H : h.IsCInf) (fl : Vert.Flag E 2) :
    (VMetric.det (H.restrict (fl.isSubbundle 1) (fl.isVB 1))).Isometric (VMetric.grLB fl 0 H) := by
  have H₀ : (h.stepMet fl 0).IsCInf := H.restrict _ _
  have hS₀ := VMetric.stepSeq_shortExact fl 0
  have i₂ : IsIso (VMetric.stepSeq fl 0).g :=
    hS₀.isIso_g_iff.2 (VB.isVB_zero_iff.1 (fl.isVB (Fin.castSucc 0)))
  exact T.det_metric_isometric_of_isometry k X p _ _ 1 (h.stepMet fl 0) (h.grMet fl 0) H₀
      (H.grMet fl 0) (asIso (VMetric.stepSeq fl 0).g) ((VMetric.isIsometry_iff _).2 (VMetric.ext
        (funext fun σ => ChTwoModel.quot_eq_map ((h.stepMet fl 0).met σ) hS₀
          (fl.isVB (Fin.castSucc 0)) _)))

private theorem exists_ratSec_lines {k : Type} [CommRing k] {X : Scheme.{0}} [IsIntegral X] {p : X ⟶ Sp k}
    {V L Q L' : X.Modules} {l : L ⟶ V} {m : V ⟶ Q} {w : l ≫ m = 0} {l' : L' ⟶ V}
    (hS : (ShortComplex.mk l m w).ShortExact) (hL : VB.IsVB L 1) (hQ : VB.IsVB Q 1) (hL' : VB.IsVB L' 1)
    (hl : VB.IsSubbundle l) (hl' : VB.IsSubbundle l') {h : VMetric p V (1 + 1)} (H : h.IsCInf) (hs : l' ≫ m ≠ 0)
    {S M N : HermLB p} (e₂ : (VMetric.det (H.restrict hl' hL')).Isometric S)
    (e₃ : (VMetric.det (H.restrict hl hL)).Isometric M)
    (e₁ : (VMetric.det (VMetric.IsCInf.quot (S := .mk l m w) hS hL hQ H)).Isometric N) :
    ∃ (r : (S.dual.tens N).B.ι → X.functionFieldˣ) (hr : IsRatSec (S.dual.tens N).B r),
      (∀ z ∈ ((S.dual.tens N).div hr).supp,
        ∀ (Z : Scheme.{0}) (i : Z ⟶ X) [IsIntegral Z], i (genericPoint Z) = z →
          (S.restr i).Isometric (M.restr i)) ∧
      ∀ σ : k →+* ℂ, ∃ v : CxPts p σ → ℝ,
        GlobalTheory.CurveDens.IsCosSq (h.met σ) l' l v ∧
        ∀ y ∈ offSupp p σ ((S.dual.tens N).div hr), v y < 1 ∧
          logNorm ((S.dual.tens N).φ σ) r y = Real.log (1 - v y) / 2 := by
  have HQ := VMetric.IsCInf.quot (S := .mk l m w) hS hL hQ H
  obtain ⟨r, hr, hv, hn⟩ := T.exists_ratSec_det_dual_tensor_support k X p L' Q (h.restrict hl' hL')
    (VMetric.quot (S := .mk l m w) h hS hL hQ) (H.restrict hl' hL') HQ (l' ≫ m) hs
  obtain ⟨r', hr', hd, hN⟩ := (e₂.dual.tens e₁).exists_isRatSec hr
  refine ⟨r', hr', ?_, fun σ => ?_⟩
  · rw [hd]
    rintro z hz Z i _ rfl
    exact ((e₂.pull i rfl).symm.trans
      (T.det_metric_restriction_vanishing_locus k X p V L Q L' l m w l' hS hQ hL hL' hl hl' h H Z i (hv _ hz)).symm).trans (e₃.pull i rfl)
  · obtain ⟨v, hc, -, -⟩ := T.exists_continuous_cosSq_angle_function k X p σ V L L' _ (h.met σ) l l' (H σ) hl hl' hL hL'
    refine ⟨v, hc.symm, ?_⟩
    rw [hd]
    intro y hy
    obtain ⟨U, t, t', ht, ht', hU⟩ := AdjFlag.exists_frames hL hL' y
    obtain ⟨n₁, n₂⟩ := hn σ y hy U t' ht' hU
    have e := AdjFlag.div_eq_one_sub hS hL hQ hL' hl hl' (h.met σ) hc ht ht' hU
    have := div_pos n₁ (AdjFlag.form_frame_pos ((h.met σ).restrict hl' hL') ht' hU)
    have h₁ : 0 < 1 - v y := this.trans_eq e
    exact ⟨by linarith, (hN σ hy).trans (n₂.trans (congrArg (Real.log · / 2) e))⟩

private theorem isometric_second {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {E : X.Modules}
    {h : VMetric p E (1 + 1)} (H : h.IsCInf) (fl : Vert.Flag E 2) {Q : X.Modules} {m : E ⟶ Q} {w : fl.ι 1 ≫ m = 0}
    (hS : (ShortComplex.mk (fl.ι 1) m w).ShortExact) (hL : VB.IsVB (fl.F 1) 1) (hQ : VB.IsVB Q 1) :
    (VMetric.det (VMetric.IsCInf.quot (S := .mk (fl.ι 1) m w) hS hL hQ H)).Isometric (VMetric.grLB fl 1 H) := by
  have i₁ : IsIso (fl.ι (Fin.succ 1)) := fl.isIso_last
  have H₁ : (h.stepMet fl 1).IsCInf := H.restrict _ _
  have hI : (h.stepMet fl 1).IsIsometry h (asIso (fl.ι (Fin.succ 1))) := fun σ V s t y hy =>
    ((h.met σ).form_restrict (fl.isSubbundle _) _ s t hy).symm
  have he : (Iso.refl (fl.F 1)).hom ≫ fl.ι 1 = (VMetric.stepSeq fl 1).f ≫ (asIso (fl.ι (Fin.succ 1))).hom :=
    (Category.id_comp _).trans (fl.step_ι 1).symm
  have e := T.det_metric_shortExact_iso_isometric k X p (VMetric.stepSeq fl 1) (.mk (fl.ι 1) m w) 1 1 (h.stepMet fl 1) h H₁ H
      (VMetric.stepSeq_shortExact fl 1) hS (fl.isVB (Fin.castSucc 1)) (fl.isVB_gr 1) hL hQ
      (Iso.refl (fl.F 1)) (asIso (fl.ι (Fin.succ 1))) he hI
  exact e.1.symm

private theorem exists_ratSec_flags {k : Type} [CommRing k] {X : Scheme.{0}} [IsIntegral X] {p : X ⟶ Sp k}
    {V : X.Modules} {h : VMetric p V 2} (H : h.IsCInf) (fl fl' : Vert.Flag V 2) (hne : ¬ fl.SameStep fl' 1)
    {M Q : HermLB p} (hM : (VMetric.grLB fl' 0 H).Isometric M) (hQ : (VMetric.grLB fl' 1 H).Isometric Q) :
    ∃ (r : ((VMetric.grLB fl 0 H).dual.tens Q).B.ι → X.functionFieldˣ)
      (hr : IsRatSec ((VMetric.grLB fl 0 H).dual.tens Q).B r),
      (∀ z ∈ (((VMetric.grLB fl 0 H).dual.tens Q).div hr).supp,
        ∀ (Z : Scheme.{0}) (i : Z ⟶ X) [IsIntegral Z], i (genericPoint Z) = z →
          ((VMetric.grLB fl 0 H).restr i).Isometric (M.restr i)) ∧
      ∀ σ : k →+* ℂ, ∃ v : CxPts p σ → ℝ,
        GlobalTheory.CurveDens.IsCosSq (h.met σ) (fl.ι 1) (fl'.ι 1) v ∧
        ∀ y ∈ offSupp p σ (((VMetric.grLB fl 0 H).dual.tens Q).div hr), v y < 1 ∧
          logNorm (((VMetric.grLB fl 0 H).dual.tens Q).φ σ) r y = Real.log (1 - v y) / 2 := by
  have hL : VB.IsVB (fl'.F 1) 1 := fl'.isVB 1
  have hL' : VB.IsVB (fl.F 1) 1 := fl.isVB 1
  have hl := fl'.isSubbundle 1
  have hl' := fl.isSubbundle 1
  have hC : VB.IsVB (Limits.cokernel (fl'.ι 1)) 1 := fl'.isVB_cokernel 1
  have hC' : VB.IsVB (Limits.cokernel (fl.ι 1)) 1 := fl.isVB_cokernel 1
  have hS : (ShortComplex.mk (fl'.ι 1) _ (Limits.cokernel.condition (fl'.ι 1))).ShortExact :=
    { exact := ShortComplex.exact_cokernel _ }
  have hS' : (ShortComplex.mk (fl.ι 1) _ (Limits.cokernel.condition (fl.ι 1))).ShortExact :=
    { exact := ShortComplex.exact_cokernel _ }
  have hs : fl.ι 1 ≫ Limits.cokernel.π (fl'.ι 1) ≠ 0 := fun hs =>
    hne (T.iso_of_equal_sublines_shortExact X V _ _ _ _ _ _ _ _ _ _ hS hS' hC hC' hs)
  exact exists_ratSec_lines hS hL hC hL' hl hl' (h := h) H hs (isometric_first H fl)
    ((isometric_first H fl').trans hM) ((isometric_second H fl' hS hL hC).trans hQ)

theorem _root_.GlobalTheory.T.rank_two_flag_rational_sections : ∀ (k : Type) [CommRing k] (B Y : Scheme.{0}) [IsIntegral B] [IsIntegral Y] (q : B ⟶ Sp k) (p : Y ⟶ Sp k) (d : ℕ),
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
  have hne : ¬ fl.SameStep (flB.pull π) 1 := fun h₁ => by
    have : IsIso π := isIso_of_sameStep π E 2 flB fl hF fun i => by
      fin_cases i
      exacts [AdjFlag.sameStep_of_end (Or.inl rfl), h₁, AdjFlag.sameStep_of_end (Or.inr rfl)]
    have e := IsHomeomorph.topologicalKrullDim_eq _ π.homeomorph.isHomeomorph
    rw [hB.dim_eq, hY.dim_eq] at e
    have e' : d + 1 + 1 = d + 1 := by exact_mod_cast e
    omega
  obtain ⟨r, hr, h₁, h₂⟩ := exists_ratSec_flags (H.pull π w) fl (flB.pull π) hne
    (VMetric.isometric_grLB_pull k B Y q p E 2 h H flB π w 0) (VMetric.isometric_grLB_pull k B Y q p E 2 h H flB π w 1)
  exact ⟨r, hr, fun z hz Z i _ _ hi => h₁ z hz Z i hi, h₂⟩
