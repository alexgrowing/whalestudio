import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsFlagModelHermSum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NontrivialIsomClassInt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BcMeasUniv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetMetricIsometricOfIsometry
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GradedMetricPullbackIsometric
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagBcFiniteOfIso
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIsometryPullIdComp

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.HermFrame

namespace GlobalTheory.ChTwoModel

variable {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {σ : k →+* ℂ}

theorem quot_eq_map {S : ShortComplex X.Modules} (h : Met p σ S.X₂ (0 + 1)) (hS : S.ShortExact)
    (h₁ : IsVB S.X₁ 0) (h₃ : IsVB S.X₃ 1) [IsIso S.g] :
    h.quot hS h₁ h₃ = h.map (asIso S.g) := Met.ext_of_exists fun y => by
  obtain ⟨a, ha⟩ := Met.exists_adapted hS h₁ h₃ y
  refine ⟨a.quot, ha, ?_⟩
  rw [h.quot_G hS h₁ h₃ a ha]
  ext i j
  refine Eq.trans ?_ (((h.map (asIso S.g)).form_frame a.quot ha i j).symm.trans
    (h.form_map (asIso S.g) (a.t i) (a.t j) ha)).symm
  simp [quotGram, toBlocks₂₂, Met.gram, VBExt.AdaptedChart.frame]

theorem isometric_grLB {E : X.Modules} {h : VMetric p E 1} (H : h.IsCInf) (fl : Vert.Flag E 1) :
    (VMetric.det H).Isometric (VMetric.grLB fl 0 H) := by
  have i₁ : IsIso (fl.ι (Fin.succ 0)) := fl.isIso_last
  have hS := VMetric.stepSeq_shortExact fl 0
  have i₂ : IsIso (VMetric.stepSeq fl 0).g :=
    hS.isIso_g_iff.2 (VB.isVB_zero_iff.1 (fl.isVB (Fin.castSucc 0)))
  have H₁ : (h.stepMet fl 0).IsCInf := H.restrict _ _
  have e₁ := CurveDens.det_isometric_of_isIsometry k X p _ _ 1 (h.stepMet fl 0) h H₁ H
    (asIso (fl.ι (Fin.succ 0))) fun σ V s t y hy => ((h.met σ).form_restrict (fl.isSubbundle _) _ s t hy).symm
  have e₂ := CurveDens.det_isometric_of_isIsometry k X p _ _ 1 (h.stepMet fl 0) (h.grMet fl 0) H₁
    (H.grMet fl 0) (asIso (VMetric.stepSeq fl 0).g) ((VMetric.isIsometry_iff _).2 (VMetric.ext
      (funext fun σ => quot_eq_map ((h.stepMet fl 0).met σ) hS (fl.isVB (Fin.castSucc 0)) _)))
  exact e₁.symm.trans e₂

theorem isCh2Deg_rank_one (HC : Published.ArCalc) [IsIntegral X] (hX : IsRegSurf p) {E : X.Modules}
    {h : VMetric p E 1} (H : h.IsCInf) {a : ℝ} (ha : (VMetric.det H).IsSelfInter a) :
    h.IsCh2Deg (a / 2) := by
  refine ⟨⟨.self hX H (.ofRankOne h.isVB)⟩, fun M => (VMetric.isFlagCh2_rank_one _ _).2 ?_⟩
  have h₁ := (HC.2.2.2.2.1 k X M.Y p (M.ρ ≫ p) 1 hX.toIsArithVar M.reg.toIsArithVar M.ρ rfl
    M.generic M.finite).1 _ a ha
  have h₂ := ((VMetric.isometric_det_pull H M.ρ rfl).symm.trans
    (isometric_grLB M.cInf M.flag)).isSelfInter M.reg.toIsArithVar h₁
  convert h₂ using 1
  rw [RegCover.deg]
  ring

theorem isometric_det_ofLB (L : HermLB p) : L.Isometric (VMetric.det (VMetric.isCInf_ofLB L)) :=
  HermLB.isometric_of_chart (M := VMetric.det (VMetric.isCInf_ofLB L)) (Chart.ofLB L.isLB)
    (fun _ => le_rfl) (fun x i j _ _ => congrArg (gm (𝟙 X) x _) (TautFlag.detUnit_chartSec_eq L.isLB i j).symm)
    fun σ _ _ hy => Met.detWeight_ofWeight (L.φ σ) hy

theorem isCh2Deg_scale (HC : Published.ArCalc) [IsIntegral X] (hX : IsRegSurf p) {E : X.Modules}
    {h : VMetric p E 1} (H : h.IsCInf) {a : ℝ} (ha : (VMetric.det H).IsSelfInter a) (t : ℝ) :
    (h.scale t).IsCh2Deg (a / 2 - t / 2 * h.first_chern_integral) := by
  have h₁ := HC.2.2.1 k X p 1 hX.toIsArithVar _ a (-t / 2) ha
  have e : ((VMetric.det H).shift (fun _ => -t / 2) fun _ => rfl).Isometric (VMetric.det (H.scale t)) :=
    HermLB.isometric_of_chart (M := VMetric.det (H.scale t)) id (fun _ => le_rfl)
      (fun _ _ _ _ _ => rfl) fun σ c y hy => by
        change -Real.log ((Real.exp t : ℂ) • (h.met σ).G c y).det.re = -Real.log _ + 2 * (-t / 2)
        rw [det_smul, Fintype.card_fin, pow_one, Complex.re_ofReal_mul,
          Real.log_mul (by positivity) (det_re_pos ((h.met σ).posDef c y hy)).ne', Real.log_exp]
        ring
  convert isCh2Deg_rank_one HC hX (H.scale t) (e.isSelfInter hX.toIsArithVar h₁) using 1
  rw [VMetric.firstChernIntegral_eq_degree H]
  push_cast
  ring

theorem secondChernDegree_fubiniStudy_line (HC : Published.ArCalc) :
    haveI := ProjSpace.isRegSurf_line.isIntegral
    (HermVB.ofLB (ProjSpace.hermitianTwistingSheaf ℤ 1)).h.IsCh2Deg (1 / 4) ∧
      (HermVB.ofLB (ProjSpace.hermitianTwistingSheaf ℤ 1)).ch2Deg = 1 / 4 := by
  haveI := ProjSpace.isRegSurf_line.isIntegral
  have h := isCh2Deg_rank_one HC ProjSpace.isRegSurf_line (VMetric.isCInf_ofLB (ProjSpace.hermitianTwistingSheaf ℤ 1))
    ((isometric_det_ofLB _).isSelfInter ProjSpace.isRegSurf_line.toIsArithVar (TautFlag.selfInter HC).1)
  rw [show (1 / 2 / 2 : ℝ) = 1 / 4 by norm_num] at h
  exact ⟨h, h.ch2Deg_eq⟩

theorem eq_of_isFlagCh2 [IsIntegral X] (hX : IsRegSurf p) {E : X.Modules} {r : ℕ} {h : VMetric p E r}
    {H : h.IsCInf} {fl : Vert.Flag E r} {a b : ℝ} (ha : h.IsCh2Deg a)
    (hb : VMetric.IsFlagCh2 H fl b) : a = b := by
  let φ := (Scheme.Modules.pullbackId X).app E
  have e₁ := (VMetric.isIsometry_pull_id_comp k X p E r h).1
  have e₂ : h.IsIsometry (h.pull (𝟙 X) (Category.id_comp p)) φ.symm := fun σ V s t y hy => by
    have u (s : Γ(E, V)) : φ.hom.app V (φ.inv.app V s) = s := congr(($(φ.inv_hom_id)).app V s)
    exact (e₁ σ V _ _ y hy).symm.trans (congrArg₂ ((h.met σ).form · · y) (u s) (u t))
  have e₃ := (VMetric.isFlagCh2_ofIso k X p _ _ r h _ φ.symm H
    (H.pull (𝟙 X) (Category.id_comp p)) fl b e₂).1 hb
  have e₄ (q : X ⟶ Sp k) (e : 𝟙 X ≫ p = q) (fl') (H' : VMetric.IsFlagCh2 (H.pull (𝟙 X) e) fl' b) :
      VMetric.IsFlagCh2 (H.pull (𝟙 X) rfl) fl' b := by subst e; exact H'
  have e₅ := ha.eq_div (.self hX H fl) (e₄ _ _ _ e₃)
  rwa [show (VMetric.FlagModel.self hX H fl).deg = 1 from RegCover.deg_self hX, Nat.cast_one,
    div_one] at e₅

theorem eq_zero_of_isCh2Deg_std (HC : Published.ArCalc) {a : ℝ} :
    haveI := ProjSpace.isRegSurf_line.isIntegral
    (HermVB.std (PSpace.str ℤ 1) 2).h.IsCh2Deg a → a = 0 :=
  haveI := ProjSpace.isRegSurf_line.isIntegral
  fun ha => have ⟨_, _, _, hf⟩ := TautFlag.exists_flag HC
    eq_of_isFlagCh2 ProjSpace.isRegSurf_line ha hf

end GlobalTheory.ChTwoModel
