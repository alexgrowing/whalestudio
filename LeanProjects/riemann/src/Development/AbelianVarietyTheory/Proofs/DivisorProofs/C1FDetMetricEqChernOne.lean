import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaF
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SubquotientCurvatureStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SecondChernFormPullback
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernAtOneEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FirstChernIsometricEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagOmegaFormReal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetMetricIsometricOfIsometry
import Development.AbelianVarietyTheory.Definitions.Divisors.SecondChernDegreeFubiniStudyLine
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FsOne

set_option autoImplicit false

noncomputable section

open Set Matrix Filter Topology
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory.HermFrame GlobalTheory.CxForm GlobalTheory.FibLine
open GlobalTheory.GoodMetric (coordVec chernPoly curvPoly)
open scoped ContDiff ComplexOrder ComplexConjugate

namespace GlobalTheory.FibTheta

section Coordinates

variable {n m : ℕ}

theorem pull_ofValues (L : V n →L[ℂ] V m) {α : V m → V m → ℂ} (hα : IsSesq α) :
    pull L (ofValues α : Alt m) = ofValues (fun ξ η => α (L ξ) (L η)) := by
  simp only [ofValues, GlobalTheory.LineForm.OmReal.sesq_expand hα (L _), AddSubmonoidClass.coe_finsetSum, Subalgebra.coe_smul,
    sym, map_sum, map_smul, map_mul, (pull_dz L _).1, (pull_dz L _).2, Finset.sum_mul, Finset.mul_sum, Finset.sum_smul,
    Finset.smul_sum, smul_mul_smul_comm, smul_smul]
  conv_lhs => enter [2, a, 2, b]; rw [Finset.sum_comm]
  conv_lhs => enter [2, a]; rw [Finset.sum_comm]
  conv_lhs => rw [Finset.sum_comm]
  conv_lhs => enter [2, c, 2, a]; rw [Finset.sum_comm]
  conv_lhs => enter [2, c]; rw [Finset.sum_comm]

theorem ofValues_add (α β : V n → V n → ℂ) : ofValues (fun ξ η => α ξ η + β ξ η) = ofValues α + ofValues β := by
  simp only [ofValues, add_smul, Finset.sum_add_distrib]

theorem ofValues_sum {ι : Type} (s : Finset ι) (c : ι → ℂ) (α : ι → V n → V n → ℂ) :
    ofValues (fun ξ η => ∑ i ∈ s, c i * α i ξ η) = ∑ i ∈ s, c i • ofValues (α i) := by
  simp only [ofValues, Finset.sum_smul, Finset.smul_sum, mul_smul]
  conv_lhs => enter [2, a]; rw [Finset.sum_comm]
  rw [Finset.sum_comm]

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E]
  {r : Type} [Fintype r] [DecidableEq r]

theorem isSesq_lineCurv {G : E → Matrix r r ℂ} {z : E} (h : MContDiffAt 2 G z) (hu : IsUnit (G z).det) (w : r → ℂ) :
    IsSesq (lineCurv G z w) := by
  have hs := isSesq_curv h hu
  constructor <;> intros <;>
    simp only [lineCurv, hs.add_left, hs.add_right, hs.smul_left, hs.smul_right, add_mulVec, smul_mulVec,
      form_add_left, form_smul_left, smul_eq_mul] <;> ring

theorem curv_chg {K G A : E → Matrix r r ℂ} {z : E} (hG : MContDiffAt 2 G z) (hu : IsUnit (G z).det)
    (hA : ∀ i j, AnalyticAt ℂ (fun w => A w i j) z) (hAu : IsUnit (A z).det)
    (hK : K =ᶠ[𝓝 z] fun w => chg (A w) (G w)) (ξ η : E) : curv K z ξ η = (A z)⁻¹ * curv G z ξ η * A z := by
  have hA2 : MContDiffAt 2 A z := fun a b => (hA a b).contDiffAt.restrict_scalars ℝ
  have hA0 : ∀ᶠ x in 𝓝 z, ∀ η, mdbar A x η = 0 := by
    have hev : ∀ᶠ x in 𝓝 z, ∀ a b, AnalyticAt ℂ (fun w => A w a b) x :=
      eventually_all.2 fun a => eventually_all.2 fun b => (hA a b).eventually_analyticAt
    filter_upwards [hev] with x hx η
    ext a b
    rw [mdbar_apply, GlobalTheory.dbar_eq_zero (hx a b).differentiableAt]
    rfl
  have hGe : K =ᶠ[𝓝 z] fun u => (A u)ᵀ * G u * (A u)ᴴᵀ := hK
  rw [curv_congr hGe, curv_changeFrame hG hu hA2 hAu hA0]

theorem lineCurv_chg {K G A : E → Matrix r r ℂ} {z : E} (hG : MContDiffAt 2 G z) (hu : IsUnit (G z).det)
    (hA : ∀ i j, AnalyticAt ℂ (fun w => A w i j) z) (hAu : IsUnit (A z).det)
    (hK : K =ᶠ[𝓝 z] fun w => chg (A w) (G w)) (w : r → ℂ) : lineCurv K z w = lineCurv G z (A z *ᵥ w) := by
  funext ξ η
  rw [lineCurv, lineCurv, curv_chg hG hu hA hAu hK, hK.eq_of_nhds, form_chg, form_chg, mulVec_mulVec, mulVec_mulVec,
    Matrix.mul_assoc, mul_nonsing_inv_cancel_left _ _ hAu]

theorem lineCurv_submatrix {r' : Type} [Fintype r'] [DecidableEq r'] (e : r' ≃ r) {G : E → Matrix r r ℂ}
    {K : E → Matrix r' r' ℂ} {z : E} (hK : K =ᶠ[𝓝 z] fun w => (G w).submatrix e e) (w : r → ℂ) :
    lineCurv K z (w ∘ e) = lineCurv G z w := by
  have f (M : Matrix r r ℂ) (u u' : r → ℂ) : form (M.submatrix e e) (u ∘ e) (u' ∘ e) = form M u u' := by
    simp only [form_eq_sum, submatrix_apply, Function.comp_apply]
    rw [← e.sum_comp]
    exact Finset.sum_congr rfl fun a _ => by rw [← e.sum_comp]
  funext ξ η
  rw [lineCurv, lineCurv, curv_congr hK, curv_submatrix_equiv, hK.eq_of_nhds, submatrix_mulVec_equiv, f,
    show (w ∘ e) ∘ e.symm = w by ext; simp, f]

theorem lineCurv_unitary (G : E → Matrix r r ℂ) (z : E) {P : Matrix r r ℂ} (hP : chg P (G z) = 1) (u : r → ℂ) (ξ η : E) :
    lineCurv G z (P *ᵥ u) ξ η = ∑ ab : r × r, (u ab.2 * conj (u ab.1) / ((∑ a, ‖u a‖ ^ 2 : ℝ) : ℂ)) *
      (kappa * (P⁻¹ * curv G z ξ η * P) ab.1 ab.2) := by
  have hu : IsUnit P.det := by
    have := congrArg det hP
    rw [det_chg, det_one] at this
    refine IsUnit.mk0 _ fun h => ?_
    simp [h] at this
  have e : curv G z ξ η *ᵥ (P *ᵥ u) = P *ᵥ ((P⁻¹ * curv G z ξ η * P) *ᵥ u) := by
    rw [mulVec_mulVec, mulVec_mulVec, Matrix.mul_assoc, mul_nonsing_inv_cancel_left _ _ hu]
  rw [lineCurv, e, ← form_chg, ← form_chg, hP]
  generalize P⁻¹ * curv G z ξ η * P = M
  have e₁ : form 1 u u = ((∑ a, ‖u a‖ ^ 2 : ℝ) : ℂ) := by
    simp [form, dotProduct, Complex.mul_conj']
  rw [e₁, Fintype.sum_prod_type]
  rw [form, one_mulVec]
  simp only [dotProduct, mulVec, Finset.sum_mul, Finset.sum_div, Finset.mul_sum, Pi.star_apply,
    Complex.star_def]
  exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring

theorem extTrace_eq_lineCurv_sub {U : Set E} {K : E → Matrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1) ℂ} {z : E}
    (h : IsPosFrame U K) (hz : z ∈ U) (ξ η : E) :
    extTrace K z ξ η = lineCurv K z (Pi.single (.inl 0) 1) ξ η - chernOne (fun w => subGram (K w)) z ξ η := by
  have hs := fun z hz => GlobalTheory.IndefiniteRowSideFullHecke.CovariantSecondFundamentalForm.isUnit_sub h z hz
  have := (SubQuotCurv.line_bundle_curvature_subquotient h hz rfl rfl (SubQuotCurv.gaussS h.isHermFrame hs hz)
    (SubQuotCurv.chernOne_add h.isHermFrame hs hz) (fun _ => 1) (fun e => one_ne_zero (congrFun e 0)) ξ η).1
  have e : incl (Fin 1) (Fin 1) *ᵥ (fun _ => (1 : ℂ)) = Pi.single (.inl 0) 1 := by
    ext (i | i) <;> simp [incl, mulVec, dotProduct, Subsingleton.elim i 0]
  rw [e] at this
  exact eq_sub_of_add_eq (by rw [add_comm]; exact eq_sub_iff_add_eq.1 this)

theorem extTrace_fibre {E' : Type} [NormedAddCommGroup E'] [NormedSpace ℂ E'] [NormedSpace ℝ E'] [IsScalarTower ℝ ℂ E']
    [CompleteSpace E] {U : Set E} {K : E → Matrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1) ℂ} (h : IsPosFrame U K) {φ : E' → E} {z : E'}
    (hz : φ z ∈ U) (hφ : AnalyticAt ℂ φ z) {A : E' → Matrix (Fin 2) (Fin 1 ⊕ Fin 1) ℂ}
    (hA : ∀ i j, AnalyticAt ℂ (fun w => A w i j) z) {g : E' → ℂ} (hg : AnalyticAt ℂ g z)
    (hK : ∀ᶠ w in 𝓝 z, K (φ w) = chg (A w) 1)
    (hl : ∀ᶠ w in 𝓝 z, ∃ t : ℂ, (fun i => A w i (.inl 0)) = t • lineVec (g w)) (ξ η : E') :
    extTrace K (φ z) (fderiv ℂ φ z ξ) (fderiv ℂ φ z η) =
      fsDens (g z) * (Complex.I / 2) * (fderiv ℂ g z ξ * conj (fderiv ℂ g z η)) := by
  have h2 := h.isHermFrame.two hz
  have hu := h.isHermFrame.isUnit _ hz
  let e : Fin 1 ⊕ Fin 1 ≃ Fin 2 := finSumFinEquiv
  have hK' : (fun w => K (φ w)) =ᶠ[𝓝 z] fun w => chg ((A w).submatrix e id) 1 := hK.mono fun w hw => by
    have := chg_submatrix (A w) 1 e id
    rw [submatrix_one_equiv, submatrix_id_id] at this
    exact hw.trans this.symm
  have hAu : IsUnit ((A z).submatrix e id).det := by
    refine IsUnit.mk0 _ fun h0 => hu.ne_zero ?_
    rw [show K (φ z) = _ from hK'.eq_of_nhds, det_chg, h0]
    simp
  have e₁ : curv K (φ z) (fderiv ℂ φ z ξ) (fderiv ℂ φ z η) = 0 := by
    rw [← curv_comp_holo h2 hu hφ.contDiffAt, curv_chg (A := fun w => (A w).submatrix e id) (mContDiffAt_const 1)
      (by simp) (fun i j => hA _ _) hAu hK',
      curv_const, Matrix.mul_zero, Matrix.zero_mul]
  have hS := h.sub.isHermFrame
  have ht := hA 0 (.inl 0)
  have hf : ∀ᶠ w in 𝓝 z, subGram (K (φ w)) default default = ((‖A w 0 (.inl 0)‖ ^ 2 * (‖g w‖ ^ 2 + 1) : ℝ) : ℂ) := by
    filter_upwards [hK, hl] with w hw ⟨t, hwt⟩
    have e0 : A w 0 (.inl 0) = t := by simpa [lineVec] using congrFun hwt 0
    change K (φ w) (.inl 0) (.inl 0) = _
    rw [hw, chg_apply, hwt, e0]
    simp [form, dotProduct, lineVec, Complex.mul_conj']
    linear_combination (g w * conj (g w)) * Complex.mul_conj' t + (‖t‖ : ℂ) ^ 2 * Complex.mul_conj' (g w)
  have ht0 : A z 0 (.inl 0) ≠ 0 := fun h0 => by
    have := (h.sub.posDef _ hz).diag_pos (i := default)
    rw [hf.self_of_nhds, h0] at this
    simp at this
  have c₁ : ContDiffAt ℝ 2 (fun w => ‖A w 0 (.inl 0)‖ ^ 2) z := (ht.contDiffAt.restrict_scalars ℝ).norm_sq ℂ
  have c₂ : ContDiffAt ℝ 2 (fun w => ‖g w‖ ^ 2 + 1) z :=
    ((hg.contDiffAt.restrict_scalars ℝ).norm_sq ℂ).add contDiffAt_const
  have p₁ : ‖A z 0 (.inl 0)‖ ^ 2 ≠ 0 := by positivity
  have p₂ (w : E') : ‖g w‖ ^ 2 + 1 ≠ 0 := by positivity
  have e₂ : chernOne (fun w => subGram (K w)) (φ z) (fderiv ℂ φ z ξ) (fderiv ℂ φ z η) =
      -(kappa * leviForm (fun w => Real.log (‖g w‖ ^ 2 + 1)) z ξ η) := by
    rw [chernOne, ← curv_comp_holo (H := fun w => subGram (K w)) (hS.two hz) (hS.isUnit _ hz) hφ.contDiffAt, ← chernOne,
      chernOne_line (c₁.mul c₂) (mul_ne_zero p₁ (p₂ z)) hf, ddc,
      leviForm_congr (u' := fun w => Real.log (‖A w 0 (.inl 0)‖ ^ 2) + Real.log (‖g w‖ ^ 2 + 1)),
      leviForm_add (c₁.log p₁) (c₂.log (p₂ z)), leviForm_log_normSq_eq_zero ht.contDiffAt ht0, zero_add]
    filter_upwards [c₁.continuousAt.eventually_ne p₁] with w hw using Real.log_mul hw (p₂ w)
  rw [extTrace_eq_lineCurv_sub h hz, lineCurv, e₁, e₂, leviForm_log_normSq_add_comp hg.contDiffAt (p₂ z)]
  have hp : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have p₃ : (‖g z‖ : ℂ) ^ 2 + 1 ≠ 0 := by exact_mod_cast p₂ z
  simp only [zero_mulVec, form, zero_dotProduct, zero_div, mul_zero, zero_sub, neg_neg, kappa, fsDens, RCLike.inner_apply]
  push_cast
  rw [add_comm 1]
  field_simp
  linear_combination (-fderiv ℂ g z ξ * conj (fderiv ℂ g z η)) * Complex.mul_conj' (g z)

end Coordinates

open CategoryTheory AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.Points GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.LineForm GlobalTheory.FibGlob
open GlobalTheory.VBExt (AdaptedChart)

section Variety

variable {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {D : ℕ}

def lineCrd {E : X.Modules} (fl : Vert.Flag E 2) (c : Chart E 2) {σ : k →+* ℂ} (y : CxPts p σ) : Fin 2 → ℂ :=
  c.crd p σ ((frameAt fl y).frame (.inl 0)) y

theorem crd_frame_eq_smul {E : X.Modules} (fl : Vert.Flag E 2) (c : Chart E 2) {σ : k →+* ℂ} {y : CxPts p σ}
    (a : AdaptedChart (lineSC fl) 1 1) (ha : y ∈ ptsIn p σ a.U) :
    ∃ t : ℂ, c.crd p σ (a.frame (.inl 0)) y = t • lineCrd fl c y := by
  refine ⟨(frameAt fl y).sub.crd p σ (a.e 0) y 0, ?_⟩
  refine (c.crd_app (frameAt fl y).sub (fl.ι 1) (a.e 0) ha (mem_frameAt fl y)).trans ?_
  funext i
  simp only [mulVec, dotProduct, Fin.sum_univ_one, of_apply, Pi.smul_apply, smul_eq_mul]
  exact mul_comm _ _

theorem lineCrd_ne_zero {E : X.Modules} (fl : Vert.Flag E 2) (c : Chart E 2) {σ : k →+* ℂ} {y : CxPts p σ}
    (hc : y ∈ ptsIn p σ c.U) : lineCrd fl c y ≠ 0 := fun h => by
  have hS := lineSC_shortExact fl
  have ha := mem_frameAt fl y
  have e := ((frameAt fl y).mid hS).tr_mulVec c ((frameAt fl y).frame (.inl 0)) ha hc
  rw [show c.crd p σ ((frameAt fl y).frame (.inl 0)) y = 0 from h, mulVec_zero] at e
  have := (congrFun e _).trans ((frameAt fl y).crd_frame hS ha (.inl 0) (.inl 0))
  simp at this

variable (h : IsRegVar p D) (σ : k →+* ℂ)

theorem isPosFrame_gram {E : X.Modules} {m : VMetric p E 2} (H : m.IsCInf) (fl : Vert.Flag E 2)
    (a : AdaptedChart (lineSC fl) 1 1) (c : AlgChart p σ D) :
    IsPosFrame (c.e.target ∩ c.e.symm ⁻¹' ptsIn p σ a.U) fun v => (m.met σ).gram a.frame (c.e.symm v) := by
  refine ⟨ChartGlue.isOpen_over c.e (isOpen_ptsIn _), fun i j v hv => ?_, fun v hv =>
    Met.posDef_gram_frame (S := lineSC fl) (r := 1) (s := 1) (m.met σ) (lineSC_shortExact fl) a hv.2⟩
  have := ((H σ).gram a.frame hv.2).mContDiffAt c (c.e.map_target hv.1) i j
  rw [c.e.right_inv hv.1] at this
  exact this.contDiffWithinAt

theorem c1F_det_metric_eq_chernOne {L : X.Modules} {m : VMetric p L 1} (H : m.IsCInf) (c : Chart L 1) (x : (h.atlas σ).Pt)
    (hc : x.pt ∈ ptsIn p σ c.U) :
    c1F h σ (VMetric.det H) x = ofValues (chernOne (fun v => (m.met σ).G c (x.ch.symm v)) x.crd) := by
  let b : Chart L 1 := pick ((VMetric.det H).φ σ).isLB x.pt
  have hb : x.pt ∈ ptsIn p σ b.U := mem_pick ((VMetric.det H).φ σ).isLB x.pt
  have e := SecondChernPull.chern_G_eq h (H σ) b c x hb hc 1
  rw [HolAtlas.chern, HolAtlas.chern, SecForm.chernAt_one_eq_ofValues, SecForm.chernAt_one_eq_ofValues] at e
  rw [e]
  change ofValues (ddc (fun v => -Real.log ((m.met σ).G b (x.ch.symm v)).det.re) x.crd) = _
  congr 1
  funext ξ η
  have hG : MContDiffAt 2 (fun v => (m.met σ).G b (x.ch.symm v)) x.crd :=
    ((H σ b _ hb).mContDiffAt x.1.1 x.2).of_le (by norm_cast)
  have hp : ∀ᶠ v in 𝓝 x.crd, ((m.met σ).G b (x.ch.symm v)).PosDef := by
    filter_upwards [(ChartGlue.isOpen_over x.ch (isOpen_ptsIn _)).mem_nhds (ChartGlue.mem_over x.ch x.2 hb)] with v hv
    exact (m.met σ).posDef b _ hv.2
  rw [chernOne_line (f := fun v => ((m.met σ).G b (x.ch.symm v)).det.re)
    (Complex.reCLM.contDiff.contDiffAt.comp _ hG.det) (det_re_pos hp.self_of_nhds).ne', ddc, ddc, leviForm_neg]
  · simp
  · filter_upwards [hp] with v hv
    exact (det_unique _).symm.trans (Complex.ext rfl (Complex.pos_iff.1 hv.det_pos).2.symm)

theorem isometric_line {E : X.Modules} {m : VMetric p E 2} (H : m.IsCInf) (fl : Vert.Flag E 2) :
    (VMetric.det (H.restrict (fl.isSubbundle 1) (fl.isVB 1))).Isometric (VMetric.grLB fl 0 H) := by
  have hS₀ := VMetric.stepSeq_shortExact fl 0
  have i₂ : IsIso (VMetric.stepSeq fl 0).g := hS₀.isIso_g_iff.2 (isVB_zero_iff.1 (fl.isVB (Fin.castSucc 0)))
  exact CurveDens.det_isometric_of_isIsometry k X p _ _ 1 (m.stepMet fl 0) (m.grMet fl 0) (H.restrict _ _)
    (H.grMet fl 0) (asIso (VMetric.stepSeq fl 0).g) ((VMetric.isIsometry_iff _).2 (VMetric.ext
      (funext fun σ => ChTwoModel.quot_eq_map ((m.stepMet fl 0).met σ) hS₀
        (fl.isVB (Fin.castSucc 0)) _)))

theorem thetaF_eq_lineCurv {E : X.Modules} {m : VMetric p E 2} (H : m.IsCInf) (fl : Vert.Flag E 2) (c : Chart E 2)
    (x : (h.atlas σ).Pt) (hc : x.pt ∈ ptsIn p σ c.U) :
    thetaF h σ H fl x = ofValues (lineCurv (fun v => (m.met σ).G c (x.ch.symm v)) x.crd (lineCrd fl c x.pt)) := by
  have := h.isIntegral
  have hS := lineSC_shortExact fl
  let a := frameAt fl x.pt
  have ha : x.pt ∈ ptsIn p σ a.U := mem_frameAt fl x.pt
  have e : x.ch.symm x.crd = x.pt := x.ch.left_inv x.2
  have hK := isPosFrame_gram σ H fl a x.1.1
  have e₁ : thetaF h σ H fl x = ofValues (lineCurv (fun v => (m.met σ).gram a.frame (x.ch.symm v)) x.crd
      (Pi.single (.inl 0) 1)) := by
    rw [thetaF, Pi.add_apply, ← c1F_eq_of_isometric k X p D h σ _ _ (isometric_line H fl), c1F_det_metric_eq_chernOne h σ _ a.sub x ha, omF,
      ← ofValues_add]
    congr 1
    funext ξ η
    exact (congrArg (_ + ·) (extTrace_eq_lineCurv_sub hK (ChartGlue.mem_over x.ch x.2 ha) ξ η)).trans
      (add_sub_cancel _ _)
  have e₂ : (Pi.single (.inl 0) 1 : Fin 1 ⊕ Fin 1 → ℂ) = (Pi.single 0 1 : Fin (1 + 1) → ℂ) ∘ finSumFinEquiv := by
    ext (i | i) <;> simp [Subsingleton.elim i 0, Pi.single_apply] <;> decide
  rw [e₁, e₂, lineCurv_submatrix (G := fun v => (m.met σ).G (a.mid hS) (x.ch.symm v)),
    lineCurv_chg (z := x.crd) (G := fun v => (m.met σ).G c (x.ch.symm v)) (A := fun v => c.tr p σ (a.mid hS) (x.ch.symm v))
      (((H σ c _ hc).mContDiffAt x.1.1 x.2).of_le (by norm_cast)), e, mulVec_single_one]
  · rfl
  · rw [e]; exact (isUnit_iff_isUnit_det _).1 ((m.met σ).posDef c _ hc).isUnit
  · exact fun i j => GlobalTheory.SCV.analyticAt_of_differentiableOn (AlgChart.holo x.1.1 _ _)
      ((ChartGlue.isOpen_over x.ch (isOpen_ptsIn _)).mem_nhds
        (ChartGlue.mem_over x.ch x.2 (mem_ptsIn_inf.2 ⟨ha, hc⟩)))
  · rw [e]; exact (isUnit_iff_isUnit_det _).1 (c.isUnit_tr _ hc ha)
  · filter_upwards [(ChartGlue.isOpen_over x.ch (isOpen_ptsIn _)).mem_nhds (ChartGlue.mem_over x.ch x.2 hc)] with v hv
    exact (m.met σ).trans c _ _ hv.2
  · filter_upwards [(ChartGlue.isOpen_over x.ch (isOpen_ptsIn _)).mem_nhds (ChartGlue.mem_over x.ch x.2 ha)] with v hv
    exact Met.gram_frame (S := lineSC fl) (r := 1) (s := 1) (m.met σ) hS _ hv.2

def curvH {E : X.Modules} (m : VMetric p E 2) (c : Chart E 2) (P : Matrix (Fin 2) (Fin 2) ℂ) (x : (h.atlas σ).Pt) :
    Matrix (Fin 2) (Fin 2) (Ev D) :=
  Matrix.of fun a b => ofValues fun ξ η =>
    kappa * (P⁻¹ * curv (fun v => (m.met σ).G c (x.ch.symm v)) x.crd ξ η * P) a b

theorem curvH_eq {E : X.Modules} (m : VMetric p E 2) (c : Chart E 2) (P : Matrix (Fin 2) (Fin 2) ℂ)
    (x : (h.atlas σ).Pt) : curvH h σ m c P x = kappa • ((algebraMap ℂ (Ev D)).mapMatrix P⁻¹ *
      (MvPolynomial.aeval sym : _ →ₐ[ℂ] Ev D).toRingHom.mapMatrix
        (curvPoly (fun v => (m.met σ).G c (x.ch.symm v)) x.crd) * (algebraMap ℂ (Ev D)).mapMatrix P) := by
  ext1 a b
  have e (F : V D → V D → Matrix (Fin 2) (Fin 2) ℂ) : (fun ξ η => kappa * (P⁻¹ * F ξ η * P) a b) =
      fun ξ η => ∑ ij : Fin 2 × Fin 2, (kappa * (P⁻¹ a ij.1 * P ij.2 b)) * F ξ η ij.1 ij.2 := by
    funext ξ η
    simp only [mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two]
    ring
  have e' (i j : Fin 2) : MvPolynomial.aeval sym (curvPoly (fun v => (m.met σ).G c (x.ch.symm v)) x.crd i j) =
      ofValues fun ξ η => curv (fun v => (m.met σ).G c (x.ch.symm v)) x.crd ξ η i j := by
    simp only [curvPoly, of_apply, ofValues, map_sum, map_mul, MvPolynomial.aeval_C, MvPolynomial.aeval_X,
      ← Algebra.smul_def]
  rw [curvH, of_apply, e, ofValues_sum]
  simp only [Matrix.smul_apply, mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two, RingHom.mapMatrix_apply, map_apply,
    AlgHom.toRingHom_eq_coe, RingHom.coe_coe, e', Algebra.smul_def, map_mul]
  ring

theorem isUnit_det_of_chg_eq_one {r : Type} [Fintype r] [DecidableEq r] {P G : Matrix r r ℂ} (hP : chg P G = 1) :
    IsUnit P.det := by
  have := congrArg Matrix.det hP
  rw [det_chg, det_one] at this
  refine IsUnit.mk0 _ fun h => ?_
  simp [h] at this

theorem coeff_two_charpolyRev {R : Type} [CommRing R] (M : Matrix (Fin 2) (Fin 2) R) :
    (-M).charpolyRev.coeff 2 = M.det := by
  have e : (-M).charpolyRev = Polynomial.C M.det * Polynomial.X ^ 2 + Polynomial.C M.trace * Polynomial.X + Polynomial.C 1 := by
    simp [Matrix.charpolyRev, det_fin_two, trace_fin_two]
    ring
  rw [e, Polynomial.coeff_add, Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_C_mul, Polynomial.coeff_C]
  simp [Polynomial.coeff_X]

theorem trace_det_curvH {E : X.Modules} {m : VMetric p E 2} (H : m.IsCInf) (fl : Vert.Flag E 2) (c : Chart E 2)
    {P : Matrix (Fin 2) (Fin 2) ℂ} (hP : IsUnit P.det) (x : (h.atlas σ).Pt) (hc : x.pt ∈ ptsIn p σ c.U) :
    (curvH h σ m c P x).trace = c1EF h σ m fl x ∧ (curvH h σ m c P x).det = c2F h σ m fl x := by
  have hi : (algebraMap ℂ (Ev D)).mapMatrix P * (algebraMap ℂ (Ev D)).mapMatrix P⁻¹ = 1 := by
    rw [← map_mul, mul_nonsing_inv _ hP, map_one]
  have e₁ : c1EF h σ m fl x = (h.atlas σ).chern ((m.met σ).G c) 1 x := by
    have hS := lineSC_shortExact fl
    have ha := mem_frameAt fl x.pt
    refine Eq.trans ?_ (SecondChernPull.chern_G_eq h (H σ) c ((frameAt fl x.pt).mid hS) x hc ha 1)
    refine SecondChernPull.chernAt_reindex (r := Fin 2) (finSumFinEquiv (m := 1) (n := 1)) ?_ 1
    filter_upwards [(ChartGlue.isOpen_over x.ch (isOpen_ptsIn _)).mem_nhds (ChartGlue.mem_over x.ch x.2 ha)] with v hv
    exact Met.gram_frame (S := lineSC fl) (r := 1) (s := 1) (m.met σ) hS _ hv.2
  rw [e₁, SecondChernPull.c2F_eq_chern_of_mem_chart h σ H fl c x hc, curvH_eq, HolAtlas.chern, HolAtlas.chern, chernAt, chernAt, chernPoly,
    chernPoly]
  generalize curvPoly (fun v => (m.met σ).G c (x.ch.symm v)) x.crd = M
  constructor
  · rw [trace_smul, trace_mul_cycle, hi, Matrix.one_mul, Matrix.coeff_charpolyRev_eq_neg_trace, trace_neg, neg_neg,
      pow_one]
    simp [trace]
  · rw [← algebraMap_smul (Ev D) kappa, det_smul, det_mul, det_mul, mul_right_comm, ← det_mul, mul_eq_one_comm.1 hi,
      det_one, one_mul, ← RingHom.map_det, coeff_two_charpolyRev, Fintype.card_fin, ← map_pow, ← Algebra.smul_def]
    rfl

end Variety

section Pull

variable {k : Type} [CommRing k] {B Y : Scheme.{0}} {q : B ⟶ Sp k} {p : Y ⟶ Sp k} {d d' : ℕ}
  (hB : IsRegVar q d) (hY : IsRegVar p d') (π : Y ⟶ B) (w : π ≫ q = p) {E : B.Modules} {m : VMetric q E 2}
  (H : m.IsCInf) (fl : Vert.Flag ((Scheme.Modules.pullback π).obj E) 2) (σ : k →+* ℂ) (c : Chart E 2)

theorem thetaF_eq_pull_lineCurv (x : (hY.atlas σ).Pt) (x' : (hB.atlas σ).Pt)
    (hx : x'.pt = PtsOver.map π w (spMap σ) x.pt) (hc : x'.pt ∈ ptsIn q σ c.U) :
    (thetaF hY σ (H.pull π w) fl x : Alt d') = pull (fderiv ℂ (x'.ch ∘ PtsOver.map π w (spMap σ) ∘ x.ch.symm) x.crd)
      (ofValues (lineCurv (fun v => (m.met σ).G c (x'.ch.symm v)) x'.crd (lineCrd fl (c.pull m.isVB π) x.pt)) : Alt d) := by
  set f : CxPts p σ → CxPts q σ := PtsOver.map π w (spMap σ) with hf
  have hm : ∀ z, (f z).1 = z.1 ≫ π := fun _ => rfl
  have hc' : f x.pt ∈ ptsIn q σ c.U := hx ▸ hc
  have hs : x.pt ∈ f ⁻¹' x'.ch.source := by rw [mem_preimage, ← hx]; exact x'.2
  have ho := ChartGlue.isOpen_over x.ch (x'.ch.open_source.preimage (continuous_of_comp hm))
  have hn := ho.mem_nhds (ChartGlue.mem_over x.ch x.2 hs)
  have hφ : AnalyticAt ℂ (x'.ch ∘ f ∘ x.ch.symm) x.crd :=
    GlobalTheory.SCV.analyticAt_of_differentiableOn (AlgChart.holo_map hm x.1.1 x'.1.1) hn
  have hv : (x'.ch ∘ f ∘ x.ch.symm) x.crd = x'.crd :=
    (congrArg (fun z => x'.ch (f z)) (x.ch.left_inv x.2)).trans (congrArg x'.ch hx.symm)
  have h2 : MContDiffAt 2 (fun v => (m.met σ).G c (x'.ch.symm v)) x'.crd :=
    ((H σ c _ hc).mContDiffAt x'.1.1 x'.2).of_le (by norm_cast)
  have hu : IsUnit ((m.met σ).G c (x'.ch.symm x'.crd)).det := by
    rw [x'.ch.left_inv x'.2]; exact (Matrix.isUnit_iff_isUnit_det _).1 ((m.met σ).posDef c _ hc).isUnit
  have he : (fun v => ((m.pull π w).met σ).G (c.pull m.isVB π) (x.ch.symm v)) =ᶠ[𝓝 x.crd]
      fun v => (m.met σ).G c (x'.ch.symm ((x'.ch ∘ f ∘ x.ch.symm) v)) := by
    filter_upwards [hn, (ChartGlue.isOpen_over x.ch ((isOpen_ptsIn c.U).preimage (continuous_of_comp hm))).mem_nhds
      (ChartGlue.mem_over x.ch x.2 (show x.pt ∈ f ⁻¹' ptsIn q σ c.U from hc'))] with v h₁ h₂
    refine ((m.met σ).pull_G π w c h₂.2).trans ?_
    exact congrArg ((m.met σ).G c) (x'.ch.left_inv h₁.2).symm
  rw [thetaF_eq_lineCurv hY σ (H.pull π w) fl (c.pull m.isVB π) x hc', pull_ofValues _ (isSesq_lineCurv h2 hu _)]
  congr 2
  funext ξ η
  rw [lineCurv, lineCurv, curv_congr he, he.eq_of_nhds,
    curv_comp_holo (H := fun v => (m.met σ).G c (x'.ch.symm v)) (hv ▸ h2) (hv ▸ hu) hφ.contDiffAt, hv]

theorem thetaF_eq_pull (x : (hY.atlas σ).Pt) (x' : (hB.atlas σ).Pt)
    (hx : x'.pt = PtsOver.map π w (spMap σ) x.pt) (hc : x'.pt ∈ ptsIn q σ c.U) {P : Matrix (Fin 2) (Fin 2) ℂ}
    (hP : chg P ((m.met σ).G c x'.pt) = 1) {u : Fin 2 → ℂ}
    (hu : ∃ t : ℂ, lineCrd fl (c.pull m.isVB π) x.pt = t • (P *ᵥ u)) :
    (thetaF hY σ (H.pull π w) fl x : Alt d') = pull (fderiv ℂ (x'.ch ∘ PtsOver.map π w (spMap σ) ∘ x.ch.symm) x.crd)
      ((∑ ab : Fin 2 × Fin 2, (u ab.2 * conj (u ab.1) / ((∑ a, ‖u a‖ ^ 2 : ℝ) : ℂ)) •
        curvH hB σ m c P x' ab.1 ab.2 : Ev d) : Alt d) := by
  obtain ⟨t, ht⟩ := hu
  have ht0 : t ≠ 0 := fun h0 => lineCrd_ne_zero fl (c.pull m.isVB π) (y := x.pt)
    (show PtsOver.map π w (spMap σ) x.pt ∈ ptsIn q σ c.U from hx ▸ hc) (by rw [ht, h0, zero_smul])
  rw [thetaF_eq_pull_lineCurv hB hY π w H fl σ c x x' hx hc, ht, lineCurv_smul _ _ _ ht0]
  congr 2
  refine Eq.trans (congrArg ofValues (funext₂ fun ξ η => lineCurv_unitary _ _ ?_ u ξ η)) (ofValues_sum _ _ _)
  rw [x'.ch.left_inv x'.2, hP]

theorem thetaF_eq_pull_qMat (x : (hY.atlas σ).Pt) (x' : (hB.atlas σ).Pt)
    (hx : x'.pt = PtsOver.map π w (spMap σ) x.pt) (hc : x'.pt ∈ ptsIn q σ c.U) {P : Matrix (Fin 2) (Fin 2) ℂ}
    (hP : chg P ((m.met σ).G c x'.pt) = 1) {z : ℂ}
    (hu : ∃ t : ℂ, lineCrd fl (c.pull m.isVB π) x.pt = t • (P *ᵥ lineVec z)) :
    (thetaF hY σ (H.pull π w) fl x : Alt d') = pull (fderiv ℂ (x'.ch ∘ PtsOver.map π w (spMap σ) ∘ x.ch.symm) x.crd)
      ((qMat (curvH hB σ m c P x') z : Ev d) : Alt d) := by
  rw [thetaF_eq_pull hB hY π w H fl σ c x x' hx hc hP hu, qMat]
  simp only [qCoef, Fin.sum_univ_two, lineVec, cons_val_zero, cons_val_one, norm_one, one_pow]
  rfl

theorem thetaF_horizontal (x : (hY.atlas σ).Pt) : ∃ β : Ev d, (thetaF hY σ (H.pull π w) fl x : Alt d') =
    pull (fderiv ℂ ((hB.atlas σ).e ((hB.atlas σ).cover (PtsOver.map π w (spMap σ) x.pt)).choose ∘
      PtsOver.map π w (spMap σ) ∘ x.ch.symm) x.crd) (β : Alt d) :=
  ⟨_, thetaF_eq_pull_lineCurv hB hY π w H fl σ (m.isVB.pick _) x
    ⟨(_, _), ((hB.atlas σ).cover (PtsOver.map π w (spMap σ) x.pt)).choose_spec⟩ rfl (m.isVB.mem_pick _)⟩

include H in

theorem extTrace_along_fibre {E' : Type} [NormedAddCommGroup E'] [NormedSpace ℂ E'] [NormedSpace ℝ E']
    [IsScalarTower ℝ ℂ E'] {b : CxPts q σ} (hc : b ∈ ptsIn q σ c.U) {P : Matrix (Fin 2) (Fin 2) ℂ}
    (hP : chg P ((m.met σ).G c b) = 1) (x : (hY.atlas σ).Pt) {f : E' → CxPts p σ} {g : E' → ℂ} {z : E'}
    (hz : f z = x.pt) (hf : ContinuousAt f z) (hφ : AnalyticAt ℂ (x.ch ∘ f) z) (hg : AnalyticAt ℂ g z)
    (hb : ∀ᶠ v in 𝓝 z, PtsOver.map π w (spMap σ) (f v) = b)
    (hl : ∀ᶠ v in 𝓝 z, ∃ t : ℂ, lineCrd fl (c.pull m.isVB π) (f v) = t • (P *ᵥ lineVec (g v))) (ξ η : E') :
    extTrace (fun v => ((m.pull π w).met σ).gram (frameAt fl x.pt).frame (x.ch.symm v)) x.crd
        (fderiv ℂ (x.ch ∘ f) z ξ) (fderiv ℂ (x.ch ∘ f) z η) =
      fsDens (g z) * (Complex.I / 2) * (fderiv ℂ g z ξ * conj (fderiv ℂ g z η)) := by
  have hPu := isUnit_det_of_chg_eq_one hP
  let a := frameAt fl x.pt
  have ha : x.pt ∈ ptsIn p σ a.U := mem_frameAt fl x.pt
  let c' := c.pull m.isVB π
  have hc' : x.pt ∈ ptsIn p σ c'.U := by
    rw [← hz]; exact show PtsOver.map π w (spMap σ) (f z) ∈ ptsIn q σ c.U from hb.self_of_nhds ▸ hc
  have hv : (x.ch ∘ f) z = x.crd := congrArg x.ch hz
  have n₁ : ∀ᶠ v in 𝓝 z, f v ∈ x.ch.source := hf.eventually_mem (x.ch.open_source.mem_nhds (hz ▸ x.2))
  have n₂ : ∀ᶠ v in 𝓝 z, f v ∈ ptsIn p σ a.U := hf.eventually_mem ((isOpen_ptsIn _).mem_nhds (hz ▸ ha))
  let A : E' → Matrix (Fin 2) (Fin 1 ⊕ Fin 1) ℂ := fun v => Matrix.of fun i j => c'.crd p σ (a.frame j) (f v) i
  have hA (i j) : AnalyticAt ℂ (fun v => A v i j) z := by
    have h₀ : AnalyticAt ℂ (fun v => c'.crd p σ (a.frame j) (x.ch.symm v) i) ((x.ch ∘ f) z) := by
      rw [hv]
      exact GlobalTheory.SCV.analyticAt_of_differentiableOn (AlgChart.holo x.1.1 _ _)
        ((ChartGlue.isOpen_over x.ch (isOpen_ptsIn _)).mem_nhds
          (ChartGlue.mem_over x.ch x.2 (mem_ptsIn_inf.2 ⟨ha, hc'⟩)))
    refine (h₀.comp hφ).congr (n₁.mono fun v hv => ?_)
    exact congrArg (fun y => c'.crd p σ (a.frame j) y i) (x.ch.left_inv hv)
  rw [← hv]
  refine extTrace_fibre (isPosFrame_gram σ (H.pull π w) fl a x.1.1) (hv ▸ ChartGlue.mem_over x.ch x.2 ha) hφ
    (A := fun v => P⁻¹ * A v) (fun i j => ?_) hg ?_ ?_ ξ η
  · simp only [mul_apply]
    exact Finset.analyticAt_fun_sum _ fun l _ => analyticAt_const.mul (hA l j)
  · filter_upwards [n₁, n₂, hb] with v h₁ h₂ h₃
    have h₄ : PtsOver.map π w (spMap σ) (f v) ∈ ptsIn q σ c.U := h₃ ▸ hc
    rw [← hP, chg_chg, mul_nonsing_inv_cancel_left _ _ hPu, ← h₃, ← (m.met σ).pull_G π w c h₄]
    exact (congrArg _ (x.ch.left_inv h₁)).trans (((m.pull π w).met σ).gram_eq c' h₄ a.frame h₂)
  · filter_upwards [n₂, hl] with v h₂ ⟨t, ht⟩
    obtain ⟨s, hs⟩ := crd_frame_eq_smul fl c' a h₂
    refine ⟨s * t, ?_⟩
    change P⁻¹ *ᵥ c'.crd p σ (a.frame (.inl 0)) (f v) = _
    rw [hs, ht, smul_smul, mulVec_smul, mulVec_mulVec, nonsing_inv_mul _ hPu, one_mulVec]

include H in

theorem pull_omF_fibre {n : ℕ} {b : CxPts q σ} (hc : b ∈ ptsIn q σ c.U) {P : Matrix (Fin 2) (Fin 2) ℂ}
    (hP : chg P ((m.met σ).G c b) = 1) (x : (hY.atlas σ).Pt) {f : V n → CxPts p σ} {g : V n → ℂ} {z : V n}
    (hz : f z = x.pt) (hf : ContinuousAt f z) (hφ : AnalyticAt ℂ (x.ch ∘ f) z) (hg : AnalyticAt ℂ g z)
    (hb : ∀ᶠ v in 𝓝 z, PtsOver.map π w (spMap σ) (f v) = b)
    (hl : ∀ᶠ v in 𝓝 z, ∃ t : ℂ, lineCrd fl (c.pull m.isVB π) (f v) = t • (P *ᵥ lineVec (g v))) :
    pull (fderiv ℂ (x.ch ∘ f) z) (omF hY σ (m.pull π w) fl x : Alt d') =
      ofValues fun ξ η => fsDens (g z) * (Complex.I / 2) * (fderiv ℂ g z ξ * conj (fderiv ℂ g z η)) := by
  have hK := isPosFrame_gram σ (H.pull π w) fl (frameAt fl x.pt) x.1.1
  have hm := ChartGlue.mem_over x.ch x.2 (mem_frameAt fl x.pt)
  refine (pull_ofValues _ (OmReal.isSesq_extTrace (hK.isHermFrame.one hm)
    (eventually_of_mem (hK.isOpen.mem_nhds hm) hK.posDef))).trans ?_
  exact congrArg (fun α => (ofValues α : Alt n))
    (funext₂ (extTrace_along_fibre hY π w H fl σ c hc hP x hz hf hφ hg hb hl))

theorem ofValues_one (ρ α : ℂ) : (ofValues fun ξ η : V 1 => ρ * (Complex.I / 2) * (α * ξ 0 * conj (α * η 0))) =
    (ρ * ((‖α‖ ^ 2 : ℝ) : ℂ)) • vol 1 := by
  simp only [ofValues, vol, Fin.sum_univ_one, Fin.prod_univ_one, smul_smul]
  congr 1
  simp [coordVec, Complex.mul_conj']
  ring

include H in

theorem pull_omF_affine {b : CxPts q σ} (hc : b ∈ ptsIn q σ c.U) {P : Matrix (Fin 2) (Fin 2) ℂ}
    (hP : chg P ((m.met σ).G c b) = 1) (x : (hY.atlas σ).Pt) {Φ : ℂ → CxPts p σ} (α β : ℂ) {z : V 1}
    (hz : Φ (z 0) = x.pt) (hf : ContinuousAt Φ (z 0)) (hφ : AnalyticAt ℂ (x.ch ∘ Φ) (z 0))
    (hb : ∀ᶠ s in 𝓝 (z 0), PtsOver.map π w (spMap σ) (Φ s) = b)
    (hl : ∀ᶠ s in 𝓝 (z 0), ∃ t : ℂ, lineCrd fl (c.pull m.isVB π) (Φ s) = t • (P *ᵥ lineVec (α * s + β))) :
    pull (fderiv ℂ (fun v : V 1 => x.ch (Φ (v 0))) z) (omF hY σ (m.pull π w) fl x : Alt d') =
      ((fsDens (α * z 0 + β) * ‖α‖ ^ 2 : ℝ) : ℂ) • (vol 1 : Alt 1) := by
  let L : V 1 →L[ℂ] ℂ := EuclideanSpace.proj 0
  have hL : HasFDerivAt (fun v : V 1 => α * v 0 + β) (α • L) z := (L.hasFDerivAt.const_mul α).add_const β
  refine (pull_omF_fibre hY π w H fl σ c hc hP x (f := fun v => Φ (v 0)) (g := fun v => α * v 0 + β) hz
    (ContinuousAt.comp (f := L) hf L.continuous.continuousAt) (AnalyticAt.comp (f := L) hφ (L.analyticAt z))
    ((analyticAt_const.mul (L.analyticAt z)).add analyticAt_const) (L.continuous.continuousAt.eventually hb)
    (L.continuous.continuousAt.eventually hl)).trans ?_
  rw [hL.fderiv, Complex.ofReal_mul, ← Subalgebra.coe_smul, ← ofValues_one]
  rfl

end Pull

section GramSchmidt

def gsUp (G : Matrix (Fin 2) (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![((√(G 0 0).re : ℝ) : ℂ)⁻¹, -G 1 0 * ((√(G 0 0).re : ℝ) : ℂ)⁻¹ * ((√G.det.re : ℝ) : ℂ)⁻¹;
    0, ((√(G 0 0).re : ℝ) : ℂ) * ((√G.det.re : ℝ) : ℂ)⁻¹]

def gsLow (G : Matrix (Fin 2) (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![((√(G 1 1).re : ℝ) : ℂ) * ((√G.det.re : ℝ) : ℂ)⁻¹, 0;
    -G 0 1 * ((√(G 1 1).re : ℝ) : ℂ)⁻¹ * ((√G.det.re : ℝ) : ℂ)⁻¹, ((√(G 1 1).re : ℝ) : ℂ)⁻¹]

variable {G : Matrix (Fin 2) (Fin 2) ℂ}

theorem sqrt_re_sq {a : ℂ} (h : 0 < a) : ((√a.re : ℝ) : ℂ) ≠ 0 ∧ ((√a.re : ℝ) : ℂ) ^ 2 = a := by
  have h₁ := Complex.pos_iff.1 h
  refine ⟨by simpa using (Real.sqrt_pos.2 h₁.1).ne', ?_⟩
  rw [← Complex.ofReal_pow, Real.sq_sqrt h₁.1.le]
  exact Complex.ext rfl h₁.2

theorem chg_gsLow (hG : G.PosDef) : chg (gsLow G) G = 1 := by
  obtain ⟨a0, ha⟩ := sqrt_re_sq (hG.diag_pos (i := 1))
  obtain ⟨d0, hd⟩ := sqrt_re_sq hG.det_pos
  have hc : conj (G 0 1) = G 1 0 := hG.isHermitian.apply 1 0
  rw [gsLow]
  generalize (√(G 1 1).re : ℝ) = a at *
  generalize (√G.det.re : ℝ) = d at *
  rw [det_fin_two] at hd
  ext i j
  rw [chg_apply, form_eq_sum]
  fin_cases i <;> fin_cases j <;> simp [Fin.sum_univ_two, hc, ← ha] <;> field_simp
  · rw [← ha] at hd
    linear_combination -hd
  · ring
  · ring

theorem lineVec_eq_gsLow (hG : G.PosDef) (x : ℂ) : ∃ t : ℂ, lineVec x =
    t • (gsLow G *ᵥ lineVec (G 1 1 / (√G.det.re : ℝ) * x + G 0 1 / (√G.det.re : ℝ))) := by
  obtain ⟨a0, ha⟩ := sqrt_re_sq (hG.diag_pos (i := 1))
  obtain ⟨d0, -⟩ := sqrt_re_sq hG.det_pos
  refine ⟨(√G.det.re : ℝ) / (√(G 1 1).re : ℝ), ?_⟩
  rw [gsLow]
  generalize (√(G 1 1).re : ℝ) = a at *
  generalize (√G.det.re : ℝ) = d at *
  funext i
  fin_cases i <;> simp [lineVec, mulVec, dotProduct, Fin.sum_univ_two, ← ha] <;> field_simp
  ring

variable {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {σ : k →+* ℂ}
  {A : CxPts p σ → Matrix (Fin 2) (Fin 2) ℂ} {y : CxPts p σ}

end GramSchmidt

section Main

variable {k : Type} [CommRing k] {B Y : Scheme.{0}} {q : B ⟶ Sp k} {p : Y ⟶ Sp k} {d d' : ℕ}
  (hB : IsRegVar q d) (hY : IsRegVar p d') (π : Y ⟶ B) (w : π ≫ q = p) {E : B.Modules} {m : VMetric q E 2}
  (H : m.IsCInf) (fl : Vert.Flag ((Scheme.Modules.pullback π).obj E) 2) (σ : k →+* ℂ) (c : Chart E 2)

end Main

end GlobalTheory.FibTheta
