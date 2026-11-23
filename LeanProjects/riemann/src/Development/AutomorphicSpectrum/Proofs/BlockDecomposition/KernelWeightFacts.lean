import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.FriedrichsKernels.CalcSteps
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ZOpMemCE
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnitaryMemGLs
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LengthFunctionFactsHold

noncomputable section

open MeasureTheory Matrix Finset Filter Topology
open scoped ContDiff ComplexConjugate InnerProductSpace ZeroAtInfty

namespace GlobalTheory.CompanionTheory.KerWord

open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Fc
open GlobalTheory.CompanionTheory.RCalc (isOpen_GLs mulL mulR Rd_congr Rd_contDiffOn mapsTo_mulR gel_left gel_right gel_post)
open GlobalTheory.CompanionTheory.WaveWords (good_gel good_zOp)

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

theorem val_mem (y : G n) : y.val ∈ GLs n :=
  ((Matrix.isUnit_iff_isUnit_det _).1 y.isUnit).ne_zero

theorem mul_mem {x y : Mat n} (hx : x ∈ GLs n) (hy : y ∈ GLs n) : x * y ∈ GLs n :=
  GlobalTheory.CompanionTheory.RCalc.mul_mem_GLs hx hy

theorem inv_mem {x : Mat n} (hx : x ∈ GLs n) : x⁻¹ ∈ GLs n := by
  have h : x.det ≠ 0 := hx
  show (x⁻¹).det ≠ 0
  rw [Matrix.det_nonsing_inv, Ring.inverse_eq_inv]
  exact inv_ne_zero h

theorem inv_inv_mat {x : Mat n} (hx : x ∈ GLs n) : x⁻¹⁻¹ = x :=
  Matrix.nonsing_inv_nonsing_inv x (isUnit_iff_ne_zero.2 hx)

def toG {x : Mat n} (hx : x ∈ GLs n) : G n := Matrix.GeneralLinearGroup.mkOfDetNeZero x hx

@[simp] theorem toG_val {x : Mat n} (hx : x ∈ GLs n) : (toG hx).val = x := rfl

theorem val_inv (z : G n) : (z⁻¹ : G n).val = z.val⁻¹ := Matrix.coe_units_inv z

theorem lg_val_le (hL : LgFacts) (z : G n) {x : Mat n} (hx : x ∈ GLs n) :
    lg z.val ≤ lg ((z⁻¹ : G n).val * x) + lg x := by
  obtain ⟨hsub, hinv, -⟩ := hL n
  have hy : (z⁻¹ : G n).val * x ∈ GLs n := mul_mem (val_mem _) hx
  have e : ((z⁻¹ : G n).val * x) * x⁻¹ = (z⁻¹ : G n).val := by
    rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv x (isUnit_iff_ne_zero.2 hx), Matrix.mul_one]
  have h1 := hsub _ hy _ (inv_mem hx)
  have h2 : lg (z⁻¹ : G n).val = lg z.val := by rw [val_inv, hinv _ (val_mem z)]
  rw [e, hinv x hx, h2] at h1
  exact h1

theorem fderiv_far (hL : LgFacts) {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W] {K : Mat n → W} {R : ℝ}
    (hR : ∀ y ∈ GLs n, R < lg y → K y = 0) {y : Mat n} (hy : y ∈ GLs n) (h : R < lg y) : fderiv ℝ K y = 0 := by
  have hc : ContinuousOn (lg : Mat n → ℝ) (GLs n) := (hL n).2.2.2.1.continuousOn
  have ho : IsOpen (GLs n ∩ lg ⁻¹' Set.Ioi R) := hc.isOpen_inter_preimage isOpen_GLs isOpen_Ioi
  have he : K =ᶠ[𝓝 y] fun _ => 0 :=
    eventually_of_mem (ho.mem_nhds ⟨hy, h⟩) fun a ha => hR a ha.1 ha.2
  rw [he.fderiv_eq]
  simp

theorem cpt_Rd (hL : LgFacts) {W : Type} [NormedAddCommGroup W] [NormedSpace ℂ W] {K : Mat n → W} (hK : Cpt K)
    (X : Mat n) : Cpt (Rd X K) := by
  obtain ⟨R, hR⟩ := hK
  refine ⟨R, fun y hy h => ?_⟩
  simp [Rd, fderiv_far hL hR hy h]

def mulLL : Mat n →L[ℝ] Mat n →L[ℝ] Mat n :=
  LinearMap.toContinuousLinearMap
    { toFun := mulL
      map_add' := fun a b => by ext1 v; simp [Matrix.add_mul]
      map_smul' := fun c a => by ext1 v; simp }

@[simp] theorem mulLL_apply (a : Mat n) : mulLL a = mulL a := rfl

section Core

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]

def evL : V →L[ℝ] (V →L[ℂ] V) →L[ℝ] V := (ContinuousLinearMap.restrictScalarsL ℂ V V ℝ ℝ).flip

@[simp] theorem evL_apply (v : V) (A : V →L[ℂ] V) : evL v A = A v := rfl

abbrev CL (P W : Type) [NormedAddCommGroup P] [NormedSpace ℝ P] [NormedAddCommGroup W] [NormedSpace ℝ W] : Type :=
  P →L[ℝ] W

def Dk (K : Mat n → (V →L[ℂ] V)) (f : Mat n → V) (x : Mat n) (z : G n) : CL (Mat n) V :=
  (evL (f z.val)).comp ((fderiv ℝ K ((z⁻¹ : G n).val * x)).comp (mulL (z⁻¹ : G n).val))

theorem Dk_apply (K : Mat n → (V →L[ℂ] V)) (f : Mat n → V) (x : Mat n) (z : G n) (v : Mat n) :
    Dk K f x z v = fderiv ℝ K ((z⁻¹ : G n).val * x) ((z⁻¹ : G n).val * v) (f z.val) := rfl

theorem Dk_eq_zero {K : Mat n → (V →L[ℂ] V)} (f : Mat n → V) {x : Mat n} {z : G n}
    (h : fderiv ℝ K ((z⁻¹ : G n).val * x) = 0) : Dk K f x z = 0 := by
  refine ContinuousLinearMap.ext fun v => ?_
  rw [Dk_apply, h]
  rfl

theorem continuous_valinv : Continuous fun z : G n => (z⁻¹ : G n).val :=
  Units.continuous_val.comp continuous_inv

theorem continuousOn_Dk {K : Mat n → (V →L[ℂ] V)} (hK : ContDiffOn ℝ ∞ K (GLs n)) {f : Mat n → V}
    (hf : ContinuousOn f (GLs n)) :
    ContinuousOn (fun p : Mat n × G n => Dk K f p.1 p.2) (GLs n ×ˢ Set.univ) := by
  have h1 : ContinuousOn (fderiv ℝ K) (GLs n) := hK.continuousOn_fderiv_of_isOpen isOpen_GLs (by simp)
  have h2 : Continuous fun p : Mat n × G n => (p.2⁻¹ : G n).val * p.1 :=
    (continuous_valinv.comp continuous_snd).mul continuous_fst
  have h3 : ContinuousOn (fun p : Mat n × G n => fderiv ℝ K ((p.2⁻¹ : G n).val * p.1)) (GLs n ×ˢ Set.univ) :=
    h1.comp h2.continuousOn fun p hp => mul_mem (val_mem _) hp.1
  have h4 : Continuous fun p : Mat n × G n => mulL (p.2⁻¹ : G n).val :=
    mulLL.continuous.comp (continuous_valinv.comp continuous_snd)
  have h5 : Continuous fun p : Mat n × G n => evL (f p.2.val) := by
    refine evL.continuous.comp ?_
    exact (hf.comp_continuous Units.continuous_val val_mem).comp continuous_snd
  exact h5.continuousOn.clm_comp (h3.clm_comp h4.continuousOn)

variable [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure]

def Lk (K : Mat n → (V →L[ℂ] V)) (f : Mat n → V) : Mat n → V :=
  fun x => ∫ z : G n, K ((z⁻¹ : G n).val * x) (f z.val) ∂μ

include μ in
theorem integrable_far (hL : LgFacts) {W : Type} [NormedAddCommGroup W] {Φ : G n → W} (hc : Continuous Φ) (R : ℝ)
    (h : ∀ z : G n, R < lg z.val → Φ z = 0) : Integrable Φ μ := by
  refine hc.integrable_of_hasCompactSupport (HasCompactSupport.of_support_subset_isCompact ((hL n).2.2.2.2.1 R) ?_)
  intro z hz
  by_contra hlt
  exact hz (h z (not_le.1 hlt))

theorem integrable_Lk (hL : LgFacts) {K : Mat n → (V →L[ℂ] V)} (hK : ContinuousOn K (GLs n)) (hc : Cpt K)
    {f : Mat n → V} (hf : ContinuousOn f (GLs n)) {x : Mat n} (hx : x ∈ GLs n) :
    Integrable (fun z : G n => K ((z⁻¹ : G n).val * x) (f z.val)) μ := by
  obtain ⟨R, hR⟩ := hc
  have h1 : Continuous fun z : G n => K ((z⁻¹ : G n).val * x) :=
    hK.comp_continuous (continuous_valinv.mul continuous_const) fun z => mul_mem (val_mem _) hx
  have h2 : Continuous fun z : G n => f z.val := hf.comp_continuous Units.continuous_val val_mem
  refine integrable_far μ hL (h1.clm_apply h2) (R + lg x) fun z hz => ?_
  have := lg_val_le hL z hx
  rw [hR _ (mul_mem (val_mem _) hx) (by linarith)]
  simp

theorem integrable_Dk (hL : LgFacts) {K : Mat n → (V →L[ℂ] V)} (hK : ContDiffOn ℝ ∞ K (GLs n)) (hc : Cpt K)
    {f : Mat n → V} (hf : ContinuousOn f (GLs n)) {x : Mat n} (hx : x ∈ GLs n) :
    Integrable (Dk K f x) μ := by
  obtain ⟨R, hR⟩ := hc
  have h1 : Continuous (fun z : G n => Dk K f x z) :=
    (continuousOn_Dk hK hf).comp_continuous (f := fun z : G n => (x, z)) (continuous_const.prodMk continuous_id)
      fun z => ⟨hx, Set.mem_univ _⟩
  refine integrable_far μ hL h1 (R + lg x) fun z hz => ?_
  have := lg_val_le hL z hx
  exact Dk_eq_zero f (fderiv_far hL hR (mul_mem (val_mem z⁻¹) hx) (by linarith))

theorem hasFDerivAt_integrand {K : Mat n → (V →L[ℂ] V)} (hK : ContDiffOn ℝ ∞ K (GLs n)) (f : Mat n → V) {x : Mat n}
    (hx : x ∈ GLs n) (z : G n) :
    HasFDerivAt (fun x' => K ((z⁻¹ : G n).val * x') (f z.val)) (Dk K f x z) x := by
  have hy : (z⁻¹ : G n).val * x ∈ GLs n := mul_mem (val_mem _) hx
  have h1 : HasFDerivAt K (fderiv ℝ K ((z⁻¹ : G n).val * x)) ((z⁻¹ : G n).val * x) :=
    (GlobalTheory.CompanionTheory.RCalc.differentiableAt_of_smooth hK hy).hasFDerivAt
  have h2 : HasFDerivAt (fun x' : Mat n => mulL (z⁻¹ : G n).val x') (mulL (z⁻¹ : G n).val) x :=
    (mulL (z⁻¹ : G n).val).hasFDerivAt
  have h3 := HasFDerivAt.comp x (g := K) h1 h2
  exact (evL (f z.val)).hasFDerivAt.comp x h3

theorem hasFDerivAt_Lk [CompleteSpace V] (hL : LgFacts) {K : Mat n → (V →L[ℂ] V)} (hK : ContDiffOn ℝ ∞ K (GLs n))
    (hc : Cpt K) {f : Mat n → V} (hf : ContinuousOn f (GLs n)) {x₀ : Mat n} (hx₀ : x₀ ∈ GLs n) :
    HasFDerivAt (Lk μ K f) (∫ z, Dk K f x₀ z ∂μ) x₀ := by
  haveI : ProperSpace (Mat n) := FiniteDimensional.proper ℝ (Mat n)
  obtain ⟨r, hr, hB⟩ := Metric.nhds_basis_closedBall.mem_iff.1 (isOpen_GLs.mem_nhds hx₀)
  have hBc : IsCompact (Metric.closedBall x₀ r) := isCompact_closedBall x₀ r
  obtain ⟨R₀, hR₀⟩ := (hBc.image_of_continuousOn ((hL n).2.2.2.1.continuousOn.mono hB)).bddAbove
  have hlg : ∀ x ∈ Metric.closedBall x₀ r, lg x ≤ R₀ := fun x hx => hR₀ ⟨x, hx, rfl⟩
  have hK' := hc
  obtain ⟨R, hR⟩ := hc
  have hC : IsCompact {z : G n | lg z.val ≤ R + R₀} := (hL n).2.2.2.2.1 (R + R₀)
  obtain ⟨M, hM⟩ := (hBc.prod hC).exists_bound_of_continuousOn
    ((continuousOn_Dk hK hf).mono fun p hp => ⟨hB hp.1, Set.mem_univ _⟩)
  have hfar : ∀ x ∈ Metric.closedBall x₀ r, ∀ z : G n, z ∉ {z : G n | lg z.val ≤ R + R₀} → Dk K f x z = 0 := by
    intro x hx z hz
    have h1 := lg_val_le hL z (hB hx)
    have h2 := hlg x hx
    have h3 : R + R₀ < lg z.val := not_le.1 hz
    exact Dk_eq_zero f (fderiv_far hL hR (mul_mem (val_mem z⁻¹) (hB hx)) (by linarith))
  refine hasFDerivAt_integral_of_dominated_of_fderiv_le
    (F := fun x (z : G n) => K ((z⁻¹ : G n).val * x) (f z.val)) (F' := Dk K f)
    (bound := {z : G n | lg z.val ≤ R + R₀}.indicator fun _ => M)
    (Metric.closedBall_mem_nhds x₀ hr) ?_ ?_ ?_ ?_ ?_ ?_
  · exact eventually_of_mem (Metric.closedBall_mem_nhds x₀ hr) fun x hx =>
      (integrable_Lk μ hL hK.continuousOn hK' hf (hB hx)).aestronglyMeasurable
  · exact integrable_Lk μ hL hK.continuousOn hK' hf hx₀
  · exact (integrable_Dk μ hL hK hK' hf hx₀).aestronglyMeasurable
  · refine ae_of_all _ fun z x hx => ?_
    by_cases hz : z ∈ {z : G n | lg z.val ≤ R + R₀}
    · rw [Set.indicator_of_mem hz]
      exact hM (x, z) ⟨hx, hz⟩
    · rw [Set.indicator_of_notMem hz, hfar x hx z hz, norm_zero]
  · exact (integrable_indicator_iff hC.measurableSet).2 (integrableOn_const hC.measure_lt_top.ne)
  · exact ae_of_all _ fun z x hx => hasFDerivAt_integrand hK f (hB hx) z

theorem Rd_Lk [CompleteSpace V] (hL : LgFacts) {K : Mat n → (V →L[ℂ] V)} (hK : ContDiffOn ℝ ∞ K (GLs n))
    (hc : Cpt K) {f : Mat n → V} (hf : ContinuousOn f (GLs n)) (X : Mat n) {x : Mat n} (hx : x ∈ GLs n) :
    Rd X (Lk μ K f) x = Lk μ (Rd X K) f x := by
  have e1 : fderiv ℝ (Lk μ K f) x = (∫ z, Dk K f x z ∂μ) := (hasFDerivAt_Lk μ hL hK hc hf hx).fderiv
  have e2 : (∫ z, Dk K f x z ∂μ : CL (Mat n) V) (x * X) = ∫ z, Dk K f x z (x * X) ∂μ :=
    ContinuousLinearMap.integral_apply (integrable_Dk μ hL hK hc hf hx) _
  have e3 : fderiv ℝ (Lk μ K f) x (x * X) = ∫ z, Dk K f x z (x * X) ∂μ := by
    rw [e1]; exact e2
  refine e3.trans (integral_congr_ae (ae_of_all _ fun z => ?_))
  simp only [Dk_apply, Rd, Matrix.mul_assoc]

def Rel (f : Mat n → V) (K : Mat n → (V →L[ℂ] V)) (B : Mat n → V) : Prop :=
  ContDiffOn ℝ ∞ K (GLs n) ∧ Cpt K ∧ ∀ x ∈ GLs n, B x = Lk μ K f x

variable {μ}

theorem Rel.Rd [CompleteSpace V] (hL : LgFacts) {f : Mat n → V} (hf : ContinuousOn f (GLs n))
    {K : Mat n → (V →L[ℂ] V)} {B : Mat n → V} (h : Rel μ f K B) (X : Mat n) :
    Rel μ f (PositivityTheory.RgBcC.Rd X K) (PositivityTheory.RgBcC.Rd X B) :=
  ⟨Rd_contDiffOn X h.1, cpt_Rd hL h.2.1 X, fun _ hx =>
    (Rd_congr X (fun _ hy => h.2.2 _ hy) hx).trans (Rd_Lk μ hL h.1 h.2.1 hf X hx)⟩

theorem Rel.zero (f : Mat n → V) : Rel μ f 0 0 := by
  refine ⟨contDiffOn_const, ⟨0, fun _ _ _ => rfl⟩, fun x _ => ?_⟩
  simp [Lk]

theorem Rel.add (hL : LgFacts) {f : Mat n → V} (hf : ContinuousOn f (GLs n))
    {K K' : Mat n → (V →L[ℂ] V)} {B B' : Mat n → V} (h : Rel μ f K B) (h' : Rel μ f K' B') :
    Rel μ f (K + K') (B + B') := by
  refine ⟨h.1.add h'.1, ?_, fun x hx => ?_⟩
  · obtain ⟨R, hR⟩ := h.2.1
    obtain ⟨R', hR'⟩ := h'.2.1
    refine ⟨max R R', fun y hy hl => ?_⟩
    simp [hR y hy (lt_of_le_of_lt (le_max_left _ _) hl), hR' y hy (lt_of_le_of_lt (le_max_right _ _) hl)]
  · rw [Pi.add_apply, h.2.2 x hx, h'.2.2 x hx]
    simp only [Lk, Pi.add_apply, ContinuousLinearMap.add_apply]
    exact (integral_add (integrable_Lk μ hL h.1.continuousOn h.2.1 hf hx)
      (integrable_Lk μ hL h'.1.continuousOn h'.2.1 hf hx)).symm

theorem Rel.smul {f : Mat n → V} {K : Mat n → (V →L[ℂ] V)} {B : Mat n → V} (c : ℂ) (h : Rel μ f K B) :
    Rel μ f (c • K) (c • B) := by
  refine ⟨h.1.const_smul c, ?_, fun x hx => ?_⟩
  · obtain ⟨R, hR⟩ := h.2.1
    exact ⟨R, fun y hy hl => by simp [hR y hy hl]⟩
  · rw [Pi.smul_apply, h.2.2 x hx]
    simp only [Lk, Pi.smul_apply, ContinuousLinearMap.smul_apply]
    exact (integral_smul c _).symm

theorem Rel.sum (hL : LgFacts) {f : Mat n → V} (hf : ContinuousOn f (GLs n)) {ι : Type} (s : Finset ι)
    {K : ι → Mat n → (V →L[ℂ] V)} {B : ι → Mat n → V} (h : ∀ i, Rel μ f (K i) (B i)) :
    Rel μ f (∑ i ∈ s, K i) (∑ i ∈ s, B i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using Rel.zero f
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact (h a).add hL hf ih

theorem Rel.Eu [CompleteSpace V] (hL : LgFacts) {f : Mat n → V} (hf : ContinuousOn f (GLs n))
    {K : Mat n → (V →L[ℂ] V)} {B : Mat n → V} (h : Rel μ f K B) (s : Bool) (a b : Fin n) :
    Rel μ f (PositivityTheory.RgBcC.Eu s a b K) (PositivityTheory.RgBcC.Eu s a b B) :=
  Rel.smul _ (Rel.add hL hf (h.Rd hL hf _) (Rel.smul _ (h.Rd hL hf _)))

theorem Rel.Epow [CompleteSpace V] (hL : LgFacts) {f : Mat n → V} (hf : ContinuousOn f (GLs n))
    {K : Mat n → (V →L[ℂ] V)} {B : Mat n → V} (h : Rel μ f K B) (s : Bool) (m : ℕ) :
    ∀ a b : Fin n, Rel μ f (PositivityTheory.RgBcC.Epow s m a b K) (PositivityTheory.RgBcC.Epow s m a b B) := by
  induction m with
  | zero =>
    intro a b
    by_cases e : a = b
    · simpa [PositivityTheory.RgBcC.Epow, e] using h
    · simpa [PositivityTheory.RgBcC.Epow, e] using Rel.zero f
  | succ m ih =>
    intro a b
    exact Rel.sum hL hf Finset.univ fun c => (ih c b).Eu hL hf s a c

theorem Rel.gel [CompleteSpace V] (hL : LgFacts) {f : Mat n → V} (hf : ContinuousOn f (GLs n))
    {K : Mat n → (V →L[ℂ] V)} {B : Mat n → V} (h : Rel μ f K B) (s : Bool) (m : ℕ) :
    Rel μ f (PositivityTheory.RgBcC.gel s m K) (PositivityTheory.RgBcC.gel s m B) :=
  Rel.sum hL hf Finset.univ fun a => h.Epow hL hf s m a a

theorem Rel.zOp [CompleteSpace V] (hL : LgFacts) {f : Mat n → V} (hf : ContinuousOn f (GLs n))
    {K : Mat n → (V →L[ℂ] V)} {B : Mat n → V} (h : Rel μ f K B) (w : List (Bool × ℕ)) :
    Rel μ f (PositivityTheory.RgBcC.zOp w K) (PositivityTheory.RgBcC.zOp w B) := by
  induction w with
  | nil => exact h
  | cons p w ih => exact ih.gel hL hf p.1 p.2

end Core

section Words

variable {W : Type} [NormedAddCommGroup W] [NormedSpace ℂ W]

theorem zOp_post (hR : RCalc) (L : W →L[ℂ] W) (w : List (Bool × ℕ)) {f : Mat n → W}
    (hf : ContDiffOn ℝ ∞ f (GLs n)) {g : Mat n} (hg : g ∈ GLs n) :
    zOp w (fun y => L (f y)) g = L (zOp w f g) := by
  induction w generalizing g with
  | nil => rfl
  | cons p w ih =>
    have e : Set.EqOn (zOp w fun y => L (f y)) (fun y => L (zOp w f y)) (GLs n) := fun y hy => ih hy
    show gel p.1 p.2 (zOp w fun y => L (f y)) g = L (gel p.1 p.2 (zOp w f) g)
    rw [(good_gel hR p.1 p.2).2.2 _ _ e hg]
    exact gel_post L p.1 p.2 ((good_zOp hR w).1 f hf) hg

theorem zOp_trans (hR : RCalc) {a b : Mat n} (ha : a ∈ GLs n) (hb : b ∈ GLs n) (w : List (Bool × ℕ)) {f : Mat n → W}
    (hf : ContDiffOn ℝ ∞ f (GLs n)) {g : Mat n} (hg : g ∈ GLs n) :
    zOp w (fun y => f (a * y * b)) g = zOp w f (a * g * b) := by
  induction w generalizing g with
  | nil => rfl
  | cons p w ih =>
    have e : Set.EqOn (zOp w fun y => f (a * y * b)) (fun y => zOp w f (a * y * b)) (GLs n) := fun y hy => ih hy
    have hZ := (good_zOp hR w).1 f hf
    have hZ' : ContDiffOn ℝ ∞ (fun y => zOp w f (y * b)) (GLs n) :=
      hZ.comp (mulR b).contDiff.contDiffOn (mapsTo_mulR hb)
    show gel p.1 p.2 (zOp w fun y => f (a * y * b)) g = gel p.1 p.2 (zOp w f) (a * g * b)
    rw [(good_gel hR p.1 p.2).2.2 _ _ e hg]
    rw [gel_left p.1 p.2 ha (f := fun y => zOp w f (y * b)) hZ' hg]
    exact gel_right p.1 p.2 hb hZ (mul_mem ha hg)

end Words

theorem act_eq_Lk [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure] (E : KMod n)
    (k : Mat n → (E.V →L[ℂ] E.V)) (f : Mat n → E.V) {x : Mat n} (hx : x ∈ GLs n) :
    act μ E k f x = Lk μ (fun y => k y⁻¹) f x := by
  have h := integral_mul_left_eq_self (μ := μ) (fun y : G n => k y.val (f (x * y.val))) (toG hx)⁻¹
  refine h.symm.trans (integral_congr_ae (ae_of_all _ fun z => ?_))
  have e1 : x * ((toG hx)⁻¹ * z).val = z.val := by
    have : (toG hx * ((toG hx)⁻¹ * z)).val = z.val := by rw [mul_inv_cancel_left]
    exact this
  have e2 : ((z⁻¹ : G n).val * x)⁻¹ = ((toG hx)⁻¹ * z).val := by
    have : (z⁻¹ * toG hx : G n).val⁻¹ = ((z⁻¹ * toG hx : G n)⁻¹).val := (val_inv _).symm
    have e3 : (z⁻¹ * toG hx : G n).val = (z⁻¹ : G n).val * x := rfl
    rw [e3] at this
    rw [this, _root_.mul_inv_rev, _root_.inv_inv]
  simp only [e1, e2]

theorem kerW : KerW := by
  rintro n _ _ μ _ E w g hL hU hR ⟨k₀, hs, ⟨R, hR0⟩, heq, hact⟩
  haveI := FiniteDimensional.complete ℂ E.V
  have hKs : ContDiffOn ℝ ∞ (fun y : Mat n => k₀ y⁻¹) (GLs n) :=
    hs.comp GlobalTheory.CompanionTheory.LengthGL.contDiffOn_inv fun _ hy => inv_mem hy
  have hKc : Cpt (fun y : Mat n => k₀ y⁻¹) :=
    ⟨R, fun y hy h => hR0 _ (inv_mem hy) (by rwa [(hL n).2.1 y hy])⟩
  have hZs := (good_zOp hR w).1 _ hKs
  have hZc : Cpt (zOp w fun y : Mat n => k₀ y⁻¹) :=
    (Rel.zOp (μ := μ) hL (f := 0) continuousOn_const (B := Lk μ (fun y => k₀ y⁻¹) 0)
      ⟨hKs, hKc, fun _ _ => rfl⟩ w).2.1
  refine ⟨fun y => zOp w (fun y : Mat n => k₀ y⁻¹) y⁻¹, hZs.comp GlobalTheory.CompanionTheory.LengthGL.contDiffOn_inv fun _ hy => inv_mem hy,
    ?_, ?_, ?_⟩
  · obtain ⟨R', hR'⟩ := hZc
    exact ⟨R', fun y hy h => hR' _ (inv_mem hy) (by rwa [(hL n).2.1 y hy])⟩
  · intro y hy k₁ k₂
    have hk₁ := GlobalTheory.CompanionTheory.RCalc.unitary_mem_GLs k₁
    have hk₂ := GlobalTheory.CompanionTheory.RCalc.unitary_mem_GLs k₂
    have hinv : ∀ x : Mat n, (k₁.1 * x * k₂.1)⁻¹ = k₂.1⁻¹ * x⁻¹ * k₁.1⁻¹ := fun x => by
      rw [Matrix.mul_inv_rev, Matrix.mul_inv_rev, Matrix.mul_assoc]
    have hinv' : ∀ x : Mat n, (k₂.1⁻¹ * x * k₁.1⁻¹)⁻¹ = k₁.1 * x⁻¹ * k₂.1 := fun x => by
      rw [Matrix.mul_inv_rev, Matrix.mul_inv_rev, inv_inv_mat hk₁, inv_inv_mat hk₂, Matrix.mul_assoc]
    let L : (E.V →L[ℂ] E.V) →L[ℂ] (E.V →L[ℂ] E.V) :=
      (ContinuousLinearMap.mul ℂ (E.V →L[ℂ] E.V) (E.ρ k₁)).comp
        ((ContinuousLinearMap.mul ℂ (E.V →L[ℂ] E.V)).flip (E.ρ k₂))
    have hLa : ∀ T, L T = E.ρ k₁ * T * E.ρ k₂ := fun T => by
      simp [L, mul_assoc]
    have hE : Set.EqOn (fun x : Mat n => k₀ (k₂.1⁻¹ * x * k₁.1⁻¹)⁻¹) (fun x => L (k₀ x⁻¹)) (GLs n) := fun x hx => by
      show k₀ (k₂.1⁻¹ * x * k₁.1⁻¹)⁻¹ = L (k₀ x⁻¹)
      rw [hinv', hLa, heq _ (inv_mem hx)]
    show zOp w (fun y : Mat n => k₀ y⁻¹) (k₁.1 * y * k₂.1)⁻¹ = _
    rw [hinv y, ← zOp_trans hR (inv_mem hk₂) (inv_mem hk₁) w hKs (inv_mem hy),
      (good_zOp hR w).2.2 _ _ hE (inv_mem hy), zOp_post hR L w hKs (inv_mem hy), hLa]
  · intro u hu x hx
    have hf : ContinuousOn (u 0) (GLs n) := (hu.2.1 0).1.continuousOn
    have h0 : Rel μ (u 0) (fun y : Mat n => k₀ y⁻¹) (fun x' => ∫ t, (g t : ℂ) • u t x') :=
      ⟨hKs, hKc, fun x hx => (hact u hu x hx).symm.trans (act_eq_Lk μ E k₀ (u 0) hx)⟩
    have h1 := (h0.zOp hL hf w).2.2 x hx
    rw [h1, act_eq_Lk μ E _ (u 0) hx]
    refine integral_congr_ae (ae_of_all _ fun z => ?_)
    simp only [inv_inv_mat (mul_mem (val_mem z⁻¹) hx)]

end GlobalTheory.CompanionTheory.KerWord
