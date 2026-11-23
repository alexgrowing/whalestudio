import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.GLMatrixDerivatives.ChainOfSt
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.GLMatrixDerivatives.ChainOfCactA
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LengthFunctionFactsHold

noncomputable section

open MeasureTheory Matrix Finset Filter Topology Metric Set
open scoped ContDiff

namespace PositivityTheory.RgBcC.LfSt.ChainPf.Cact

open PositivityTheory.RgBcC
open PositivityTheory.RgTw (Mat G)
open GlobalTheory.CompanionTheory.LengthGL (isOpen_GLs contDiffOn_inv mem_GLs_val isCompact_G lg_mul_le fderiv_inv_mul
  differentiableAt_inv contDiffOn_lg)

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

theorem inv_mem {a : Mat n} (ha : a ∈ GLs n) : a⁻¹ ∈ GLs n := by
  simp only [GLs, Set.mem_ofPred_eq, Matrix.det_nonsing_inv, Ring.inverse_eq_inv'] at *
  exact inv_ne_zero ha

theorem mul_mem {a b : Mat n} (ha : a ∈ GLs n) (hb : b ∈ GLs n) : a * b ∈ GLs n := by
  simp only [GLs, Set.mem_ofPred_eq, Matrix.det_mul] at *
  exact mul_ne_zero ha hb

theorem isUnit_det {a : Mat n} (ha : a ∈ GLs n) : IsUnit a.det := isUnit_iff_ne_zero.2 ha

def mulR (z : Mat n) : Mat n →L[ℝ] Mat n :=
  LinearMap.toContinuousLinearMap
    { toFun := fun w => w * z, map_add' := fun a b => Matrix.add_mul a b z,
      map_smul' := fun c a => Matrix.smul_mul c a z }

def mulL (x : Mat n) : Mat n →L[ℝ] Mat n :=
  LinearMap.toContinuousLinearMap
    { toFun := fun w => x * w, map_add' := fun a b => Matrix.mul_add x a b,
      map_smul' := fun c a => Matrix.mul_smul x c a }

theorem cdo_mul {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X] {s : Set X} {A B : X → Mat n}
    (hA : ContDiffOn ℝ ∞ A s) (hB : ContDiffOn ℝ ∞ B s) : ContDiffOn ℝ ∞ (fun x => A x * B x) s := by
  have hAe : ∀ i j, ContDiffOn ℝ ∞ (fun x => A x i j) s := fun i j =>
    (GlobalTheory.CompanionTheory.LengthGL.ent i j).contDiff.comp_contDiffOn hA
  have hBe : ∀ i j, ContDiffOn ℝ ∞ (fun x => B x i j) s := fun i j =>
    (GlobalTheory.CompanionTheory.LengthGL.ent i j).contDiff.comp_contDiffOn hB
  refine contDiffOn_pi.2 fun i => contDiffOn_pi.2 fun j => ?_
  simp only [Matrix.mul_apply]
  exact ContDiffOn.sum fun c _ => (hAe i c).mul (hBe c j)

def Psi {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] (k : Mat n → (V →L[ℂ] V)) (f : Mat n → V)
    (p : Mat n × Mat n) : V :=
  k (p.1⁻¹ * p.2) (f p.2)

theorem contDiffOn_Psi {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] {k : Mat n → (V →L[ℂ] V)}
    {f : Mat n → V} (hk : ContDiffOn ℝ ∞ k (GLs n)) (hf : ContDiffOn ℝ ∞ f (GLs n)) :
    ContDiffOn ℝ ∞ (Psi k f) (GLs n ×ˢ GLs n) := by
  have h1 : ContDiffOn ℝ ∞ (fun p : Mat n × Mat n => p.1⁻¹ * p.2) (GLs n ×ˢ GLs n) :=
    cdo_mul (contDiffOn_inv.comp contDiffOn_fst fun p hp => hp.1) contDiffOn_snd
  have h2 : MapsTo (fun p : Mat n × Mat n => p.1⁻¹ * p.2) (GLs n ×ˢ GLs n) (GLs n) :=
    fun p hp => mul_mem (inv_mem hp.1) hp.2
  have h3 : ContDiffOn ℝ ∞ (fun p : Mat n × Mat n => k (p.1⁻¹ * p.2)) (GLs n ×ˢ GLs n) := hk.comp h1 h2
  have h4 : ContDiffOn ℝ ∞ (fun p : Mat n × Mat n => f p.2) (GLs n ×ˢ GLs n) :=
    hf.comp contDiffOn_snd fun (p : Mat n × Mat n) (hp : p ∈ GLs n ×ˢ GLs n) => hp.2
  have h3' : ContDiffOn ℝ ∞ (fun p : Mat n × Mat n => (k (p.1⁻¹ * p.2)).restrictScalars ℝ) (GLs n ×ˢ GLs n) :=
    (ContinuousLinearMap.restrictScalarsL ℂ V V ℝ ℝ).contDiff.comp_contDiffOn h3
  exact h3'.clm_apply h4

theorem locSupp_Psi {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] {k : Mat n → (V →L[ℂ] V)}
    (f : Mat n → V) (hkc : Cpt k) : LocSupp (GLs n) (fun y : G n => y.val) (Psi k f) := by
  obtain ⟨R, hR⟩ := hkc
  intro x₀ hx₀
  obtain ⟨r, hr, hrU⟩ := Metric.isOpen_iff.1 isOpen_GLs x₀ hx₀
  have hcb : closedBall x₀ (r / 2) ⊆ GLs n := (closedBall_subset_ball (by linarith)).trans hrU
  haveI : ProperSpace (Mat n) := FiniteDimensional.proper ℝ (Mat n)
  obtain ⟨M, hM⟩ := (isCompact_closedBall x₀ (r / 2)).exists_bound_of_continuousOn
    (contDiffOn_lg.continuousOn.mono hcb)
  refine ⟨ball x₀ (r / 2), isOpen_ball, mem_ball_self (by linarith), ball_subset_closedBall.trans hcb,
    {y : G n | lg y.val ≤ R + M}, isCompact_G _, fun x hx y hy => ?_⟩
  have hxG : x ∈ GLs n := hcb (ball_subset_closedBall hx)
  have hlx : lg x ≤ M := (le_abs_self _).trans (by simpa using hM x (ball_subset_closedBall hx))
  have hy' : R + M < lg y.val := lt_of_not_ge hy
  have hsub : lg y.val ≤ lg x + lg (x⁻¹ * y.val) := by
    have := lg_mul_le x (x⁻¹ * y.val)
    rwa [Matrix.mul_nonsing_inv_cancel_left _ _ (isUnit_det hxG)] at this
  have hz : k (x⁻¹ * y.val) = 0 := hR _ (mul_mem (inv_mem hxG) (mem_GLs_val y)) (by linarith)
  simp [Psi, hz]

section Int

variable [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure]

theorem act_eq_Psi (E : KMod n) (k : Mat n → (E.V →L[ℂ] E.V))
    (f : Mat n → E.V) {x : Mat n} (hx : x ∈ GLs n) :
    act μ E k f x = ∫ y : G n, Psi k f (x, y.val) ∂μ := by
  let u : G n := Matrix.nonsingInvUnit x (isUnit_det hx)
  have hu : (u : Mat n) = x := rfl
  rw [← integral_mul_left_eq_self (fun y : G n => Psi k f (x, y.val)) u]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  simp only [Psi, Units.val_mul, hu, Matrix.nonsing_inv_mul_cancel_left _ _ (isUnit_det hx)]

theorem hasFDerivAt_Psi_slice {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] {k : Mat n → (V →L[ℂ] V)}
    (f : Mat n → V) (hk : ContDiffOn ℝ ∞ k (GLs n)) {x z : Mat n} (hx : x ∈ GLs n) (hz : z ∈ GLs n) :
    HasFDerivAt (fun x' => Psi k f (x', z))
      (((ContinuousLinearMap.apply ℂ V (f z)).restrictScalars ℝ).comp
        ((fderiv ℝ k (x⁻¹ * z)).comp ((mulR z).comp (fderiv ℝ (fun y : Mat n => y⁻¹) x)))) x := by
  have hg : HasFDerivAt (fun x' : Mat n => x'⁻¹ * z) ((mulR z).comp (fderiv ℝ (fun y : Mat n => y⁻¹) x)) x :=
    (mulR z).hasFDerivAt.comp x (differentiableAt_inv hx).hasFDerivAt
  have hk' : HasFDerivAt k (fderiv ℝ k (x⁻¹ * z)) (x⁻¹ * z) :=
    ((hk.differentiableOn (by simp)).differentiableAt
      (isOpen_GLs.mem_nhds (mul_mem (inv_mem hx) hz))).hasFDerivAt
  have hev : HasFDerivAt (fun L : V →L[ℂ] V => L (f z)) ((ContinuousLinearMap.apply ℂ V (f z)).restrictScalars ℝ)
      (k (x⁻¹ * z)) :=
    ((ContinuousLinearMap.apply ℂ V (f z)).restrictScalars ℝ).hasFDerivAt
  exact hev.comp x (hk'.comp x hg)

theorem pd_Psi_apply (E : KMod n) {k : Mat n → (E.V →L[ℂ] E.V)} (f : Mat n → E.V) (hk : ContDiffOn ℝ ∞ k (GLs n))
    (hf : ContDiffOn ℝ ∞ f (GLs n)) {x z : Mat n} (hx : x ∈ GLs n) (hz : z ∈ GLs n) (X : Mat n) :
    pd (Psi k f) (x, z) (x * X) = Ld X k (x⁻¹ * z) (f z) := by
  have h1 := hasFDerivAt_pd isOpen_GLs isOpen_GLs (contDiffOn_Psi hk hf) hx hz
  have key : pd (Psi k f) (x, z) (x * X) =
      (fderiv ℝ k (x⁻¹ * z) (mulR z (fderiv ℝ (fun y : Mat n => y⁻¹) x (x * X)))) (f z) := by
    rw [h1.unique (hasFDerivAt_Psi_slice f hk hx hz)]
    rfl
  rw [key, fderiv_inv_mul hx X]
  have : mulR z (-(X * x⁻¹)) = -(X * (x⁻¹ * z)) := by
    show -(X * x⁻¹) * z = -(X * (x⁻¹ * z))
    rw [neg_mul, Matrix.mul_assoc]
  rw [this, map_neg]
  rfl

theorem actDer : ActDer := by
  intro _hU n _ _ μ _ E k f hk hkc hf
  have hΦ := contDiffOn_Psi hk hf
  have hS := locSupp_Psi f hkc
  have hιc : Continuous fun y : G n => y.val := Units.continuous_val
  have hι : ∀ y : G n, (fun y : G n => y.val) y ∈ GLs n := mem_GLs_val
  have hI := contDiffOn_int μ isOpen_GLs isOpen_GLs hιc hι hΦ hS
  refine ⟨hI.congr fun x hx => act_eq_Psi μ E k f hx, fun X x hx => ?_⟩
  have heq : act μ E k f =ᶠ[𝓝 x] fun x => ∫ y : G n, Psi k f (x, y.val) ∂μ :=
    eventually_of_mem (isOpen_GLs.mem_nhds hx) fun x' hx' => act_eq_Psi μ E k f hx'
  have hD : HasFDerivAt (fun x => ∫ y : G n, Psi k f (x, y.val) ∂μ)
      (∫ y : G n, pd (Psi k f) (x, y.val) ∂μ) x := hasFDerivAt_int μ isOpen_GLs isOpen_GLs hιc hι hΦ hS hx
  have hint : Integrable (fun y : G n => pd (Psi k f) (x, y.val)) μ :=
    integrable_pd μ isOpen_GLs isOpen_GLs hιc hι hΦ hS hx
  have hA : HasFDerivAt (act μ E k f) (∫ y : G n, pd (Psi k f) (x, y.val) ∂μ) x := hD.congr_of_eventuallyEq heq
  have h1 : Rd X (act μ E k f) x = (∫ y : G n, pd (Psi k f) (x, y.val) ∂μ) (x * X) :=
    congrArg (fun L => L (x * X)) hA.fderiv
  rw [h1, ContinuousLinearMap.integral_apply hint]
  let u : G n := Matrix.nonsingInvUnit x (isUnit_det hx)
  have hu : (u : Mat n) = x := rfl
  rw [← integral_mul_left_eq_self (fun y : G n => pd (Psi k f) (x, y.val) (x * X)) u]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  simp only [Units.val_mul, hu]
  rw [pd_Psi_apply E f hk hf hx (mul_mem hx (mem_GLs_val y)) X,
    Matrix.nonsing_inv_mul_cancel_left _ _ (isUnit_det hx)]

end Int

end PositivityTheory.RgBcC.LfSt.ChainPf.Cact
