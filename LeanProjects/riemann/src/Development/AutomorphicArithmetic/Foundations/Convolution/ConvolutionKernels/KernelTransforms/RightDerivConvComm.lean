import Mathlib
import GroundTheory.AutomorphicForms.AutomorphicFormSpaces.Height
import GroundTheory.AutomorphicForms.TraceFormulaConvolution
import GroundTheory.AutomorphicForms.CuspidalDiscreteness.SummandsAreCuspForms
import GroundTheory.AutomorphicForms.MultiplicityOne.OpenSubgroupRep
import GroundTheory.AutomorphicForms.MultiplicityOne.FiniteLevelGroups
import GroundTheory.AutomorphicForms.MultiplicityOne.FiniteAdelicHaar
import GroundTheory.AutomorphicForms.L2LocalComponents.CenterCommute
import GroundTheory.AutomorphicForms.GKModules.KernelCalculus
import GroundTheory.AutomorphicForms.AutomorphicFormSpaces.LeftTranslate
import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.DerivInt
import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.InvSmooth
import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.Unimod
import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.CenterTr
import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.ExpGen

open MeasureTheory NumberField IsDedekindDomain
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open scoped TensorProduct InnerProductSpace ComplexConjugate Pointwise

section
open GroundTheory.Automorphic.IsExpLieAlgebra Filter
open scoped ContDiff Manifold

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸]
  {G : Subgroup 𝔸ˣ} {𝔤 : Submodule ℝ 𝔸} (h : IsExpLieAlgebra G 𝔤)

private theorem UpperTheory.ConvolutionTheory.Tf.smooth_conv {f : G → ℂ} (hf : h.IsSmoothFun f) (X : 𝔤) :
    h.IsSmoothFun (h.convDeriv X f) := by
  let _ := h.chartedSpace
  have := h.lieGroup ∞
  exact ContMDiff.comp (I' := 𝓘(ℝ, 𝔤)) (h.isSmoothFun_rightDeriv (isSmoothFun_comp_inv hf) X)
    (contMDiff_inv 𝓘(ℝ, 𝔤) ∞)

private noncomputable def UpperTheory.ConvolutionTheory.Tf.convEnd (X : 𝔤) : Module.End ℂ (h.smoothFuns (F := ℂ)) where
  toFun f := ⟨h.convDeriv X f, UpperTheory.ConvolutionTheory.Tf.smooth_conv h f.2 X⟩
  map_add' f₁ f₂ := by
    ext1; funext y
    exact congrFun (h.rightDeriv_add (isSmoothFun_comp_inv f₁.2) (isSmoothFun_comp_inv f₂.2) X) y⁻¹
  map_smul' c f := by
    ext1; funext y
    exact congrFun (h.rightDeriv_smul (isSmoothFun_comp_inv f.2) c X) y⁻¹

private theorem UpperTheory.ConvolutionTheory.Tf.hasDerivAt_conv {f : G → ℂ} (hf : h.IsSmoothFun f) (X : 𝔤) (g : G) :
    HasDerivAt (fun s : ℝ => f ((h.expG (s • X))⁻¹ * g)) (h.convDeriv X f g) 0 := by
  have h1 := h.hasDerivAt_rightDeriv (isSmoothFun_comp_inv hf) X g⁻¹
  refine h1.congr_of_eventuallyEq (Eventually.of_forall fun s => ?_)
  simp

private theorem UpperTheory.ConvolutionTheory.Tf.conv_one {f : G → ℂ} (hf : h.IsSmoothFun f) (X : 𝔤) :
    h.convDeriv X f 1 = -h.rightDeriv X f 1 := by
  have h1 := UpperTheory.ConvolutionTheory.Tf.hasDerivAt_conv h hf X 1
  have h2 := h.hasDerivAt_rightDeriv hf (-X) 1
  rw [rightDeriv_neg_left] at h2
  exact h1.unique (h2.congr_of_eventuallyEq (Eventually.of_forall fun s => by
    simp [smul_neg, h.expG_neg]))

private theorem UpperTheory.ConvolutionTheory.Tf.rightDeriv_conv_comm {f : G → ℂ} (hf : h.IsSmoothFun f) (X Y : 𝔤)
    (g : G) : h.rightDeriv Y (h.convDeriv X f) g = h.convDeriv X (h.rightDeriv Y f) g := by
  set A : ℝ × ℝ → ℂ := fun p => f ((h.expG (p.1 • X))⁻¹ * (g * h.expG (p.2 • Y))) with hAdef
  have hA : ContDiff ℝ ∞ A := by
    let _ := h.chartedSpace
    have := h.lieGroup ∞
    have hm : ContMDiff 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, 𝔤) ∞
        (fun p : ℝ × ℝ => (h.expG (p.1 • X))⁻¹ * (g * h.expG (p.2 • Y))) :=
      ((h.contMDiff_expG_comp (contDiff_fst.smul contDiff_const)).inv).mul
        (contMDiff_const.mul (h.contMDiff_expG_comp (contDiff_snd.smul contDiff_const)))
    exact (ContMDiff.comp (I' := 𝓘(ℝ, 𝔤)) hf hm).contDiff
  have hAd : Differentiable ℝ A := hA.differentiable (by simp)
  set e₁ : ℝ × ℝ := (1, 0)
  set e₂ : ℝ × ℝ := (0, 1)
  set D2 := fderiv ℝ (fderiv ℝ A) 0
  have d1 : ∀ t : ℝ, fderiv ℝ A (t • e₂) e₁ = h.convDeriv X f (g * h.expG (t • Y)) := by
    intro t
    have h1 := hasDerivAt_comp_line (hAd (t • e₂)) e₁
    have h2 := UpperTheory.ConvolutionTheory.Tf.hasDerivAt_conv h hf X (g * h.expG (t • Y))
    refine h1.unique (h2.congr_of_eventuallyEq (Eventually.of_forall fun s => ?_))
    simp [A, e₁, e₂]
  have d2 : ∀ s : ℝ, fderiv ℝ A (s • e₁) e₂ = h.rightDeriv Y f ((h.expG (s • X))⁻¹ * g) := by
    intro s
    have h1 := hasDerivAt_comp_line (hAd (s • e₁)) e₂
    have h2 := h.hasDerivAt_rightDeriv hf Y ((h.expG (s • X))⁻¹ * g)
    refine h1.unique (h2.congr_of_eventuallyEq (Eventually.of_forall fun t => ?_))
    simp [A, e₁, e₂, mul_assoc]
  have a1 : D2 e₂ e₁ = h.rightDeriv Y (h.convDeriv X f) g := by
    have h1 := hasDerivAt_fderiv_line hA 0 e₂ e₁
    have h2 := h.hasDerivAt_rightDeriv (UpperTheory.ConvolutionTheory.Tf.smooth_conv h hf X) Y g
    refine h1.unique (h2.congr_of_eventuallyEq (Eventually.of_forall fun t => ?_))
    simp only [zero_add]
    rw [d1]
  have a2 : D2 e₁ e₂ = h.convDeriv X (h.rightDeriv Y f) g := by
    have h1 := hasDerivAt_fderiv_line hA 0 e₁ e₂
    have h2 := UpperTheory.ConvolutionTheory.Tf.hasDerivAt_conv h (h.isSmoothFun_rightDeriv hf Y) X g
    refine h1.unique (h2.congr_of_eventuallyEq (Eventually.of_forall fun s => ?_))
    simp only [zero_add]
    rw [d2]
  have hsymm : D2 e₂ e₁ = D2 e₁ e₂ :=
    (hA.contDiffAt.isSymmSndFDerivAt (by
      simp only [minSmoothness_of_isRCLikeNormedField]; exact WithTop.coe_le_coe.2 le_top)) e₂ e₁
  rw [← a1, ← a2, hsymm]

private theorem UpperTheory.ConvolutionTheory.Tf.conv_rightTranslate (f : G → ℂ) (X : 𝔤) (x y : G) :
    h.convDeriv X (GroundTheory.Automorphic.rightTranslate x f) y = h.convDeriv X f (y * x) := by
  have e : (fun z : G => GroundTheory.Automorphic.rightTranslate x f z⁻¹) = GroundTheory.Automorphic.leftTranslate x⁻¹ (fun z : G => f z⁻¹) := by
    funext z; simp [GroundTheory.Automorphic.rightTranslate, GroundTheory.Automorphic.leftTranslate]
  show h.rightDeriv X (fun z : G => GroundTheory.Automorphic.rightTranslate x f z⁻¹) y⁻¹ = h.rightDeriv X (fun z : G => f z⁻¹) (y * x)⁻¹
  rw [e, h.rightDeriv_leftTranslate]
  simp [GroundTheory.Automorphic.leftTranslate]

private theorem UpperTheory.ConvolutionTheory.Tf.commute_uAction {T : Module.End ℂ (h.smoothFuns (F := ℂ))}
    (hT : ∀ Y : 𝔤, Commute T (h.rightDerivEnd Y))
    (v : UniversalEnvelopingAlgebra ℝ h.lieSubalgebra) : Commute T (h.rightUAction v) := by
  obtain ⟨t, rfl⟩ : ∃ t, UniversalEnvelopingAlgebra.mkAlgHom ℝ h.lieSubalgebra t = v :=
    RingCon.mkₐ_surjective (α := ℝ) (UniversalEnvelopingAlgebra.ringCon ℝ h.lieSubalgebra) v
  induction t using TensorAlgebra.induction with
  | algebraMap r =>
    simp only [AlgHom.commutes]
    exact (Algebra.commutes r T).symm
  | ι x =>
    have e : UniversalEnvelopingAlgebra.mkAlgHom ℝ h.lieSubalgebra (TensorAlgebra.ι ℝ x) =
        UniversalEnvelopingAlgebra.ι ℝ x := rfl
    rw [e, rightUAction_ι]
    exact hT _
  | mul a b ha hb =>
    simp only [map_mul]
    exact ha.mul_right hb
  | add a b ha hb =>
    simp only [map_add]
    exact ha.add_right hb

variable [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure]

private theorem UpperTheory.ConvolutionTheory.Tf.ibp {Ψ γ : G → ℂ} (hΨ : h.IsTestFunction Ψ) (hγ : h.IsTestFunction γ)
    (X : 𝔤) : ∫ a, Ψ a * h.convDeriv X γ a ∂μ = -∫ a, h.convDeriv X Ψ a * γ a ∂μ := by
  have hA := h.rightDeriv_integral_mul μ (hΨ.continuous h) hγ X 1
  have hB := h.rightDeriv_integral_mul μ (hγ.continuous h) hΨ X 1
  have hsA := h.isSmoothFun_integral_mul μ (hΨ.continuous h) hγ
  have e : (fun g => ∫ y, Ψ (g⁻¹ * y) * γ y ∂μ) = fun g => ∫ y, γ (g * y) * Ψ y ∂μ := by
    funext g
    have := IsExpLieAlgebra.integral_mul_left_kernel μ Ψ γ g⁻¹
    rw [this]
    simp [mul_comm]
  have hc := UpperTheory.ConvolutionTheory.Tf.conv_one h hsA X
  have hc' : h.rightDeriv X (fun g => ∫ y, γ (g * y) * Ψ y ∂μ) 1 =
      -h.rightDeriv X (fun g => ∫ y, Ψ (g * y) * γ y ∂μ) 1 := by
    rw [← e, ← hc]
    simp [IsExpLieAlgebra.convDeriv]
  rw [hA, hB] at hc'
  simp only [one_mul] at hc'
  have e2 : ∫ a, h.convDeriv X Ψ a * γ a ∂μ = ∫ a, γ a * h.convDeriv X Ψ a ∂μ := by
    congr 1; funext a; ring
  rw [e2, hc', neg_neg]

private theorem UpperTheory.ConvolutionTheory.Tf.integrable_mul_inv {p q : G → ℂ} (hp : Continuous p) (hq : Continuous q)
    (hc : HasCompactSupport p) : Integrable (fun a => p a * q a⁻¹) μ :=
  (hp.mul (hq.comp continuous_inv)).integrable_of_hasCompactSupport hc.mul_right

private theorem UpperTheory.ConvolutionTheory.Tf.exists_transpose
    (hcs : ∀ (v : UniversalEnvelopingAlgebra ℝ h.lieSubalgebra) (κ : h.smoothFuns (F := ℂ)),
      HasCompactSupport (κ : G → ℂ) → HasCompactSupport (h.rightUAction v κ : G → ℂ))
    (u : UniversalEnvelopingAlgebra ℝ h.lieSubalgebra) :
    ∃ T : Module.End ℂ (h.smoothFuns (F := ℂ)),
      (∀ Y : 𝔤, Commute T (h.rightDerivEnd Y)) ∧ (∀ x : G, Commute T (h.rightTranslateEnd x)) ∧
      (∀ Ψ, (T Ψ : G → ℂ) 1 = (h.rightUAction u Ψ : G → ℂ) 1) ∧
      (∀ Ψ : h.smoothFuns (F := ℂ), HasCompactSupport (Ψ : G → ℂ) →
        HasCompactSupport (T Ψ : G → ℂ)) ∧
      (∀ Ψ κ : h.smoothFuns (F := ℂ), HasCompactSupport (Ψ : G → ℂ) →
        HasCompactSupport (κ : G → ℂ) →
        ∫ a, (T Ψ : G → ℂ) a * (κ : G → ℂ) a⁻¹ ∂μ =
          ∫ a, (Ψ : G → ℂ) a * (h.rightUAction u κ : G → ℂ) a⁻¹ ∂μ) := by
  obtain ⟨t, rfl⟩ : ∃ t, UniversalEnvelopingAlgebra.mkAlgHom ℝ h.lieSubalgebra t = u :=
    RingCon.mkₐ_surjective (α := ℝ) (UniversalEnvelopingAlgebra.ringCon ℝ h.lieSubalgebra) u
  induction t using TensorAlgebra.induction with
  | algebraMap r =>
    have hr : ∀ (Ψ : h.smoothFuns (F := ℂ)) (x : G),
        ((algebraMap ℝ (Module.End ℂ (h.smoothFuns (F := ℂ))) r Ψ : h.smoothFuns (F := ℂ)) : G → ℂ) x =
          (r : ℂ) * (Ψ : G → ℂ) x := fun _ _ => rfl
    refine ⟨algebraMap ℝ _ r, fun Y => Algebra.commutes r _, fun x => Algebra.commutes r _,
      fun Ψ => ?_, fun Ψ hΨ => ?_, fun Ψ κ _ _ => ?_⟩
    · simp only [AlgHom.commutes]
    · refine hΨ.mono fun x hx h0 => hx ?_
      rw [hr, h0, mul_zero]
    · simp only [AlgHom.commutes, hr]
      congr 1; funext a; ring
  | ι x =>
    have e : UniversalEnvelopingAlgebra.mkAlgHom ℝ h.lieSubalgebra (TensorAlgebra.ι ℝ x) =
        UniversalEnvelopingAlgebra.ι ℝ x := rfl
    have hn : ∀ (Ψ : h.smoothFuns (F := ℂ)) (y : G),
        (((-UpperTheory.ConvolutionTheory.Tf.convEnd h (h.ofLie x)) Ψ : h.smoothFuns (F := ℂ)) : G → ℂ) y =
          -h.convDeriv (h.ofLie x) Ψ y := fun _ _ => rfl
    refine ⟨-UpperTheory.ConvolutionTheory.Tf.convEnd h (h.ofLie x), fun Y => ?_, fun a => ?_, fun Ψ => ?_,
      fun Ψ hΨ => ?_, fun Ψ κ hΨ hκ => ?_⟩
    · refine Commute.neg_left (LinearMap.ext fun f => Subtype.ext (funext fun g => ?_))
      exact (UpperTheory.ConvolutionTheory.Tf.rightDeriv_conv_comm h f.2 (h.ofLie x) Y g).symm
    · refine Commute.neg_left (LinearMap.ext fun f => Subtype.ext (funext fun g => ?_))
      exact UpperTheory.ConvolutionTheory.Tf.conv_rightTranslate h f (h.ofLie x) a g
    · rw [e, rightUAction_ι, hn, UpperTheory.ConvolutionTheory.Tf.conv_one h Ψ.2, neg_neg]
      rfl
    · have := (hasCompactSupport_convDeriv hΨ (h := h) (h.ofLie x)).comp_left (g := Neg.neg) neg_zero
      exact this
    · have hγ : h.IsTestFunction (fun y => (κ : G → ℂ) y⁻¹) :=
        ⟨isSmoothFun_comp_inv κ.2, hκ.comp_homeomorph (Homeomorph.inv _)⟩
      have hΨt : h.IsTestFunction (Ψ : G → ℂ) := ⟨Ψ.2, hΨ⟩
      have hi := UpperTheory.ConvolutionTheory.Tf.ibp h μ hΨt hγ (h.ofLie x)
      have e3 : (fun a => (Ψ : G → ℂ) a * h.convDeriv (h.ofLie x) (fun y => (κ : G → ℂ) y⁻¹) a) =
          fun a => (Ψ : G → ℂ) a * (h.rightUAction (UniversalEnvelopingAlgebra.ι ℝ x) κ : G → ℂ) a⁻¹ := by
        funext a
        rw [rightUAction_ι]
        simp [IsExpLieAlgebra.convDeriv]
      rw [e3] at hi
      rw [e, hi, ← integral_neg]
      congr 1; funext a
      rw [hn, neg_mul]
  | mul a b ha hb =>
    obtain ⟨Ta, ha1, ha2, ha3, ha4, ha5⟩ := ha
    obtain ⟨Tb, hb1, hb2, hb3, hb4, hb5⟩ := hb
    refine ⟨Tb * Ta, fun Y => (hb1 Y).mul_left (ha1 Y), fun x => (hb2 x).mul_left (ha2 x),
      fun Ψ => ?_, fun Ψ hΨ => hb4 _ (ha4 _ hΨ), fun Ψ κ hΨ hκ => ?_⟩
    · have hc := LinearMap.congr_fun (UpperTheory.ConvolutionTheory.Tf.commute_uAction h ha1
        (UniversalEnvelopingAlgebra.mkAlgHom ℝ h.lieSubalgebra b)).eq Ψ
      simp only [Module.End.mul_apply] at hc
      rw [Module.End.mul_apply, hb3, ← hc, ha3, map_mul, map_mul, Module.End.mul_apply]
    · rw [Module.End.mul_apply, hb5 _ κ (ha4 _ hΨ) hκ, ha5 Ψ _ hΨ (hcs _ κ hκ), map_mul, map_mul,
        Module.End.mul_apply]
  | add a b ha hb =>
    obtain ⟨Ta, ha1, ha2, ha3, ha4, ha5⟩ := ha
    obtain ⟨Tb, hb1, hb2, hb3, hb4, hb5⟩ := hb
    refine ⟨Ta + Tb, fun Y => (ha1 Y).add_left (hb1 Y), fun x => (ha2 x).add_left (hb2 x),
      fun Ψ => ?_, fun Ψ hΨ => ?_, fun Ψ κ hΨ hκ => ?_⟩
    · simp only [map_add, LinearMap.add_apply, Submodule.coe_add, Pi.add_apply, ha3, hb3]
    · exact (ha4 Ψ hΨ).add (hb4 Ψ hΨ)
    · have hcont : ∀ f : h.smoothFuns (F := ℂ), Continuous (f : G → ℂ) :=
        fun f => continuous_of_isSmoothFun f.2
      simp only [map_add, LinearMap.add_apply, Submodule.coe_add, Pi.add_apply, add_mul, mul_add]
      rw [integral_add (UpperTheory.ConvolutionTheory.Tf.integrable_mul_inv μ (hcont _) (hcont κ) (ha4 Ψ hΨ))
          (UpperTheory.ConvolutionTheory.Tf.integrable_mul_inv μ (hcont _) (hcont κ) (hb4 Ψ hΨ)),
        integral_add (UpperTheory.ConvolutionTheory.Tf.integrable_mul_inv μ (hcont Ψ) (hcont _) hΨ)
          (UpperTheory.ConvolutionTheory.Tf.integrable_mul_inv μ (hcont Ψ) (hcont _) hΨ), ha5 Ψ κ hΨ hκ, hb5 Ψ κ hΨ hκ]
end

theorem UpperTheory.ConvolutionTheory.Tf.convZ :
    ∀ (K : Type) [Field K] [NumberField K] [IsTotallyComplex K] (n : ℕ) (ν : Measure (archGroup K n)) [ν.IsHaarMeasure]
      (β₁ β₂ : CompactlySupportedContinuousMap (archGroup K n) ℂ) (h₁ : (fun g => β₁ g⁻¹) ∈ (isExpLieAlgebra K n).smoothFuns (F := ℂ)) (h₂ : (fun g => β₂ g⁻¹) ∈ (isExpLieAlgebra K n).smoothFuns (F := ℂ))
      (z : UEnv K n), z ∈ (isExpLieAlgebra K n).centerU → ∀ x : archGroup K n,
        ∫ a, ((isExpLieAlgebra K n).rightUAction z ⟨fun g => β₁ g⁻¹, h₁⟩ : archGroup K n → ℂ) a⁻¹ * β₂ (a⁻¹ * x) ∂ν =
          ∫ a, β₁ a * ((isExpLieAlgebra K n).rightUAction z ⟨fun g => β₂ g⁻¹, h₂⟩ : archGroup K n → ℂ) (a⁻¹ * x)⁻¹ ∂ν := by
  intro K _ _ _ n ν _ β₁ β₂ h₁ h₂ z hz x
  have hcs : ∀ (v : UEnv K n) (κ : (isExpLieAlgebra K n).smoothFuns (F := ℂ)),
      HasCompactSupport (κ : archGroup K n → ℂ) →
      HasCompactSupport ((isExpLieAlgebra K n).rightUAction v κ : archGroup K n → ℂ) := by
    intro v κ hκ
    exact IsCompact.of_isClosed_subset hκ (isClosed_tsupport _)
      ((UpperTheory.ConvolutionTheory.Tf.invSmooth K n κ κ.2).2.2.2 κ.2 v)
  obtain ⟨T, -, hb, hc, -, he⟩ := UpperTheory.ConvolutionTheory.Tf.exists_transpose (isExpLieAlgebra K n) ν hcs z
  have hTz : ∀ (Ψ : (isExpLieAlgebra K n).smoothFuns (F := ℂ)) (y : archGroup K n),
      (T Ψ : archGroup K n → ℂ) y = ((isExpLieAlgebra K n).rightUAction z Ψ : archGroup K n → ℂ) y := by
    intro Ψ y
    obtain ⟨hk, hk2⟩ := UpperTheory.ConvolutionTheory.Tf.centerTr K n z hz y
      (by rw [UpperTheory.ConvolutionTheory.Tf.expGen]; trivial) Ψ Ψ.2
    have h1 := LinearMap.congr_fun (hb y).eq Ψ
    simp only [Module.End.mul_apply] at h1
    have h2 : (T Ψ : archGroup K n → ℂ) y =
        (T ((isExpLieAlgebra K n).rightTranslateEnd y Ψ) : archGroup K n → ℂ) 1 := by
      rw [h1]
      simp [GroundTheory.Automorphic.rightTranslate]
    have h3 := hk2 1
    rw [one_mul] at h3
    rw [h2, hc]
    exact h3
  have hk1 : HasCompactSupport (fun g : archGroup K n => β₁ g⁻¹) :=
    β₁.hasCompactSupport.comp_homeomorph (Homeomorph.inv _)
  have hk2 : HasCompactSupport (fun g : archGroup K n => β₂ g⁻¹) :=
    β₂.hasCompactSupport.comp_homeomorph (Homeomorph.inv _)
  set k₂ : (isExpLieAlgebra K n).smoothFuns (F := ℂ) := ⟨fun g => β₂ g⁻¹, h₂⟩ with hk₂
  set k₁ : (isExpLieAlgebra K n).smoothFuns (F := ℂ) := ⟨fun g => β₁ g⁻¹, h₁⟩ with hk₁
  have hΨc : HasCompactSupport
      (((isExpLieAlgebra K n).leftTranslateEnd x⁻¹ k₂ : (isExpLieAlgebra K n).smoothFuns (F := ℂ)) :
        archGroup K n → ℂ) :=
    hk2.comp_homeomorph (Homeomorph.mulLeft x⁻¹)
  have key := he ((isExpLieAlgebra K n).leftTranslateEnd x⁻¹ k₂) k₁ hΨc hk1
  calc ∫ a, ((isExpLieAlgebra K n).rightUAction z k₁ : archGroup K n → ℂ) a⁻¹ * β₂ (a⁻¹ * x) ∂ν
      = ∫ a, (((isExpLieAlgebra K n).leftTranslateEnd x⁻¹ k₂ : (isExpLieAlgebra K n).smoothFuns (F := ℂ)) :
          archGroup K n → ℂ) a * ((isExpLieAlgebra K n).rightUAction z k₁ : archGroup K n → ℂ) a⁻¹ ∂ν := by
        congr 1; funext a
        rw [mul_comm]
        congr 1
    _ = ∫ a, (T ((isExpLieAlgebra K n).leftTranslateEnd x⁻¹ k₂) : archGroup K n → ℂ) a * (k₁ : archGroup K n → ℂ) a⁻¹ ∂ν := key.symm
    _ = _ := by
        congr 1; funext a
        rw [hTz, IsExpLieAlgebra.rightUAction_leftTranslate_apply, mul_comm]
        have e1 : (k₁ : archGroup K n → ℂ) a⁻¹ = β₁ a := by
          show β₁ a⁻¹⁻¹ = β₁ a
          simp
        rw [e1]
        simp
