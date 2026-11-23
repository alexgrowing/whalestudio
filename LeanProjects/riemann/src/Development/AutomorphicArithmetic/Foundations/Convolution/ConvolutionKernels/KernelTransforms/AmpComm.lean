import Development.AutomorphicArithmetic.Foundations.Convolution.TensFun
import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.NormIntLe
import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.CommPrj
import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.LactConv
import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.HopLevel
import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.TsphComm

open MeasureTheory NumberField IsDedekindDomain MvPolynomial
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C
open scoped TensorProduct InnerProductSpace ComplexConjugate Pointwise

private theorem finAt_mem_of_integral {K : Type} [Field K] [NumberField K] {n : ℕ} (w : Pl K)
    {u : AdelicGLn.FiniteAdelicGL K n} (hu : u ∈ AdelicGLn.integralFiniteGL K n) :
    finAt w (finEmb K n u) ∈ GLnLocal.integralGL (w.adicCompletion K) n := by
  have e : finAt w (finEmb K n u) = AdelicGLn.finiteRestrictedEquiv K n u w := by
    show (AdelicGLn.finiteRestrictedEquiv K n (AdelicGLn.prodEquiv K n (finEmb K n u)).2) w = _
    rw [prodEquiv_finEmb]
  rw [e]
  exact (AdelicGLn.mem_integralFiniteGL_iff_forall K n).1 hu w

theorem UpperTheory.ConvolutionTheory.Tf.ampComm :
    ∀ (K : Type) [Field K] [NumberField K] [IsTotallyComplex K] (n : ℕ) (μ : Measure (normOneGL K n)) [μ.IsHaarMeasure] (𝔞 : Amp μ),
      (∀ τ i, zc τ i ∈ Subalgebra.center ℂ (UC K n)) →
      0 ≤ 𝔞.A ∧ ‖𝔞.A‖ ≤ 1 ∧ (∀ v, 𝔞.A v ∈ fixF μ 𝔞.U) ∧ IsCompact (𝔞.U : Set (AdelicGLn.FiniteAdelicGL K n)) ∧
      (∀ x, Commute 𝔞.A (𝔞.Z x)) ∧ (∀ x y, Commute (𝔞.Z x) (𝔞.Z y)) ∧
      ∀ w ∉ 𝔞.S, ∀ i, Commute 𝔞.A (Tsph μ w i) ∧ ∀ x, Commute (𝔞.Z x) (Tsph μ w i) := by
  intro K _ _ _ n μ _ 𝔞 hz
  obtain ⟨-, -, a1, a2, -, -, -, -, hT⟩ := UpperTheory.ConvolutionTheory.Tf.commPrj K n μ 𝔞.U
  obtain ⟨hconv, -, -, -, -, -, -, -, hρ⟩ := UpperTheory.ConvolutionTheory.Tf.opAlg K n μ 𝔞.ν (Measure.haar : Measure (AdelicGLn.FiniteAdelicGL K n))
  have hA : ∀ β : TI K n, Oinf μ 𝔞.ν β ∘L prj (fixF μ 𝔞.U) = Oinf μ 𝔞.ν β * prj (fixF μ 𝔞.U) := fun _ => rfl
  have hOP : ∀ β : TI K n, Commute (Oinf μ 𝔞.ν β) (prj (fixF μ 𝔞.U)) := fun β => hT _ fun u _ => hρ β u
  have hPP : prj (fixF μ 𝔞.U) * prj (fixF μ 𝔞.U) = prj (fixF μ 𝔞.U) :=
    ContinuousLinearMap.ext fun v => a2 _ (a1 v)
  have hcomp : ∀ β γ : TI K n, conv 𝔞.ν β γ = conv 𝔞.ν γ β →
      Commute (Oinf μ 𝔞.ν β * prj (fixF μ 𝔞.U)) (Oinf μ 𝔞.ν γ * prj (fixF μ 𝔞.U)) := by
    intro β γ h
    have e : ∀ β γ : TI K n, (Oinf μ 𝔞.ν β * prj (fixF μ 𝔞.U)) * (Oinf μ 𝔞.ν γ * prj (fixF μ 𝔞.U)) =
        Oinf μ 𝔞.ν (conv 𝔞.ν β γ) * prj (fixF μ 𝔞.U) := by
      intro β γ
      rw [(hOP γ).symm.mul_mul_mul_comm, hPP, (hconv β γ).1]
      rfl
    show _ * _ = _ * _
    rw [e, e, h]
  have hs := 𝔞.smooth
  have hl := UpperTheory.ConvolutionTheory.Tf.lactSpec K n 𝔞.a₀ hs
  obtain ⟨-, -, hsm, -, hmul, -⟩ := hl
  have hswap : ∀ u ∈ Subalgebra.center ℂ (UC K n), ∀ β : TI K n, SmoothT β →
      conv 𝔞.ν (lact u 𝔞.a₀) β = conv 𝔞.ν 𝔞.a₀ (lact u β) := fun u hu β hβ =>
    (UpperTheory.ConvolutionTheory.Tf.lactConv K n 𝔞.ν 𝔞.a₀ β hs).2.2 inferInstance hβ u hu
  have hHop : ∀ w ∉ 𝔞.S, ∀ (x : GL (Fin n) (w.adicCompletion K)) (β : TI K n),
      Commute (Oinf μ 𝔞.ν β * prj (fixF μ 𝔞.U)) (Hop μ w (GLnLocal.integralGL (w.adicCompletion K) n) x) := by
    intro w hw x β
    have hO := GLnLocal.isOpen_integralGL (w.adicCompletion K) n
    have hC := GLnLocal.isCompact_integralGL (w.adicCompletion K) n
    have hUc : IsCompact (𝔞.U : Set (AdelicGLn.FiniteAdelicGL K n)) :=
      (AdelicGLn.isCompact_integralFiniteGL K n).of_isClosed_subset (𝔞.U.isClosed_of_isOpen 𝔞.isOpen) 𝔞.le
    have h1 : Commute (Oinf μ 𝔞.ν β) (Hop μ w (GLnLocal.integralGL (w.adicCompletion K) n) x) :=
      (UpperTheory.ConvolutionTheory.Tf.hopBasic K n μ w _ x hO hC).2.2.2.2.1 _ fun g => hρ β _
    have h2 := (UpperTheory.ConvolutionTheory.Tf.hopLevel K n μ (Measure.haar : Measure (AdelicGLn.FiniteAdelicGL K n)) w _ x 𝔞.U hO hC 𝔞.isOpen hUc
      (𝔞.max w hw) fun u hu => finAt_mem_of_integral w (𝔞.le hu)).1
    exact h1.mul_left h2.symm
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have hpos : (Oinf μ 𝔞.ν 𝔞.a₀).IsPositive := (ContinuousLinearMap.nonneg_iff_isPositive _).1 𝔞.pos
    have hadj : ContinuousLinearMap.adjoint (prj (fixF μ 𝔞.U)) = prj (fixF μ 𝔞.U) :=
      (isSelfAdjoint_starProjection _).adjoint_eq
    have h := hpos.conj_adjoint (prj (fixF μ 𝔞.U))
    rw [hadj] at h
    have e : prj (fixF μ 𝔞.U) ∘L Oinf μ 𝔞.ν 𝔞.a₀ ∘L prj (fixF μ 𝔞.U) = 𝔞.A := by
      show prj (fixF μ 𝔞.U) * (Oinf μ 𝔞.ν 𝔞.a₀ * prj (fixF μ 𝔞.U)) = Oinf μ 𝔞.ν 𝔞.a₀ * prj (fixF μ 𝔞.U)
      rw [← mul_assoc, ← (hOP _).eq, mul_assoc, hPP]
    rw [e] at h
    exact (ContinuousLinearMap.nonneg_iff_isPositive _).2 h
  · calc ‖𝔞.A‖ ≤ ‖Oinf μ 𝔞.ν 𝔞.a₀‖ * ‖prj (fixF μ 𝔞.U)‖ := ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ 1 * 1 := mul_le_mul 𝔞.norm_le (Submodule.starProjection_norm_le _) (norm_nonneg _) zero_le_one
      _ = 1 := one_mul 1
  · intro v
    have e : 𝔞.A v = prj (fixF μ 𝔞.U) (Oinf μ 𝔞.ν 𝔞.a₀ v) :=
      congrArg (fun S : LL μ →L[ℂ] LL μ => S v) (hOP 𝔞.a₀).eq
    rw [e]
    exact a1 _
  · exact (AdelicGLn.isCompact_integralFiniteGL K n).of_isClosed_subset (𝔞.U.isClosed_of_isOpen 𝔞.isOpen) 𝔞.le
  · intro x
    exact hcomp _ _ (hswap _ (hz x.1 x.2) _ hs).symm
  · intro x y
    refine hcomp _ _ ?_
    rw [hswap _ (hz x.1 x.2) _ (hsm _).1, hswap _ (hz y.1 y.2) _ (hsm _).1, ← (hmul _ _).1, ← (hmul _ _).1,
      (Subalgebra.mem_center_iff.1 (hz x.1 x.2) (zc y.1 y.2))]
  · intro w hw i
    refine ⟨(hHop w hw _ _).smul_right _, fun x => (hHop w hw _ _).smul_right _⟩
