import Development.AutomorphicArithmetic.Foundations.Convolution.TensFun
import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.TensApply
import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.InvSmooth
import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.Unimod
import GroundTheory.AutomorphicForms.CuspidalProjection.Global
import GroundTheory.AutomorphicForms.GKModules.Garding

open MeasureTheory NumberField IsDedekindDomain MvPolynomial
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C
open GroundTheory.Global
open scoped TensorProduct InnerProductSpace ComplexConjugate Pointwise ContDiff Manifold

section
variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸]
  {G : Subgroup 𝔸ˣ} {𝔤 : Submodule ℝ 𝔸} (h : IsExpLieAlgebra G 𝔤)

private theorem UpperTheory.ConvolutionTheory.Tf.leftSm_avg {S : Type*} [TopologicalSpace S] [T2Space S] [SecondCountableTopology S]
    [MeasurableSpace S] [OpensMeasurableSpace S] (ρ : Measure S) [IsFiniteMeasureOnCompacts ρ]
    {z : S → G} (hz : Continuous z) {β : G → ℂ} (hβ : h.IsSmoothFun β) (y : G)
    (hs : ∀ C : Set G, IsCompact C → ∃ D : Set S, IsCompact D ∧ ∀ a ∈ C, ∀ s ∉ D, β (a * y * z s) = 0) :
    h.IsSmoothFun (fun A => ∫ s, β (A * y * z s) ∂ρ) := by
  rw [h.isSmoothFun_iff]
  intro g
  set ψ : 𝔤 → G → ℂ := fun Y w => β (g * h.expG Y * w) with hψdef
  have hψ : ∀ w₀ : G, ContDiff ℝ ∞ (fun q : 𝔤 × 𝔤 => ψ q.1 (w₀ * h.expG q.2)) := by
    intro w₀
    let := h.chartedSpace
    have := h.lieGroup ∞
    have hm : ContMDiff 𝓘(ℝ, 𝔤 × 𝔤) 𝓘(ℝ, 𝔤) ∞
        (fun q : 𝔤 × 𝔤 => g * h.expG q.1 * (w₀ * h.expG q.2)) :=
      (contMDiff_const.mul (h.contMDiff_expG_comp contDiff_fst)).mul
        (contMDiff_const.mul (h.contMDiff_expG_comp contDiff_snd))
    exact (ContMDiff.comp (I' := 𝓘(ℝ, 𝔤)) hβ hm).contDiff
  set F : 𝔤 → S → ℂ := fun Y s => ψ Y (y * z s) with hFdef
  have e : (fun Y : 𝔤 => ∫ s, β (g * h.expG Y * y * z s) ∂ρ) = fun Y => ∫ s, F Y s ∂ρ := by
    funext Y
    congr 1
    funext s
    simp only [hFdef, hψdef, mul_assoc]
  show ContDiff ℝ ∞ (fun Y : 𝔤 => ∫ s, β (g * h.expG Y * y * z s) ∂ρ)
  rw [e]
  refine contDiff_integral_of_iteratedFDeriv F (fun s => ?_) (fun k => ?_) (fun Y₀ => ?_)
  · have e2 : (fun Y => F Y s) =
        (fun q : 𝔤 × 𝔤 => ψ q.1 ((y * z s) * h.expG q.2)) ∘ fun Y => (Y, (0 : 𝔤)) := by
      funext Y
      simp only [Function.comp_apply, h.expG_zero, mul_one, hFdef]
    rw [e2]
    exact (hψ _).comp (contDiff_id.prodMk contDiff_const)
  · exact (h.continuous_iteratedFDeriv_param ψ hψ k).comp
      (continuous_fst.prodMk (continuous_const.mul (hz.comp continuous_snd)))
  · obtain ⟨D, hD, hDz⟩ := hs ((fun Y => g * h.expG Y) '' Metric.closedBall Y₀ 1)
      ((isCompact_closedBall Y₀ 1).image (continuous_const.mul h.continuous_expG))
    refine ⟨Metric.closedBall Y₀ 1, Metric.closedBall_mem_nhds Y₀ one_pos, D, hD, fun Y hY s hsD => ?_⟩
    have h0 := hDz _ ⟨Y, hY, rfl⟩ s hsD
    simpa only [hFdef, hψdef, mul_assoc] using h0

end

private theorem UpperTheory.ConvolutionTheory.Tf.leftSm_inv (f : {r : ℝ // 0 < r} → ℂ) :
    ∫ s, f s⁻¹ ∂posRealMeasure = ∫ s, f s ∂posRealMeasure := by
  have hm : MeasurableEmbedding expPos := expPosHomeomorph.measurableEmbedding
  have hi : ∀ x, (expPos x)⁻¹ = expPos (-x) := fun x => by
    apply Subtype.ext
    simp [Real.exp_neg]
  rw [posRealMeasure_eq_map_expPos, hm.integral_map, hm.integral_map]
  simp_rw [hi]
  exact integral_neg_eq_self (fun x => f (expPos x)) volume

private theorem UpperTheory.ConvolutionTheory.Tf.leftSm_kbar {K : Type} [Field K] [NumberField K] {n : ℕ} (hn : 0 < n)
    (β : TI K n) (hβ : SmoothT β) (y : archGroup K n) :
    (isExpLieAlgebra K n).IsSmoothFun fun A : archGroup K n => kbar β (A * y) := by
  refine UpperTheory.ConvolutionTheory.Tf.leftSm_avg (isExpLieAlgebra K n) posRealMeasure continuous_zInf hβ y ?_
  intro C hC
  have hD : IsCompact (detA K n '' tsupport β) := β.hasCompactSupport.isCompact.image continuous_detA
  have hR : IsCompact (detA K n '' ((fun a => a * y) '' C)) :=
    (hC.image (continuous_id.mul continuous_const)).image continuous_detA
  refine ⟨(fun p : {r : ℝ // 0 < r} × {r : ℝ // 0 < r} => p.1 * p.2⁻¹) ''
    ((detA K n '' tsupport β) ×ˢ (detA K n '' ((fun a => a * y) '' C))),
    (hD.prod hR).image (continuous_fst.mul continuous_snd.inv), fun a ha s hs => ?_⟩
  by_contra hne
  apply hs
  refine ⟨(s * detA K n (a * y), detA K n (a * y)),
    ⟨mem_of_kernel_ne_zero hn hne, _, ⟨a, ha, rfl⟩, rfl⟩, ?_⟩
  simp only [mul_inv_cancel_right]

theorem UpperTheory.ConvolutionTheory.Tf.leftSm :
    ∀ (K : Type) [Field K] [NumberField K] (n : ℕ), 0 < n → ∀ (β : TI K n) (e : TF K n),
      (SmoothT β → (∃ U : Subgroup (AdelicGLn.FiniteAdelicGL K n), IsOpen (U : Set (AdelicGLn.FiniteAdelicGL K n)) ∧ ∀ u ∈ U, ∀ h, e (u * h) = e h) → IsLeftSmooth (tens β e)) ∧
      ∀ (β' : TI K n) (e' : TF K n), (∀ a, β' a = conj (β a⁻¹)) → (∀ h, e' h = conj (e h⁻¹)) →
        CuspidalProjection.ccStar (tens β e) = tens β' e' := by
  intro K _ _ n hn β e
  have hT : ∀ (β : TI K n) (e : TF K n) x, tens β e x = tensFun β e x :=
    fun β e => (UpperTheory.ConvolutionTheory.Tf.tensApply K n hn β e).1
  refine ⟨fun hβ ⟨U, hUo, hU⟩ => ⟨fun x => ?_, ?_⟩, fun β' e' hβ' he' => ?_⟩
  · have e1 : (fun A : archGroup K n => tens β e (archP K n A * x)) = fun A =>
        e (finPart K n (x : AdelicGLn.AdelicGL K n)) • kbar β (A * infPart K n (x : AdelicGLn.AdelicGL K n)) := by
      funext A
      have hk : kbar β (A * (zInf K n (detA K n A))⁻¹ * infPart K n (x : AdelicGLn.AdelicGL K n)) =
          kbar β (A * infPart K n (x : AdelicGLn.AdelicGL K n)) := by
        rw [← map_inv, mul_assoc, zInf_mul_comm, ← mul_assoc, kbar_mul_zInf]
      rw [hT, tensFun, Subgroup.coe_mul, map_mul, map_mul, infPart_archP, finPart_archP, one_mul, hk,
        smul_eq_mul, mul_comm]
    rw [e1]
    exact ((isExpLieAlgebra K n).smoothFuns (F := ℂ)).smul_mem _ (UpperTheory.ConvolutionTheory.Tf.leftSm_kbar hn β hβ _)
  · refine ⟨U.comap (AdelicGLn.integralFiniteGL K n).subtype, hUo.preimage continuous_subtype_val,
      fun u hu x => ?_⟩
    rw [hT, hT, tensFun, tensFun, Subgroup.coe_mul, coe_finOne, map_mul, map_mul, infPart_finEmb,
      finPart_finEmb, one_mul, hU (u : AdelicGLn.FiniteAdelicGL K n) hu]
  · have zInf_inv_comm : ∀ (s : {r : ℝ // 0 < r}) (a : archGroup K n), (zInf K n s)⁻¹ * a = a * (zInf K n s)⁻¹ := by
      intro s a
      rw [← map_inv, zInf_mul_comm]
    have hk : ∀ a, kbar β' a = conj (kbar β a⁻¹) := by
      intro a
      unfold kbar
      rw [← integral_conj, ← UpperTheory.ConvolutionTheory.Tf.leftSm_inv (fun s => conj (β (a⁻¹ * zInf K n s)))]
      congr 1
      funext s
      rw [hβ', map_inv (zInf K n) s, mul_inv_rev, zInf_inv_comm]
    ext g
    rw [CuspidalProjection.ccStar_apply, hT, hT, tensFun, tensFun, map_mul, he', hk, Subgroup.coe_inv,
      map_inv, map_inv]
