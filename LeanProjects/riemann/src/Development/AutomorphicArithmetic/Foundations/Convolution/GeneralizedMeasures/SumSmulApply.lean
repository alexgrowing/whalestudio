import Development.AutomorphicArithmetic.Foundations.Convolution.GeneralizedMeasures.HeckeFinAlt
import Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.DecayTraceClassAlt
import Development.AutomorphicArithmetic.AdelicQuotients.ExistsCompactFundamentalSetOfHeightLe

open MeasureTheory NumberField IsDedekindDomain MvPolynomial Filter
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum UpperTheory.ConvolutionTheory.C PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Geo
open GroundTheory.Global GroundTheory.Global.SemiLocal GroundTheory.Automorphic.Spherical
open UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.GM

namespace UpperTheory.ConvolutionTheory.GM

section

variable {K : Type} [Field K] [NumberField K] {n : ℕ} {μ : Measure (normOneGL K n)} [μ.IsHaarMeasure]

private theorem sum_smul_apply {ι : Type} (s : Finset ι) (c : ι → ℂ) (f : ι → TG K n) (g : normOneGL K n) :
    (∑ i ∈ s, c i • f i) g = ∑ i ∈ s, c i * f i g := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, CompactlySupportedContinuousMap.add_apply, ih]
    simp

private theorem rop_add (a b : TG K n) : Rop μ (a + b) = Rop μ a + Rop μ b := by
  have h : UnitaryRep.ccToL1 μ (a + b) = UnitaryRep.ccToL1 μ a + UnitaryRep.ccToL1 μ b := by
    unfold UnitaryRep.ccToL1
    rw [← MemLp.toLp_add]
    rfl
  unfold Rop
  rw [h]
  exact ContinuousLinearMap.map_add _ _ _

private theorem rop_smul (c : ℂ) (a : TG K n) : Rop μ (c • a) = c • Rop μ a := by
  have h : UnitaryRep.ccToL1 μ (c • a) = c • UnitaryRep.ccToL1 μ a := by
    unfold UnitaryRep.ccToL1
    rw [← MemLp.toLp_const_smul]
    rfl
  unfold Rop
  rw [h]
  exact ContinuousLinearMap.map_smul _ _ _

private theorem rop_zero : Rop μ (0 : TG K n) = 0 := by
  simpa using rop_smul (μ := μ) (0 : ℂ) (0 : TG K n)

private theorem rop_sum {ι : Type} (s : Finset ι) (c : ι → ℂ) (f : ι → TG K n) :
    Rop μ (∑ i ∈ s, c i • f i) = ∑ i ∈ s, c i • Rop μ (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using rop_zero
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, rop_add, rop_smul, ih]

private theorem twK_fin (θ : Twist μ) (f : TG K n) (x : normOneGL K n) :
    (Function.support fun γ : Gam K n => f (x⁻¹ * (γ : G1 K n) * θ.e x)).Finite :=
  finite_support_automorphicKernel (Gam K n) f (x, θ.e x)

private theorem twK_sum (θ : Twist μ) {ι : Type} (s : Finset ι) (c : ι → ℂ) (f : ι → TG K n)
    (x : normOneGL K n) : twK θ (∑ i ∈ s, c i • f i) x = ∑ i ∈ s, c i * twK θ (f i) x := by
  unfold twK
  simp only [sum_smul_apply]
  rw [finsum_sum_comm]
  · exact Finset.sum_congr rfl fun i _ => (mul_finsum _ _).symm
  · intro i _
    refine (twK_fin θ (f i) x).subset fun γ hγ h0 => hγ ?_
    simp only [Function.mem_support, not_not] at h0 ⊢
    simp only [Function.mem_support, ne_eq, Decidable.not_not] at *
    rw [h0, mul_zero]

private theorem twK_cont (θ : Twist μ) (f : TG K n) : Continuous (twK θ f) := by
  have h : Continuous fun x : normOneGL K n => automorphicKernel (Gam K n) f (x, θ.e x) :=
    (continuous_automorphicKernel (Gam K n) f).comp (continuous_id.prodMk θ.e.continuous)
  exact h

private theorem twK_left (θ : Twist μ) (f : TG K n) {δ : normOneGL K n} (hδ : δ ∈ Gam K n)
    (x : normOneGL K n) : twK θ f (δ * x) = twK θ f x := by
  have h1 := automorphicKernel_smul_left (Gam K n) f ⟨δ, hδ⟩ x (θ.e (δ * x))
  have h2 := automorphicKernel_smul_right (Gam K n) f ⟨θ.e δ, (θ.mem_gam δ).2 hδ⟩ x (θ.e x)
  have e1 : twK θ f (δ * x) =
      automorphicKernel (Gam K n) f ((⟨δ, hδ⟩ : Gam K n) • x, θ.e (δ * x)) := rfl
  have e2 : θ.e (δ * x) = (⟨θ.e δ, (θ.mem_gam δ).2 hδ⟩ : Gam K n) • θ.e x := by
    rw [map_mul]
    rfl
  rw [e1, h1, e2, h2]
  rfl

private theorem twKQ_mk (θ : Twist μ) (f : TG K n) (x : normOneGL K n) :
    twKQ θ f (mk (Gam K n) x) = twK θ f x := by
  obtain ⟨γ, hγ⟩ := mk_eq_mk_iff.1
    (show mk (Gam K n) (Quotient.out (mk (Gam K n) x)) = mk (Gam K n) x from Quotient.out_eq _)
  change twK θ f (Quotient.out (mk (Gam K n) x)) = _
  rw [← hγ]
  exact twK_left θ f γ.2 x

private theorem twKQ_int (θ : Twist μ) (f : TG K n) (Z : ℝ) (h : ∀ x, Z < qht x → twK θ f x = 0) :
    Integrable (twKQ θ f) (quotientMeasure (Gam K n) μ) := by
  haveI := Reduction.isFiniteMeasure_quotientMeasure (K := K) (n := n) μ
  have hc : Continuous (twKQ θ f) :=
    (isOpenQuotientMap_mk (Gam K n)).isQuotientMap.continuous_iff.2
      ((twK_cont θ f).congr fun x => (twKQ_mk θ f x).symm)
  obtain ⟨C, hC, hcov⟩ := UpperTheory.exists_compact_fundamental_set_of_height_le K n Z
  obtain ⟨M, hM⟩ := hC.exists_bound_of_continuousOn (twK_cont θ f).continuousOn
  refine Integrable.of_bound hc.aestronglyMeasurable (max M 0) (Eventually.of_forall fun y => ?_)
  change ‖twK θ f (Quotient.out y)‖ ≤ _
  by_cases hz : Z < qht (Quotient.out y)
  · rw [h _ hz, norm_zero]
    exact le_max_right _ _
  · obtain ⟨g, hg, c, hc', e⟩ := hcov _ (not_lt.1 hz)
    rw [e, twK_left θ f hg]
    exact (hM c hc').trans (le_max_left _ _)

end

end UpperTheory.ConvolutionTheory.GM

theorem UpperTheory.ConvolutionTheory.GM.twLin :
    TwLin := by
  intro K _ _ n _ μ _ θ ι s c f Z h
  refine ⟨rop_sum s c f, fun x hx => ?_, ?_⟩
  · rw [twK_sum]
    exact Finset.sum_eq_zero fun i hi => by rw [h i hi x hx, mul_zero]
  · have e : ∀ y, twKQ θ (∑ i ∈ s, c i • f i) y = ∑ i ∈ s, c i * twKQ θ (f i) y :=
      fun y => twK_sum θ s c f _
    unfold twInt
    simp only [e]
    rw [integral_finset_sum _ fun i hi => (twKQ_int θ (f i) Z (h i hi)).const_mul _]
    simp only [integral_const_mul]
