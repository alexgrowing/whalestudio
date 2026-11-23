import Development.AutomorphicArithmetic.Foundations.Convolution.BlockHeckeSlices.DatDatum
import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.RrTens
import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.PrjFix
import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.CompatEx
import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.LactSpec
import Development.AutomorphicArithmetic.WhittakerHecke.FiniteTranslatesMatrixCoefficient
import Development.AutomorphicArithmetic.WhittakerHecke.TensorTestFunctionInvariantAndFiniteDimensionalS
import Development.AutomorphicArithmetic.WhittakerHecke.LiftOneRconvMemArchSmoothAndEnvelopingActionEq
import Development.AutomorphicArithmetic.WhittakerHecke.LiftOneRconvTensorModerateGrowthUniform
import Development.AutomorphicArithmetic.WhittakerHecke.ZCSuccEqAndEnvelopingActionCompatible
import Development.AutomorphicArithmetic.WhittakerHecke.LocGLEqLocalEmbeddingAndKGLEqIntegralGL

open NumberField

section SlopeTestRemainingChoices

open MeasureTheory IsDedekindDomain GlobalTheory.CuspRep
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.BW UpperTheory.V

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {n : ℕ}
  {μ : Measure (normOneGL E n)} [μ.IsHaarMeasure]

private theorem ampRep_open {φ : Sm E n} {U : Subgroup (AdelicGLn.FiniteAdelicGL E n)}
    (hU : IsOpen (U : Set (AdelicGLn.FiniteAdelicGL E n))) (h : ∀ u ∈ U, GlobalTheory.CuspRep.finRep E n u φ = φ) :
    IsOpen {k | GlobalTheory.CuspRep.finRep E n k φ = φ} := by
  let S : Subgroup (GL (Fin n) (Af E)) :=
    { carrier := {k | GlobalTheory.CuspRep.finRep E n k φ = φ}
      one_mem' := by simp
      mul_mem' := fun {k l} hk hl => by
        change GlobalTheory.CuspRep.finRep E n (k * l) φ = φ
        rw [map_mul, Module.End.mul_apply, hl, hk]
      inv_mem' := fun {k} hk => by
        change GlobalTheory.CuspRep.finRep E n k⁻¹ φ = φ
        conv_lhs => rw [← show GlobalTheory.CuspRep.finRep E n k φ = φ from hk, ← Module.End.mul_apply, ← map_mul,
          inv_mul_cancel, map_one]
        rfl }
  exact Subgroup.isOpen_mono (H₁ := U) (H₂ := S) h hU

private theorem ampRep_fix {f : TG E n} {v : LL μ} {φ : Sm E n}
    (hφ : φ.1 = liftOne (rconv (rationalGLOne E n) μ f v)) {u : AdelicGLn.FiniteAdelicGL E n}
    (h : ∀ z, f ((MultiplicityOne.finProj E n u)⁻¹ * z) = f z) : GlobalTheory.CuspRep.finRep E n u φ = φ := by
  refine Subtype.ext (funext fun g => ?_)
  change φ.1 (g * finGL E n u) = φ.1 g
  have e : retractOne (finGL E n u) = MultiplicityOne.finProj E n u := by
    rw [← Fb.finEmb_eq]; rfl
  simp only [hφ, liftOne, retractOne_mul, e, rconv, mul_inv_rev, mul_assoc, h]

private theorem ampRep_rep {f : TG E n} {v : LL μ} {φ : Sm E n}
    (hφ : φ.1 = liftOne (rconv (rationalGLOne E n) μ f v)) (hl : IsOpen {k | GlobalTheory.CuspRep.finRep E n k φ = φ})
    (hg : ∃ N : ℕ, ∀ u : Cm.UC E n, ∃ B : ℝ, ∀ g, ‖(Cm.uC E n u φ).1 g‖ ≤ B * AutomorphicForm.height g ^ N) :
    Rep μ (RR μ f v) φ := by
  have hc := isContRep_rconv μ f v
  refine ⟨⟨fun γ g => ?_, hl, hg⟩, fun t g => ?_, ?_⟩
  · rw [hφ]
    have hγ1 : AdelicGLn.diagonal E n γ ∈ normOneGL E n := rationalGL_le_normOneGL ⟨γ, rfl⟩
    have hγΓ : (⟨AdelicGLn.diagonal E n γ, hγ1⟩ : normOneGL E n) ∈ rationalGLOne E n := ⟨γ, rfl⟩
    exact (congrArg (rconv (rationalGLOne E n) μ f v) (retractOne_coe_mul ⟨_, hγ1⟩ g)).trans (hc.2.1 _ hγΓ _)
  · rw [hφ]
    exact liftOne_centralSection_mul _ _ g
  · filter_upwards [hc.ae_eq_quotFun] with y hy
    exact hy.trans (((congrFun hφ _).trans (liftOne_coe _ _)).trans
      ((quotFun_mk _ hc.2.1 _).symm.trans (congrArg (quotFun _ hc.2.1) (Quotient.out_eq y)))).symm

private theorem ampRep_killed {f : TG E n} {v : LL μ} {d : ℕ} {ρ : KA E n → Matrix (Fin d) (Fin d) ℂ}
    (h : ∀ x : KA E n →₀ ℂ, (x.sum fun k c => c • ρ k) = 0 →
      ∀ z, (x.sum fun k c => c * f ((Subgroup.inclusion maxCompact_le_normOneGL k)⁻¹ * z)) = 0) :
    Killed ρ (liftOne (rconv (rationalGLOne E n) μ f v)) := by
  intro x hx g
  have e : ∀ k : KA E n, retractOne (g * (k : GA E n)) =
      retractOne g * Subgroup.inclusion maxCompact_le_normOneGL k :=
    fun k => retractOne_mul_coe g (Subgroup.inclusion maxCompact_le_normOneGL k)
  simp only [Finsupp.sum, liftOne, e, rconv, ← integral_const_mul]
  rw [← integral_finsetSum _ fun k _ => (integrable_rconv _ μ f v _).const_mul _]
  refine integral_eq_zero_of_ae (Filter.Eventually.of_forall fun y => ?_)
  have := h x hx ((retractOne g)⁻¹ * y)
  simp only [Finsupp.sum] at this
  simp only [mul_inv_rev, mul_assoc (Subgroup.inclusion maxCompact_le_normOneGL _)⁻¹, ← mul_assoc (x _),
    ← Finset.sum_mul, this, zero_mul, Pi.zero_apply]

end SlopeTestRemainingChoices

open MeasureTheory IsDedekindDomain GlobalTheory.CuspRep
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.V in
theorem UpperTheory.ConvolutionTheory.BW.ampRep :
    ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E], UpperTheory.ConvolutionTheory.BW.AmpRep E := by
  intro E _ _ _ n μ _ 𝔞 hn
  obtain ⟨m, _, hm⟩ := (Tf.compatEx E n hn).2.1 μ 𝔞.ν
  have hUc : IsCompact (𝔞.U : Set (AdelicGLn.FiniteAdelicGL E n)) :=
    (AdelicGLn.isCompact_integralFiniteGL E n).of_isClosed_subset (𝔞.U.isClosed_of_isOpen 𝔞.isOpen) 𝔞.le
  obtain ⟨e, he, heP⟩ := Tf.prjFix E n μ m 𝔞.U 𝔞.isOpen hUc
  have heU : ∀ u ∈ 𝔞.U, ∀ h, e (u * h) = e h := fun u hu h => by
    rw [he, he]
    classical
    rw [Set.indicator_apply, Set.indicator_apply]
    exact if_congr (𝔞.U.mul_mem_cancel_left hu) rfl rfl
  have hR : ∀ β, Oinf μ 𝔞.ν β ∘L prj (fixF μ 𝔞.U) = RR μ (tens β e) := fun β => by
    rw [Tf.rrTens E n hn μ 𝔞.ν m hm, heP]
  have hder := UpperTheory.liftOne_rconv_mem_archSmooth_and_envelopingAction_eq E n hn μ 𝔞.ν m hm
  have huC : ∀ β, SmoothT β → ∀ (v : LL μ) (φ : Sm E n), φ.1 = liftOne (rconv (rationalGLOne E n) μ (tens β e) v) →
      ∀ u, (Cm.uC E n u φ).1 = liftOne (rconv (rationalGLOne E n) μ (tens (lact u β) e) v) := fun β hβ v φ hφ u => by
    obtain ⟨h, hh⟩ := hder β e hβ v
    rw [(UpperTheory.zC_succ_eq_and_envelopingAction_compatible E n).2, ← hh u]
    exact congrArg (fun ψ => (uAct u ψ).1) (Subtype.ext hφ)
  have hfix : ∀ β (v : LL μ) (φ : Sm E n), φ.1 = liftOne (rconv (rationalGLOne E n) μ (tens β e) v) →
      ∀ u ∈ 𝔞.U, GlobalTheory.CuspRep.finRep E n u φ = φ := fun β v φ hφ u hu =>
    ampRep_fix hφ ((UpperTheory.tensorTestFunction_invariant_and_finiteDimensional_span E n hn β e 𝔞.U 𝔞.le 𝔞.isOpen heU).1 u hu)
  have hrep : ∀ β, SmoothT β → ∀ (v : LL μ) (φ : Sm E n), φ.1 = liftOne (rconv (rationalGLOne E n) μ (tens β e) v) →
      Rep μ ((Oinf μ 𝔞.ν β ∘L prj (fixF μ 𝔞.U)) v) φ := fun β hβ v φ hφ => by
    rw [hR]
    obtain ⟨N, hN⟩ := UpperTheory.liftOne_rconv_tensor_moderateGrowth_uniform E n hn μ 𝔞.ν m hm β e hβ
    refine ampRep_rep hφ (ampRep_open 𝔞.isOpen (hfix β v φ hφ)) ⟨N, fun u => ?_⟩
    obtain ⟨B, hB⟩ := hN u
    exact ⟨B * ‖v‖, fun g => by rw [huC β hβ v φ hφ]; exact hB v g⟩
  let L : LL μ →ₗ[ℂ] Sm E n :=
    { toFun := fun v => ⟨liftOne (rconv (rationalGLOne E n) μ (tens 𝔞.a₀ e) v),
        (Cm.sm_eq E n).ge (hder 𝔞.a₀ e 𝔞.smooth v).1⟩
      map_add' := fun v w => Subtype.ext (funext fun g => rconv_add _ μ _ v w _)
      map_smul' := fun c v => Subtype.ext (funext fun g => rconv_smul _ μ _ c v _) }
  obtain ⟨d, ρ, hρ, hk⟩ := UpperTheory.finite_translates_matrix_coefficient (KA E n) (normOneGL E n) (Subgroup.inclusion maxCompact_le_normOneGL)
    (continuous_subtype_val.subtype_mk _) (tens 𝔞.a₀ e) (tens 𝔞.a₀ e).continuous
    ((UpperTheory.tensorTestFunction_invariant_and_finiteDimensional_span E n hn 𝔞.a₀ e 𝔞.U 𝔞.le 𝔞.isOpen heU).2 𝔞.fin)
  obtain ⟨N, hN⟩ := UpperTheory.liftOne_rconv_tensor_moderateGrowth_uniform E n hn μ 𝔞.ν m hm 𝔞.a₀ e 𝔞.smooth
  refine ⟨⟨d, ρ, hρ⟩, N, L, fun v => ⟨hrep _ 𝔞.smooth v _ rfl, ampRep_killed hk, fun w hw k hk => ?_⟩,
    fun u => ?_, fun x v => ?_⟩
  · refine hfix _ v _ rfl (locGL E n w k) (𝔞.max w hw ⟨k, ?_, ((UpperTheory.locGL_eq_localEmbedding_and_KGL_eq_integralGL E n w).1 k).symm⟩)
    rw [← (UpperTheory.locGL_eq_localEmbedding_and_KGL_eq_integralGL E n w).2]
    exact hk
  · obtain ⟨B, hB⟩ := hN u
    exact ⟨B, fun v g => by rw [huC _ 𝔞.smooth v (L v) rfl]; exact hB v g⟩
  · obtain ⟨_, -, hs, -⟩ := Tf.lactSpec E n 𝔞.a₀ 𝔞.smooth
    refine hrep _ (hs _).1 v _ ?_
    rw [← huC _ 𝔞.smooth v (L v) rfl, ← (UpperTheory.zC_succ_eq_and_envelopingAction_compatible E n).1, zop, evZ, MvPolynomial.aeval_X]
