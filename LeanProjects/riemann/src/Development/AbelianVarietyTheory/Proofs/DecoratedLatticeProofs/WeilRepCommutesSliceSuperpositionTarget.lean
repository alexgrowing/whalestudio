import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsQuasiFam
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ThetaAbsoluteSum
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.TransvectionAction
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.WeilDatumExistence
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ContinuousIsotropicSandwichMeanTranslation
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilOperatorIntegralCommOfBoundedFiniteMeasureStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsThetaFunSuperpositionTargetOrthSummandStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilOperatorTargetSummandPreservesThetaFunctionsStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

noncomputable section
namespace GlobalTheory.SliceSumTarget

theorem decomp_re_im (z : ℂ) : ((max z.re 0 : ℝ) : ℂ) + -1 * ((max (-z.re) 0 : ℝ) : ℂ) + Complex.I * ((max z.im 0 : ℝ) : ℂ) +
    -Complex.I * ((max (-z.im) 0 : ℝ) : ℂ) = z := by
  have h1 := max_zero_sub_max_neg_zero_eq_self z.re
  have h2 := max_zero_sub_max_neg_zero_eq_self z.im
  apply Complex.ext
  · simp
    linarith
  · simp
    linarith

theorem isThetaFunO_sliceT {D : D7} {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) {T A B S : HSp D}
    (o : OrthDec T A B) {F : WO S T → ℂ} (hF : IsThetaFunO ψ S T F) (y : WO S B) :
    IsThetaFunO ψ S A fun u => F ((o.resT S).symm (u, y)) := by
  have h := GlobalTheory.T.isThetaFun_superposition_target_orthSummand D ψ hψ T A B S o F hF Unit (Measure.dirac ()) (fun _ => y) (fun _ => 1) measurable_const
    (integrable_const _)
  simpa only [integral_dirac, one_mul] using h

theorem weil_comm_sliceSum_target : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (T A B S : HSp D) (o : OrthDec T A B) (χ χ' : ((AE D)ˣ →* Circle)) (om : Om S A), IsWeilDatumO ψ S A χ χ' om → ∀ (F : WO S T → ℂ), IsThetaFunO ψ S T F → ∀ (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω) (k : Ω → WO S B) (a : Ω → ℂ), Measurable k → Integrable a μ → ∀ p, IsThetaFunO ψ S T (fun x => om p (fun u => F ((o.resT S).symm (u, (o.resT S x).2))) (o.resT S x).1) ∧ ∀ u₀, om p (fun u => ∫ w, a w * F ((o.resT S).symm (u, k w)) ∂μ) u₀ = ∫ w, a w * om p (fun u => F ((o.resT S).symm (u, k w))) u₀ ∂μ := by
  intro D ψ T A B S o χ χ' om hW F hF Ω _ μ k a hk ha p
  have hψ := hW.std
  have h1 := GlobalTheory.T.weil_operator_target_summand_preserves_theta_functions D ψ T A B S o F hF χ χ' om hW p
  refine ⟨h1, fun u₀ => ?_⟩
  obtain ⟨-, -, iB3, -⟩ := lattice_Mx D B.rank S.rank
  haveI : BorelSpace (WO S B) := ⟨rfl⟩

  set Fs : WO S B → WO S A → ℂ := fun y u => F ((o.resT S).symm (u, y)) with hFs
  set G : WO S T → ℂ := fun x => om p (fun u => F ((o.resT S).symm (u, (o.resT S x).2))) (o.resT S x).1 with hG
  have hGs : ∀ y u, om p (Fs y) u = G ((o.resT S).symm (u, y)) := by
    intro y u; simp only [hG, hFs, AddEquiv.apply_symm_apply]
  have cFs : Continuous fun q : WO S B × WO S A => Fs q.1 q.2 :=
    hF.cont.comp ((o.continuous_resT_symm S).comp (continuous_snd.prodMk continuous_fst))
  have cGs : Continuous fun q : WO S B × WO S A => om p (Fs q.1) q.2 := by
    simp only [hGs]
    exact h1.cont.comp ((o.continuous_resT_symm S).comp (continuous_snd.prodMk continuous_fst))
  obtain ⟨CF, hCF⟩ := GlobalTheory.IsoMean.isThetaFunO_bounded S T ψ hψ F hF
  obtain ⟨CG, hCG⟩ := GlobalTheory.IsoMean.isThetaFunO_bounded S T ψ hψ G h1
  have bFs : ∀ y u, ‖Fs y u‖ ≤ CF := fun y u => hCF _
  have bGs : ∀ y u, ‖om p (Fs y) u‖ ≤ CG := fun y u => by rw [hGs]; exact hCG _

  have mF : ∀ u, AEStronglyMeasurable (fun w => Fs (k w) u) μ := fun u =>
    ((cFs.comp (continuous_id.prodMk continuous_const)).measurable.comp hk).aestronglyMeasurable
  have mG : AEStronglyMeasurable (fun w => om p (Fs (k w)) u₀) μ :=
    ((cGs.comp (continuous_id.prodMk continuous_const)).measurable.comp hk).aestronglyMeasurable

  let P : (Ω → ℂ) → Prop := fun c => Integrable c μ ∧
    om p (fun u => ∫ w, c w * Fs (k w) u ∂μ) u₀ = ∫ w, c w * om p (Fs (k w)) u₀ ∂μ
  have intF : ∀ c, Integrable c μ → ∀ u, Integrable (fun w => c w * Fs (k w) u) μ := fun c hc u => by
    have := hc.bdd_mul (mF u) (c := CF) (Filter.Eventually.of_forall fun w => bFs _ _)
    simpa only [mul_comm] using this
  have intG : ∀ c, Integrable c μ → Integrable (fun w => c w * om p (Fs (k w)) u₀) μ := fun c hc => by
    have := hc.bdd_mul mG (c := CG) (Filter.Eventually.of_forall fun w => bGs _ _)
    simpa only [mul_comm] using this
  have Padd : ∀ c₁ c₂, P c₁ → P c₂ → P (c₁ + c₂) := by
    intro c₁ c₂ h₁ h₂
    refine ⟨h₁.1.add h₂.1, ?_⟩
    have e1 : (fun u => ∫ w, (c₁ + c₂) w * Fs (k w) u ∂μ) =
        (fun u => ∫ w, c₁ w * Fs (k w) u ∂μ) + (fun u => ∫ w, c₂ w * Fs (k w) u ∂μ) := by
      funext u
      simp only [Pi.add_apply, add_mul]
      exact integral_add (intF _ h₁.1 u) (intF _ h₂.1 u)
    rw [e1, map_add, Pi.add_apply, h₁.2, h₂.2]
    simp only [Pi.add_apply, add_mul]
    exact (integral_add (intG _ h₁.1) (intG _ h₂.1)).symm
  have Psmul : ∀ (z : ℂ) c, P c → P (fun w => z * c w) := by
    intro z c h
    refine ⟨h.1.const_mul z, ?_⟩
    have e1 : (fun u => ∫ w, (z * c w) * Fs (k w) u ∂μ) = z • (fun u => ∫ w, c w * Fs (k w) u ∂μ) := by
      funext u
      simp only [Pi.smul_apply, smul_eq_mul, mul_assoc]
      exact integral_const_mul z _
    rw [e1, map_smul, Pi.smul_apply, smul_eq_mul, h.2]
    simp only [mul_assoc]
    exact (integral_const_mul z _).symm

  have Ppos : ∀ b : Ω → ℝ, Measurable b → (∀ w, 0 ≤ b w) → Integrable b μ → P (fun w => (b w : ℂ)) := by
    intro b hbm hb0 hbi
    refine ⟨hbi.ofReal, ?_⟩
    let ν : Measure (WO S B) := (μ.withDensity fun w => ((Real.toNNReal (b w) : NNReal) : ENNReal)).map k
    haveI : IsFiniteMeasure (μ.withDensity fun w => ((Real.toNNReal (b w) : NNReal) : ENNReal)) :=
      isFiniteMeasure_withDensity_ofReal hbi.2
    have tr : ∀ φ : WO S B → ℂ, Continuous φ → ∫ y, φ y ∂ν = ∫ w, (b w : ℂ) * φ (k w) ∂μ := by
      intro φ hφ
      rw [integral_map hk.aemeasurable hφ.aestronglyMeasurable,
        integral_withDensity_eq_integral_smul (hbm.real_toNNReal) _]
      refine integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
      simp only [NNReal.smul_def, Real.coe_toNNReal _ (hb0 w), Complex.real_smul]
    have hth : IsThetaFunO ψ S A fun u => ∫ y, Fs y u ∂ν := by
      have e : (fun u => ∫ y, Fs y u ∂ν) = fun u => ∫ w, (b w : ℂ) * F ((o.resT S).symm (u, k w)) ∂μ := by
        funext u
        exact tr (fun y => Fs y u) (cFs.comp (continuous_id.prodMk continuous_const))
      rw [e]
      exact GlobalTheory.T.isThetaFun_superposition_target_orthSummand D ψ hψ T A B S o F hF Ω μ k _ hk hbi.ofReal
    have hc := GlobalTheory.T.weilOperator_integral_comm_of_bounded_finiteMeasure D ψ S A χ χ' om hW (WO S B) ν Fs p (isThetaFunO_sliceT hψ o hF) cFs ⟨CF, bFs⟩ cGs
      ⟨CG, bGs⟩ hth u₀
    have e : (fun u => ∫ y, Fs y u ∂ν) = fun u => ∫ w, (b w : ℂ) * Fs (k w) u ∂μ := by
      funext u
      exact tr (fun y => Fs y u) (cFs.comp (continuous_id.prodMk continuous_const))
    rw [e] at hc
    rw [hc]
    exact tr (fun y => om p (Fs y) u₀) (cGs.comp (continuous_id.prodMk continuous_const))

  set a' := ha.1.mk a with ha'
  have hae : a =ᵐ[μ] a' := ha.1.ae_eq_mk
  have ha'm : Measurable a' := ha.1.stronglyMeasurable_mk.measurable
  have ha'i : Integrable a' μ := ha.congr hae
  have hre := ha'i.re
  have him := ha'i.im
  have mre : Measurable fun w => (a' w).re := Complex.measurable_re.comp ha'm
  have mim : Measurable fun w => (a' w).im := Complex.measurable_im.comp ha'm
  have P1 := Ppos _ (mre.max measurable_const) (fun w => le_max_right _ _) hre.pos_part
  have P2 := Psmul (-1) _ (Ppos _ (mre.neg.max measurable_const) (fun w => le_max_right _ _) hre.neg_part)
  have P3 := Psmul Complex.I _ (Ppos _ (mim.max measurable_const) (fun w => le_max_right _ _) him.pos_part)
  have P4 := Psmul (-Complex.I) _ (Ppos _ (mim.neg.max measurable_const) (fun w => le_max_right _ _) him.neg_part)
  have Pa' := Padd _ _ (Padd _ _ (Padd _ _ P1 P2) P3) P4
  have Pa'' : P a' := by
    convert Pa' using 1
    funext w
    simp only [Pi.add_apply, Pi.neg_apply]
    first
      | exact (decomp_re_im (a' w)).symm
      | exact decomp_re_im (a' w)
  have e1 : (fun u => ∫ w, a w * Fs (k w) u ∂μ) = fun u => ∫ w, a' w * Fs (k w) u ∂μ := by
    funext u; exact integral_congr_ae (hae.mono fun w hw => by simp only [hw])
  have e2 : ∫ w, a w * om p (Fs (k w)) u₀ ∂μ = ∫ w, a' w * om p (Fs (k w)) u₀ ∂μ :=
    integral_congr_ae (hae.mono fun w hw => by simp only [hw])
  have := Pa''.2
  simp only [hFs] at this e1 e2 ⊢
  rw [e1, e2]
  exact this

end GlobalTheory.SliceSumTarget
