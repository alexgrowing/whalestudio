import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EvIInfScaleMul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharacterInvariantAdelicFormEqMulEvalZeroStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepresentationPreservesSchwartz
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdelicSchwartzNeZeroAtOrigin
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisenbergWordL2Bound
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MeasurableThetaSumOfSchrodinger
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralInfiniteScalingStatement
open scoped TensorProduct NNReal Matrix ENNReal
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped Classical
noncomputable section
namespace GlobalTheory.TorusDilate

variable {F : Type} [Field F] [NumberField F]

theorem infScale_inv_mul (t : ℝ) (ht : t ≠ 0) (a : AF F) :
    GlobalTheory.TorusTheta.infScale F t⁻¹ * (GlobalTheory.TorusTheta.infScale F t * a) = a := by
  have h : GlobalTheory.TorusTheta.infScale F t⁻¹ * GlobalTheory.TorusTheta.infScale F t = 1 := by
    unfold GlobalTheory.TorusTheta.infScale
    refine Prod.ext ?_ ?_
    · show (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (algebraMap ℝ _ t⁻¹) *
        (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (algebraMap ℝ _ t) = 1
      rw [← map_mul, ← map_mul, inv_mul_cancel₀ ht, map_one, map_one]
    · show (1 : FiniteAdeleRing (𝓞 F) F) * 1 = 1
      exact one_mul 1
  rw [← mul_assoc, h, one_mul]

theorem proj_zero_mem_adm' (κ : Type) [Fintype κ] :
    (LinearMap.proj (R := ℂ) (φ := fun _ : (κ → AF F) => ℂ) 0) ∈ (adeleClass F).adm κ := by
  intro g _
  refine ⟨g 0 • (BoundedContinuousFunction.evalCLM ℂ 0).comp
    (SchwartzMap.toBoundedContinuousFunctionCLM ℂ (κ → mixedEmbedding.mixedSpace F) ℂ), fun f => ?_⟩
  simp only [LinearMap.proj_apply, pureA, ContinuousLinearMap.coe_smul', ContinuousLinearMap.coe_comp',
    Function.comp_apply, Pi.smul_apply, SchwartzMap.toBoundedContinuousFunctionCLM_apply,
    BoundedContinuousFunction.evalCLM_apply, smul_eq_mul]
  have h1 : (fun i : κ => InfiniteAdeleRing.ringEquiv_mixedSpace F ((0 : κ → AdeleRing (𝓞 F) F) i).1) = 0 := by
    funext i; exact map_zero (InfiniteAdeleRing.ringEquiv_mixedSpace F)
  have h2 : (fun i : κ => ((0 : κ → AdeleRing (𝓞 F) F) i).2) = 0 := by
    funext i; rfl
  rw [h1, h2, mul_comm]

theorem memLp_of_mem_schA {κ : Type} [Fintype κ] (μ : @Measure (κ → AF F) (borel _))
    (hμ : @Measure.IsAddHaarMeasure _ _ _ (borel _) μ) {Φ : (κ → AF F) → ℂ} (hΦ : Φ ∈ schA F κ) :
    (letI : MeasurableSpace (κ → AF F) := borel _; MemLp Φ 2 μ) := by
  letI mA : MeasurableSpace (κ → AF F) := borel _
  induction hΦ using Submodule.span_induction with
  | mem Φ h =>
    obtain ⟨f, g, hg, rfl⟩ := h
    exact GlobalTheory.ThetaSobolevBase.memLp_pureA μ hμ f hg
  | zero => exact MemLp.zero
  | add _ _ _ _ h1 h2 => exact h1.add h2
  | smul c _ _ h => exact h.const_smul c

theorem lintegral_sq_ne_zero {κ : Type} [Fintype κ] (μ : @Measure (κ → AF F) (borel _))
    (hμ : @Measure.IsAddHaarMeasure _ _ _ (borel _) μ) {Φ : (κ → AF F) → ℂ} (hc : Continuous Φ) (h0 : Φ 0 ≠ 0) :
    ∫⁻ x, ‖Φ x‖ₑ ^ 2 ∂μ ≠ 0 := by
  letI mA : MeasurableSpace (κ → AF F) := borel _
  haveI : BorelSpace (κ → AF F) := ⟨rfl⟩
  intro h
  have hm : AEMeasurable (fun x => ‖Φ x‖ₑ ^ 2) μ := (hc.measurable.enorm.pow_const 2).aemeasurable
  rw [lintegral_eq_zero_iff' hm] at h
  have h' : Φ =ᵐ[μ] 0 := h.mono fun x hx => by
    simpa using hx
  have := (hc.ae_eq_iff_eq μ continuous_const).1 h'
  exact h0 (congrFun this 0)

end GlobalTheory.TorusDilate

namespace GlobalTheory.TorusDilate

theorem main : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W)
    (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' →
    ∀ (g : UA σ X.J) (u : Fin n × Fin d → ℝ), (∀ j, 0 < u j) →
    (∀ z : Matrix (Fin n) (Fin d) (AE F E), M.co.e (mat g * z) =
      (fun j => GlobalTheory.TorusTheta.infScale F ((u j)⁻¹) * (M.co.e z).1 j,
       fun j => GlobalTheory.TorusTheta.infScale F (u j) * (M.co.e z).2 j)) →
    ∃ κ : ℂ, ‖κ‖ ^ 2 = ∏ j, u j ^ Module.finrank ℚ F ∧
      ∀ Φ ∈ schA F (Fin n × Fin d), ∀ x, om (g, 1) Φ x = κ * Φ (fun j => GlobalTheory.TorusTheta.infScale F (u j) * x j) := by
  intro F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP g u hu hg
  have hψ : IsStd B.ψ := hP.base.std
  have hS := IsUWeilPair.isUSplitting hP.weil
  have hact : ∀ w, actAB (cA σ) (g, (1 : UA σ W.J)) w = mat g * w := fun w => by
    simp [actAB, mat]
  have himpl : ∀ w, ∀ φ ∈ schA F (Fin n × Fin d),
      om (g, 1) (schr B.ψ (M.co.e w) φ) = schr B.ψ (M.co.e (mat g * w)) (om (g, 1) φ) := fun w φ hφ => by
    have := hS.impl (g, 1) w φ hφ
    rw [hact] at this
    exact this
  set l₁ : ((Fin n × Fin d → AF F) → ℂ) →ₗ[ℂ] ℂ :=
    (LinearMap.proj (R := ℂ) (φ := fun _ : (Fin n × Fin d → AF F) => ℂ) 0) ∘ₗ om (g, 1) with hl₁
  have hadm : l₁ ∈ (adeleClass F).adm (Fin n × Fin d) := hS.adm (g, 1) _ (proj_zero_mem_adm' _)
  obtain ⟨c, hc⟩ := GlobalTheory.T.character_invariant_adelic_form_eq_mul_eval_zero F B.ψ hψ (Fin n × Fin d) l₁ hadm (fun y φ hφ => by
    have e : (fun x => B.ψ (x ⬝ᵥ y) * φ x) = schr B.ψ (M.co.e (M.co.e.symm (0, y))) φ := by
      funext x; simp [schr]
    rw [e]
    simp only [hl₁, LinearMap.comp_apply, LinearMap.proj_apply]
    rw [himpl _ φ hφ, hg]
    (simp [schr, dotProduct]) <;> rfl)
  have hval : ∀ Φ ∈ schA F (Fin n × Fin d), ∀ x,
      om (g, 1) Φ x = c * Φ (fun j => GlobalTheory.TorusTheta.infScale F (u j) * x j) := fun Φ hΦ x => by
    set p : (Fin n × Fin d → AF F) × (Fin n × Fin d → AF F) :=
      (fun j => GlobalTheory.TorusTheta.infScale F (u j) * x j, 0) with hp
    have hmem := GlobalTheory.HeisSchA.schr_mem_schA B.ψ hψ p Φ hΦ
    have h1 := hc _ hmem
    simp only [hl₁, LinearMap.comp_apply, LinearMap.proj_apply] at h1
    have e : schr B.ψ p Φ = schr B.ψ (M.co.e (M.co.e.symm p)) Φ := by rw [LinearEquiv.apply_symm_apply]
    rw [e, himpl _ Φ hΦ, hg, LinearEquiv.apply_symm_apply] at h1
    have hx : (fun j => GlobalTheory.TorusTheta.infScale F (u j)⁻¹ * (GlobalTheory.TorusTheta.infScale F (u j) * x j)) = x :=
      funext fun j => infScale_inv_mul (u j) (hu j).ne' (x j)
    simp only [hp, hx] at h1
    simpa [schr, dotProduct] using h1
  refine ⟨c, ?_, hval⟩

  letI mA : MeasurableSpace (Fin n × Fin d → AF F) := borel _
  haveI : BorelSpace (Fin n × Fin d → AF F) := ⟨rfl⟩
  let μ : Measure (Fin n × Fin d → AF F) := Measure.addHaar
  have hμ : μ.IsAddHaarMeasure := inferInstance
  obtain ⟨Φ, hΦ, h0⟩ := GlobalTheory.SchANonzero.exists_mem_schA_ne_zero F (Fin n × Fin d)
  have hI0 : ∫⁻ x, ‖Φ x‖ₑ ^ 2 ∂μ ≠ 0 :=
    lintegral_sq_ne_zero μ hμ (GlobalTheory.ThetaTransformMeas.continuous_of_mem_schA (F := F) hΦ) h0
  have hIt : ∫⁻ x, ‖Φ x‖ₑ ^ 2 ∂μ ≠ ⊤ := by
    have h2 := (memLp_of_mem_schA μ hμ hΦ).eLpNorm_lt_top
    rw [eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top (by norm_num) (by norm_num)] at h2
    simpa using h2.ne
  have hU := hS.unit μ hμ (g, 1) Φ hΦ
  have hsc := GlobalTheory.T.lintegral_infinite_scaling F (Fin n × Fin d) u hu μ hμ (fun y => ‖Φ y‖ₑ ^ 2)
  simp only [hval Φ hΦ, enorm_mul, mul_pow] at hU
  rw [lintegral_const_mul' _ _ (by simp), hsc] at hU
  set P := ENNReal.ofReal (∏ j, u j ^ Module.finrank ℚ F) with hPdef
  have hPpos : 0 < ∏ j, u j ^ Module.finrank ℚ F := Finset.prod_pos fun j _ => pow_pos (hu j) _
  have hP0 : P ≠ 0 := by rw [hPdef]; exact (ENNReal.ofReal_pos.2 hPpos).ne'
  have hPt : P ≠ ⊤ := ENNReal.ofReal_ne_top
  have hk : ‖c‖ₑ ^ 2 * P⁻¹ = 1 := by
    rw [← mul_assoc] at hU
    exact (ENNReal.mul_eq_right hI0 hIt).1 hU
  have hk' : ‖c‖ₑ ^ 2 = P := by
    have := congrArg (· * P) hk
    simpa [mul_assoc, ENNReal.inv_mul_cancel hP0 hPt] using this
  have hk'' : ENNReal.ofReal (‖c‖ ^ 2) = ENNReal.ofReal (∏ j, u j ^ Module.finrank ℚ F) := by
    rw [← hPdef, ← hk', ← ofReal_norm, ENNReal.ofReal_pow (norm_nonneg _)]
  exact (ENNReal.ofReal_eq_ofReal_iff (by positivity) hPpos.le).1 hk''

end GlobalTheory.TorusDilate
