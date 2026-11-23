import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PseudoCoefficientUpqTrivial
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.DiscreteSeriesCharacter
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleCoefficientsAnalytic
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsAdmOnOfFiniteDimensional
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.IrreducibleUnitaryAdmissible
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PseudoCoefficientExistence
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.ModularCharacterEqOneOnExpHermitian
open MeasureTheory Matrix Filter Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.FlagMeas GlobalTheory.GKModule GlobalTheory.RealInd GlobalTheory.OpTrace
open GlobalTheory.SmoothGlob (lieSet)
open GlobalTheory.Dec (IsHaarSub HasInfChar IsSqIntIrr)
open GlobalTheory.Orb (ujMat ujRep CcMat IsBiFinite IsUnitEquiv IsCharFn IsRegSS cent HasOrbInt quotMeas)
open GlobalTheory.AutomorphicL2Unitary (IsTopIrreducible)
open GlobalTheory.HCChar GlobalTheory.Published GlobalTheory.Published.Langlands
open scoped InnerProductSpace Topology ENNReal ComplexConjugate

noncomputable section

namespace GlobalTheory.AvgRightLp

theorem integrable_of_continuous_K {n : ℕ} {ε : Fin n → Bool} {E : Type*} [NormedAddCommGroup E]
    {h : KG ε → E} (hh : Continuous h) : Integrable h (muK ε) :=
  integrableOn_univ.mp (hh.continuousOn.integrableOn_compact isCompact_univ)

instance isProbabilityMeasure_muK {n : ℕ} (ε : Fin n → Bool) : IsProbabilityMeasure (muK ε) :=
  ⟨by simpa [muK] using Measure.haarMeasure_self (G := KG ε) (K₀ := ⊤)⟩

theorem integrable_coeff_avg_right : ∀ (n : ℕ) (ε : Fin n → Bool) (μ : Measure (UJ ε)) [μ.IsHaarMeasure] (U : Type) [NormedAddCommGroup U] [InnerProductSpace ℂ U] [CompleteSpace U] (π : UJ ε →* (U →L[ℂ] U)), IsUnitaryRep π → ∀ (p : ℝ), 1 ≤ p → ∀ φ : KG ε → ℂ, Continuous φ → ∀ u u' : U, Integrable (fun g => ‖⟪u', π g u⟫_ℂ‖ ^ p) μ → Integrable (fun g => ‖⟪u', π g (∫ k, φ k • π k u ∂(muK ε))⟫_ℂ‖ ^ p) μ := by
  intro n ε μ _ U _ _ _ π hπ p hp φ hφ u u' hf
  haveI : μ.IsMulRightInvariant := by
    have hG : (muG ε).IsMulRightInvariant := ⟨fun g => Formalism.REAL.indefinite_unitary_unimodular n ε g⟩
    rw [Measure.isMulLeftInvariant_eq_smul μ (muG ε)]
    infer_instance
  have hp0 : (0 : ℝ) ≤ p := by linarith
  set f : UJ ε → ℂ := fun g => ⟪u', π g u⟫_ℂ with hfdef
  have hfc : Continuous f := continuous_const.inner (hπ.continuous_apply u)
  have hvc : Continuous fun k : KG ε => φ k • π (k : UJ ε) u :=
    hφ.smul ((hπ.continuous_apply u).comp continuous_subtype_val)
  have hvi := integrable_of_continuous_K hvc
  have hF : ∀ g, ⟪u', π g (∫ k, φ k • π k u ∂(muK ε))⟫_ℂ = ∫ k, φ k * f (g * k) ∂(muK ε) := by
    intro g
    rw [← (π g).integral_comp_comm hvi, ← integral_inner ((π g).integrable_comp hvi) u']
    congr 1
    funext k
    simp only [hfdef, map_smul, inner_smul_right, map_mul, ContinuousLinearMap.mul_apply]
  set M : ℝ := ‖BoundedContinuousFunction.mkOfCompact (⟨φ, hφ⟩ : C(KG ε, ℂ))‖ with hMdef
  have hM : ∀ k, ‖φ k‖ ≤ M := fun k =>
    (BoundedContinuousFunction.mkOfCompact (⟨φ, hφ⟩ : C(KG ε, ℂ))).norm_coe_le_norm k
  have hM0 : 0 ≤ M := norm_nonneg _
  have hjc : ∀ g : UJ ε, Continuous fun k : KG ε => f (g * k) := fun g =>
    hfc.comp (continuous_const.mul continuous_subtype_val)

  have hpt : ∀ g, ‖⟪u', π g (∫ k, φ k • π k u ∂(muK ε))⟫_ℂ‖ ^ p ≤
      M ^ p * ∫ k, ‖f (g * k)‖ ^ p ∂(muK ε) := by
    intro g
    rw [hF g]
    have h1 : ‖∫ k, φ k * f (g * k) ∂(muK ε)‖ ≤ M * ∫ k, ‖f (g * k)‖ ∂(muK ε) := by
      refine (norm_integral_le_integral_norm _).trans ?_
      rw [← integral_const_mul]
      refine integral_mono (integrable_of_continuous_K (hφ.mul (hjc g)).norm)
        (integrable_of_continuous_K (continuous_const.mul (hjc g).norm)) fun k => ?_
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right (hM k) (norm_nonneg _)
    have hJ : (∫ k, ‖f (g * k)‖ ∂(muK ε)) ^ p ≤ ∫ k, ‖f (g * k)‖ ^ p ∂(muK ε) :=
      (convexOn_rpow hp).map_integral_le (Real.continuous_rpow_const hp0).continuousOn isClosed_Ici
        (ae_of_all _ fun k => norm_nonneg (f (g * k)))
        (integrable_of_continuous_K (hjc g).norm)
        (integrable_of_continuous_K ((hjc g).norm.rpow_const fun _ => Or.inr hp0))
    calc ‖∫ k, φ k * f (g * k) ∂(muK ε)‖ ^ p ≤ (M * ∫ k, ‖f (g * k)‖ ∂(muK ε)) ^ p :=
          Real.rpow_le_rpow (norm_nonneg _) h1 hp0
      _ = M ^ p * (∫ k, ‖f (g * k)‖ ∂(muK ε)) ^ p :=
          Real.mul_rpow hM0 (integral_nonneg fun k => norm_nonneg _)
      _ ≤ M ^ p * ∫ k, ‖f (g * k)‖ ^ p ∂(muK ε) :=
          mul_le_mul_of_nonneg_left hJ (Real.rpow_nonneg hM0 p)

  have hprod : Integrable (fun q : UJ ε × KG ε => ‖f (q.1 * q.2)‖ ^ p) (μ.prod (muK ε)) := by
    have hqc : Continuous fun q : UJ ε × KG ε => ‖f (q.1 * q.2)‖ ^ p :=
      (hfc.comp (continuous_fst.mul (continuous_subtype_val.comp continuous_snd))).norm.rpow_const
        fun _ => Or.inr hp0
    rw [integrable_prod_iff' hqc.aestronglyMeasurable]
    refine ⟨ae_of_all _ fun k => hf.comp_mul_right (k : UJ ε), ?_⟩
    have : (fun k : KG ε => ∫ x, ‖‖f (x * k)‖ ^ p‖ ∂μ) = fun _ => ∫ x, ‖‖f x‖ ^ p‖ ∂μ :=
      funext fun k => integral_mul_right_eq_self (fun x => ‖‖f x‖ ^ p‖) (k : UJ ε)
    rw [this]
    exact integrable_const _
  have hdom : Integrable (fun g => M ^ p * ∫ k, ‖f (g * k)‖ ^ p ∂(muK ε)) μ :=
    hprod.integral_prod_left.const_mul _
  refine hdom.mono' ?_ (ae_of_all _ fun g => ?_)
  · exact ((continuous_const.inner (hπ.continuous_apply _)).norm.rpow_const
      fun _ => Or.inr hp0).aestronglyMeasurable
  · rw [Real.norm_of_nonneg (Real.rpow_nonneg (norm_nonneg _) p)]
    exact hpt g

end GlobalTheory.AvgRightLp
