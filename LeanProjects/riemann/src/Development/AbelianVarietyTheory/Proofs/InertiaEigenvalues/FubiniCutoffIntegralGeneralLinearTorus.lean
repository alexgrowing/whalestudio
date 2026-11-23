import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LeftMulTau
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EtaleUnitsHaarMeasureDivAbsIsHaarMeasure
open GlobalTheory.JR Matrix MeasureTheory Filter Topology

namespace GlobalTheory.JR.LinDesc

theorem sigmaFinite_comap_of_measurable {X Y : Type} [MeasurableSpace X] [MeasurableSpace Y] (f : X → Y)
    (hf : Measurable f) (μ : Measure Y) [SigmaFinite μ] : SigmaFinite (μ.comap f) := by
  by_cases h : Function.Injective f ∧ ∀ s, MeasurableSet s → NullMeasurableSet (f '' s) μ
  · refine ⟨⟨⟨fun n => f ⁻¹' spanningSets μ n, fun _ => trivial, fun n => ?_, ?_⟩⟩⟩
    · rw [Measure.comap_apply₀ f μ h.1 h.2 ((measurableSet_spanningSets μ n).preimage hf).nullMeasurableSet]
      exact lt_of_le_of_lt (measure_mono (Set.image_preimage_subset _ _)) (measure_spanningSets_lt_top μ n)
    · rw [← Set.preimage_iUnion, iUnion_spanningSets, Set.preimage_univ]
  · rw [Measure.comap, dif_neg h]; infer_instance

theorem fubini_cutoff : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (r : ℕ) (τ : A.K) (p : Fin r → F) (hG : A.IsGen τ p) (M : Meas r F E) (μK : Measure A.K), μK.IsAddHaarMeasure → ∀ (α : GL (Fin r) F → ℝ) (Φ : GL (Fin r) F → ℂ), IsTest Φ → IsLocallyConstant α → HasCompactSupport α → (∀ g, 0 ≤ α g) → ∀ c : GL (Fin r) F, (∀ g, Φ g ≠ 0 → ∫ s, α (g * c * LinDesc.tm A hG s) ∂(LinDesc.unitsMeas A μK) = 1) → ∫ s, (letI := M.mG; ∫ g, Φ g * (α (g * c * LinDesc.tm A hG s) : ℂ) ∂M.μG) ∂(LinDesc.unitsMeas A μK) = (letI := M.mG; ∫ g, Φ g ∂M.μG) := by
  intro F E _ _ _ _ _ A r τ p hG M μK hμK α Φ hΦ hαlc hαcs hα0 c h1
  letI := M.mG
  haveI := M.bG
  haveI := M.haarG
  obtain ⟨hBor, hHaar, -⟩ := GlobalTheory.JR.LinDesc.unitsMeas_isHaar F E A μK hμK
  haveI := hBor
  haveI : LocallyCompactSpace F := Unram.lcF (F := F) (E := E)
  haveI : ProperSpace F := ProperSpace.of_locallyCompactSpace F
  haveI : SecondCountableTopology F := secondCountable_of_proper
  haveI : SecondCountableTopology (Matrix (Fin r) (Fin r) F) :=
    inferInstanceAs (SecondCountableTopology (Fin r → Fin r → F))
  haveI : SecondCountableTopology (Matrix (Fin r) (Fin r) F)ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.secondCountableTopology
  haveI : SecondCountableTopology (GL (Fin r) F) := Units.isEmbedding_embedProduct.secondCountableTopology
  haveI : T2Space (GL (Fin r) F) := Units.isEmbedding_embedProduct.t2Space
  have e := (LinDesc.bas A hG).equivFun
  have he1 : Continuous e := IsModuleTopology.continuous_of_linearMap e.toLinearMap
  have he2 : Continuous e.symm := IsModuleTopology.continuous_of_linearMap e.symm.toLinearMap
  haveI : SecondCountableTopology A.K := (Homeomorph.mk e.toEquiv he1 he2).secondCountableTopology
  haveI : SigmaFinite μK := inferInstance
  haveI : SigmaFinite (LinDesc.unitsMeas A μK) := by
    unfold LinDesc.unitsMeas
    haveI : SigmaFinite (μK.withDensity fun t => ENNReal.ofReal (A.absK t)⁻¹) :=
      SigmaFinite.withDensity_ofReal _
    exact sigmaFinite_comap_of_measurable _ (measurable_iff_comap_le.2 le_rfl) _
  have htm : Continuous (LinDesc.tm A hG) := Continuous.units_map _
    (IsModuleTopology.continuous_of_linearMap (Algebra.leftMulMatrix (LinDesc.bas A hG)).toLinearMap)
  have hΦc : Continuous Φ := hΦ.1.continuous
  have hαc : Continuous α := hαlc.continuous
  have hC : IsCompact (tsupport Φ) := hΦ.2
  have hz : ∀ g, g ∉ tsupport Φ → Φ g = 0 := fun g hg => image_eq_zero_of_notMem_tsupport hg
  haveI : IsFiniteMeasure (M.μG.restrict (tsupport Φ)) :=
    isFiniteMeasure_restrict.2 hC.measure_lt_top.ne
  set ν := LinDesc.unitsMeas A μK with hν
  set f : A.Kˣ → GL (Fin r) F → ℂ := fun s g => Φ g * (α (g * c * LinDesc.tm A hG s) : ℂ) with hf
  have hfc : Continuous (Function.uncurry f) := by
    refine (hΦc.comp continuous_snd).mul (Complex.continuous_ofReal.comp (hαc.comp ?_))
    exact (continuous_snd.mul continuous_const).mul (htm.comp continuous_fst)
  have hin : ∀ g, Integrable (fun s => f s g) ν := by
    intro g
    by_cases hg : Φ g = 0
    · simp [hf, hg]
    · have hi : Integrable (fun s => α (g * c * LinDesc.tm A hG s)) ν :=
        Integrable.of_integral_ne_zero (by rw [h1 g hg]; exact one_ne_zero)
      exact hi.ofReal.const_mul (Φ g)
  have hnorm : ∀ g, ∫ s, ‖f s g‖ ∂ν = ‖Φ g‖ := by
    intro g
    by_cases hg : Φ g = 0
    · simp [hf, hg]
    · simp only [hf, norm_mul, Complex.norm_real, Real.norm_of_nonneg (hα0 _)]
      rw [integral_const_mul, h1 g hg, mul_one]
  have hint : Integrable (Function.uncurry f) (ν.prod (M.μG.restrict (tsupport Φ))) := by
    rw [integrable_prod_iff' hfc.aestronglyMeasurable]
    refine ⟨Eventually.of_forall hin, ?_⟩
    exact (hΦc.norm.continuousOn.integrableOn_compact hC).congr (Eventually.of_forall fun g => (hnorm g).symm)
  have eL : ∀ s, ∫ g, f s g ∂M.μG = ∫ g in tsupport Φ, f s g ∂M.μG := fun s =>
    (setIntegral_eq_integral_of_forall_compl_eq_zero fun g hg => by simp [hf, hz g hg]).symm
  have eR : ∫ g, Φ g ∂M.μG = ∫ g in tsupport Φ, Φ g ∂M.μG :=
    (setIntegral_eq_integral_of_forall_compl_eq_zero fun g hg => hz g hg).symm
  show ∫ s, ∫ g, f s g ∂M.μG ∂ν = ∫ g, Φ g ∂M.μG
  simp_rw [eL, eR]
  rw [integral_integral_swap hint]
  refine integral_congr_ae (Eventually.of_forall fun g => ?_)
  by_cases hg : Φ g = 0
  · simp [hf, hg]
  · simp only [hf]
    rw [integral_const_mul, integral_complex_ofReal, h1 g hg, Complex.ofReal_one, mul_one]

end GlobalTheory.JR.LinDesc
