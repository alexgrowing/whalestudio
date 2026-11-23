import Mathlib
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.ConvolutionSmoothL2
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RightConvolutionOperatorAeEqIntegralAdelic
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FiniteAdelicUnitaryCongruenceTopology
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AdelicUnitaryHaarBiInvariantStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RightRegularRepUnitaryStronglyContinuousStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.InvariantExtensionIntegrableOnCompactStatement

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec
open scoped InnerProductSpace ContDiff

namespace GlobalTheory.ConvContRep

theorem continuous_conv {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [LocallyCompactSpace G] [T2Space G] [FirstCountableTopology G] [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) (ψ f : G → ℂ) (hψ : Continuous ψ) (hc : HasCompactSupport ψ)
    (hf : AEStronglyMeasurable f μ) (hi : ∀ C, IsCompact C → IntegrableOn f C μ) :
    Continuous fun x => ∫ z, ψ (x⁻¹ * z) * f z ∂μ := by
  refine continuous_iff_continuousAt.2 fun x₀ => ?_
  obtain ⟨K, hK, hKx⟩ := exists_compact_mem_nhds x₀
  obtain ⟨C, hC⟩ := hψ.bounded_above_of_compact_support hc
  set L : Set G := (fun p : G × G => p.1 * p.2) '' (K ×ˢ tsupport ψ) with hLdef
  have hL : IsCompact L := (hK.prod hc.isCompact).image continuous_mul
  refine continuousAt_of_dominated
    (bound := fun z => C * L.indicator (fun z => ‖f z‖) z) ?_ ?_ ?_ ?_
  · exact Filter.Eventually.of_forall fun x =>
      ((hψ.comp (continuous_mul_left x⁻¹)).aestronglyMeasurable).mul hf
  · filter_upwards [hKx] with x hx
    refine Filter.Eventually.of_forall fun z => ?_
    by_cases hz : z ∈ L
    · rw [Set.indicator_of_mem hz, norm_mul]
      exact mul_le_mul_of_nonneg_right (hC _) (norm_nonneg _)
    · have h0 : ψ (x⁻¹ * z) = 0 := by
        refine image_eq_zero_of_notMem_tsupport fun hm => hz ?_
        exact ⟨(x, x⁻¹ * z), ⟨hx, hm⟩, mul_inv_cancel_left x z⟩
      simp [h0, Set.indicator_of_notMem hz]
  · exact (IntegrableOn.integrable_indicator (hi _ hL).norm hL.isClosed.measurableSet).const_mul C
  · refine Filter.Eventually.of_forall fun z => ?_
    have hz : Continuous fun x : G => ψ (x⁻¹ * z) * f z := by fun_prop
    exact hz.continuousAt

theorem conv_isContRep : ∀ (B : RowsAut) (ψ : B.I.GA → ℂ) (F : B.I.L2 B.μf B.fund), Continuous ψ → HasCompactSupport ψ → IsContRep B (∫ y, ψ y • B.R y F ∂(B.I.muA B.μf)) (fun x => ∫ z, ψ (x⁻¹ * z) * B.I.ext F z ∂(B.I.muA B.μf)) := by
  intro B ψ F hψ hc
  obtain ⟨iT2, iLC, iSC, -⟩ := GlobalTheory.CongTop.adelic_topology B.I
  have iK : IsFiniteMeasureOnCompacts (B.I.muA B.μf) := by
    unfold AutInst.muA
    infer_instance
  obtain ⟨hl, -, -, -, -⟩ := GlobalTheory.T.adelicUnitaryHaar_bi_invariant B.I B.μf
  have iL : (B.I.muA B.μf).IsMulLeftInvariant := ⟨hl⟩
  obtain ⟨-, -, hiso, hcontR, hext⟩ := GlobalTheory.T.rightRegularRep_unitary_stronglyContinuous B
  obtain ⟨hEinv, hEm⟩ := hext F
  unfold IsContRep
  refine ⟨?_, ?_, ?_⟩
  · exact continuous_conv _ ψ _ hψ hc hEm fun C hC => ((GlobalTheory.T.invariantExtension_integrableOn_compact B C hC).choose_spec F).1
  · intro γ hγ x
    calc ∫ z, ψ ((γ * x)⁻¹ * z) * B.I.ext F z ∂B.I.muA B.μf
        = ∫ w, ψ ((γ * x)⁻¹ * (γ * w)) * B.I.ext F (γ * w) ∂B.I.muA B.μf :=
          (integral_mul_left_eq_self (fun z => ψ ((γ * x)⁻¹ * z) * B.I.ext F z) γ).symm
      _ = ∫ w, ψ (x⁻¹ * w) * B.I.ext F w ∂B.I.muA B.μf := by
          refine integral_congr_ae ?_
          filter_upwards [hEinv] with w hw
          rw [hw γ hγ, _root_.mul_inv_rev, mul_assoc, inv_mul_cancel_left]
  · have hint : Integrable (fun y => ψ y • B.R y F) (B.I.muA B.μf) :=
      (hψ.smul (hcontR F)).integrable_of_hasCompactSupport hc.smul_right
    have hK : AEStronglyMeasurable (fun p : B.I.GA × B.I.GA => B.I.ext F (p.1 * p.2))
        (((B.I.muA B.μf).restrict B.fund).prod (B.I.muA B.μf)) :=
      hEm.comp_quasiMeasurePreserving
        (quasiMeasurePreserving_mul ((B.I.muA B.μf).restrict B.fund) (B.I.muA B.μf))
    have hw := (GlobalTheory.ConvKernel.weak_integral_ae_eq (fun x g => B.I.ext F (x * g)) hK
      (fun g => B.R g F) (fun g => B.R_spec g F) ‖F‖ (fun g => (hiso g F).le) ψ
      (hψ.integrable_of_hasCompactSupport hc) (∫ y, ψ y • B.R y F ∂B.I.muA B.μf)
      (fun u => by rw [← integral_inner (𝕜 := ℂ) hint u]; simp only [inner_smul_right])).2
    filter_upwards [hw] with x hx
    refine hx.trans ?_
    rw [← integral_mul_left_eq_self (fun z => ψ (x⁻¹ * z) * B.I.ext F z) x]
    simp only [inv_mul_cancel_left]

end GlobalTheory.ConvContRep
