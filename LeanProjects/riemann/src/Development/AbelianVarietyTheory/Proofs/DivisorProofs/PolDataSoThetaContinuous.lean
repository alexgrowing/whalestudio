import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaBasicPropertiesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzOrbitDecayStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaLiftLeftInvariant
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MeasureFundDomLtTop
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryAdelicGroupTopology
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.ThKIntCont

theorem continuous_I_so : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' → ∀ Φ ∈ PolData B M ⊓ M.So B.ψ B.τ₁, Continuous (M.I om Φ) := by
  intro hKP F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP Φ hΦ
  have hb := GlobalTheory.T.theta_basic_properties hKP.base F E σ B n d X W M χX χW om r s r' s' hP
  have hS : Φ ∈ schA F (Fin n × Fin d) := GlobalTheory.ThKRatInv.polData_le_schA B M hP.good (Submodule.mem_inf.1 hΦ).1
  obtain ⟨C, k, hC⟩ := GlobalTheory.T.schwartz_orbit_decay hKP F E σ B n d X W M χX χW om r s r' s' hP Φ (Submodule.mem_inf.1 hΦ).2 0
  have hσ := GlobalTheory.SiegelSet.sigma_sigma hP.base.cm
  haveI := hP.good.haar
  have hvol : M.μ M.dom < ⊤ :=
    GlobalTheory.UnitaryVol.measure_fundDom_lt_top hKP.siegelSetUnitary hP.base.cm (GlobalTheory.UnitaryVol.isHermND_map hσ hP.herm)
      hP.good.dom
  haveI : BorelSpace (UA σ X.J) := ⟨rfl⟩
  have hθ : Continuous (fun x : UA σ X.J × UA σ W.J => theta om Φ x.1 x.2) := (hb.1 Φ hS).1
  have hht : Continuous (fun h : UA σ W.J => (ht h : ℝ)) :=
    Continuous.comp NNReal.continuous_coe (Continuous.comp (GlobalTheory.Grow.continuous_heightGL (F := F) (E := E)) continuous_subtype_val)
  haveI : SecondCountableTopology (UA σ W.J) := (GlobalTheory.UnitaryAdelicTop.lcsc_UA F E σ d W.J).2.2.1
  haveI : FirstCountableTopology (UA σ W.J) := TopologicalSpace.SecondCountableTopology.to_firstCountableTopology _
  refine continuous_iff_continuousAt.2 fun h₀ => ?_
  have hev : ∀ᶠ h in 𝓝 h₀, (ht h : ℝ) < ht h₀ + 1 := hht.continuousAt (Iio_mem_nhds (lt_add_one _))
  refine continuousAt_of_dominated (bound := fun _ => max C 0 * ((ht h₀ : ℝ) + 1) ^ k) ?_ ?_ ?_ ?_
  · exact Eventually.of_forall fun h => (hθ.comp (continuous_id.prodMk continuous_const)).aestronglyMeasurable
  · filter_upwards [hev] with h hh
    refine Eventually.of_forall fun g => ?_
    have h1 : (1 : ℝ) ≤ ht h := by exact_mod_cast GlobalTheory.AdelicU.one_le_heightGL (F := F) h.1
    have h2 := hC g h
    rw [pow_zero, mul_one] at h2
    calc ‖theta om Φ g h‖ ≤ C * (ht h : ℝ) ^ k := h2
      _ ≤ max C 0 * (ht h : ℝ) ^ k := mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
      _ ≤ max C 0 * ((ht h₀ : ℝ) + 1) ^ k :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hh.le _) (le_max_right _ _)
  · exact integrableOn_const hvol.ne
  · exact Eventually.of_forall fun g => (hθ.comp (continuous_const.prodMk continuous_id)).continuousAt

end GlobalTheory.ThKIntCont

end
