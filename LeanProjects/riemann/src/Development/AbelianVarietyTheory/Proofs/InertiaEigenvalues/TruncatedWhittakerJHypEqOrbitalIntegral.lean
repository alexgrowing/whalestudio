import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsTestRep
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EtaleHermitianPairStructureFactsStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NonemptyMeasAndReps
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DualCinvOKSmallStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EventuallyTestFunctionMulInverseUnitEqStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TruncatedWhittakerIntegralEqVolumeMulIntegralPerStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.VolumeScaledIntegersMulVolumeDualEqOneStatement
open GlobalTheory.JR Matrix MeasureTheory Filter Topology

noncomputable section

namespace GlobalTheory

theorem scale_integral : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (μK : Measure A.K), μK.IsAddHaarMeasure → ∀ (f : A.K → ℂ) (t : A.K), IsUnit t → ∫ b, f (t * b) ∂μK = ((A.absK t : ℂ))⁻¹ * ∫ s, f s ∂μK := by
  intro F E _ _ _ _ _ A μK hH f t ht
  have := Unram.lcF (F := F) (E := E); have := Unram.ultraF (F := F) (E := E)
  obtain ⟨_, _, _, _, -⟩ := GlobalTheory.JR.EtMeas.top_facts F A.K
  have hme : MeasurableEmbedding (fun b : A.K => ht.unit • b) := (Homeomorph.smul ht.unit).measurableEmbedding
  have hmap : Measure.map (fun b : A.K => ht.unit • b) μK =
      ((distribHaarChar A.K ht.unit : ENNReal))⁻¹ • μK := by
    ext S hS
    rw [hme.map_apply, Measure.smul_apply, smul_eq_mul]
    have h1 := distribHaarChar_mul μK ht.unit⁻¹ S
    rw [Set.preimage_smul, ← h1, map_inv, ENNReal.coe_inv (distribHaarChar_pos).ne']
  have hint : ∫ b, f (t * b) ∂μK = ∫ b, f b ∂(Measure.map (fun b : A.K => ht.unit • b) μK) := by
    rw [hme.integral_map]; rfl
  rw [hint, hmap, integral_smul_measure]
  simp [Et.absK, ht, Complex.real_smul]

theorem jHyp_wn : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (ψ : AddChar F ℂ) (μK : Measure A.K), μK.IsAddHaarMeasure → ∀ (φ' : A.K × A.K → ℂ) (z : A.K), A.jHyp μK ψ φ' (wS A.K * nS z) = ∫ t, (∫ b, φ' (b, t) * A.psiK ψ (t * z * b) ∂μK) * A.etaK t ∂μK := by
  intro F E _ _ _ _ _ A ψ μK hH φ' z
  have := Unram.lcF (F := F) (E := E); have := Unram.ultraF (F := F) (E := E)
  obtain ⟨_, _, _, _, -⟩ := GlobalTheory.JR.EtMeas.top_facts F A.K
  have : μK.IsNegInvariant := Measure.IsAddHaarMeasure.isNegInvariant_of_regular μK
  have h10 : ((wS A.K * nS z : SpecialLinearGroup (Fin 2) A.K) : Matrix (Fin 2) (Fin 2) A.K) 1 0 = -1 := by
    show (!![0, 1; -1, 0] * !![1, z; 0, 1] : Matrix (Fin 2) (Fin 2) A.K) 1 0 = -1
    simp [Matrix.mul_apply, Fin.sum_univ_two]
  have h11 : ((wS A.K * nS z : SpecialLinearGroup (Fin 2) A.K) : Matrix (Fin 2) (Fin 2) A.K) 1 1 = -z := by
    show (!![0, 1; -1, 0] * !![1, z; 0, 1] : Matrix (Fin 2) (Fin 2) A.K) 1 1 = -z
    simp [Matrix.mul_apply, Fin.sum_univ_two]
  have heta : ∀ t : A.K, A.etaK (-t) = A.etaK t := by
    intro t
    unfold Et.etaK
    have hg : ∀ x y : F, ‖x‖ = ‖y‖ → eta x = eta y := by
      intro x y h; unfold eta; rw [h]
    apply hg
    show ‖Algebra.norm F (-t)‖ = ‖Algebra.norm F t‖
    rw [show -t = algebraMap F A.K (-1) * t by simp, map_mul, Algebra.norm_algebraMap, norm_mul, norm_pow,
      norm_neg, norm_one, one_pow, one_mul]
  unfold Et.jHyp
  simp only [h10, h11]
  refine (integral_neg_eq_self _ μK).symm.trans ?_
  congr 1
  funext t
  simp only [mul_neg, mul_one, neg_neg, neg_mul, heta]
  rfl

theorem whittaker_jHyp_eq_orbK : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (ψ : AddChar F ℂ), IsStdChar ψ → ∀ (μK : Measure A.K), SelfDual μK (A.kerK ψ) → ∀ φ', IsTest φ' → ∀ a : A.K, IsUnit a → ∀ᶠ c in 𝓝[≠] (0 : F), A.abelian₂ μK ψ a (A.jHyp μK ψ φ') c = A.orbK μK φ' a := by
  intro F E _ _ _ _ _ A ψ hψ μK hμ φ' hφ a ha
  have hH : μK.IsAddHaarMeasure := hμ.1
  have hnull : μK {t : A.K | ¬ IsUnit t} = 0 := (GlobalTheory.T.etaleHermitianPair_structure_facts F E A).2.2.2.2.2.2.2.2.1 μK hH
  have hae : ∀ᵐ t ∂μK, IsUnit t := ae_iff.2 (by simpa using hnull)
  have hV : {v : A.K | ∀ t : A.K, IsUnit t → φ' ((a + v) * Ring.inverse t, t) = φ' (a * Ring.inverse t, t)}
      ∈ 𝓝 (0 : A.K) := by
    have h2 := GlobalTheory.T.eventually_testFunction_mul_inverse_unit_eq F E A φ' hφ a ha
    have hc : Tendsto (fun v : A.K => a + v) (𝓝 0) (𝓝 a) := by
      have := (continuous_add_left a).tendsto (0 : A.K)
      rwa [add_zero] at this
    exact hc h2
  filter_upwards [GlobalTheory.T.eventually_dual_scaled_OK_subset_nhds F E A ψ hψ _ hV, self_mem_nhdsWithin] with c hc hc0
  have hc0' : c ≠ 0 := hc0
  set M := {z : A.K | c • z ∈ A.OK} with hM
  set N := {y : A.K | ∀ x : A.K, c • x ∈ A.OK → A.psiK ψ (x * y) = 1} with hN
  obtain ⟨hNm, hvol⟩ := GlobalTheory.T.volume_scaledIntegers_mul_volume_dual_eq_one F E A ψ hψ μK hμ c hc0'
  have hLam : A.abelian₂ μK ψ a (A.jHyp μK ψ φ') c = (((μK M).toReal : ℝ) : ℂ) *
      ∫ t, (∫ b, φ' (b, t) * N.indicator (fun _ => (1 : ℂ)) (t * b - a) ∂μK) * A.etaK t ∂μK := by
    rw [← GlobalTheory.T.truncatedWhittakerIntegral_eq_volume_mul_integral_perp F E A ψ hψ μK hH φ' hφ a c hc0']
    unfold Et.abelian₂
    simp only [jHyp_wn F E A ψ μK hH φ']
  have hin : ∀ t : A.K, IsUnit t → (∫ b, φ' (b, t) * N.indicator (fun _ => (1 : ℂ)) (t * b - a) ∂μK) =
      ((A.absK t : ℂ))⁻¹ * (φ' (a * Ring.inverse t, t) * (((μK N).toReal : ℝ) : ℂ)) := by
    intro t ht
    have h4 := scale_integral F E A μK hH (fun s => φ' (Ring.inverse t * s, t) * N.indicator (fun _ => (1 : ℂ)) (s - a)) t ht
    simp only [Ring.inverse_mul_cancel_left t _ ht] at h4
    rw [h4]
    congr 1
    have h5 : (fun s => φ' (Ring.inverse t * s, t) * N.indicator (fun _ => (1 : ℂ)) (s - a)) =
        fun s => φ' (a * Ring.inverse t, t) * N.indicator (fun _ => (1 : ℂ)) (s - a) := by
      funext s
      by_cases hs : s - a ∈ N
      · have := hc hs t ht
        simp only [add_sub_cancel] at this
        rw [mul_comm (Ring.inverse t) s, this]
      · simp [Set.indicator_of_notMem hs]
    rw [h5, integral_const_mul]
    congr 1
    have h6 : ∫ s, N.indicator (fun _ => (1 : ℂ)) (s - a) ∂μK = ∫ s, N.indicator (fun _ => (1 : ℂ)) s ∂μK :=
      integral_sub_right_eq_self (fun s => N.indicator (fun _ => (1 : ℂ)) s) a
    rw [h6, integral_indicator_const _ hNm]
    rw [Complex.real_smul, mul_one]
    rfl
  have horb : A.orbK μK φ' a = ∫ t, φ' (a * Ring.inverse t, t) * A.etaK t * ((A.absK t : ℂ))⁻¹ ∂μK := by
    unfold Et.orbK
    rw [Measure.restrict_eq_self_of_ae_mem (s := {t : A.K | IsUnit t}) hae]
  rw [hLam, horb]
  have h7 : ∫ t, (∫ b, φ' (b, t) * N.indicator (fun _ => (1 : ℂ)) (t * b - a) ∂μK) * A.etaK t ∂μK =
      (((μK N).toReal : ℝ) : ℂ) * ∫ t, φ' (a * Ring.inverse t, t) * A.etaK t * ((A.absK t : ℂ))⁻¹ ∂μK := by
    rw [← integral_const_mul]
    refine integral_congr_ae ?_
    filter_upwards [hae] with t ht
    rw [hin t ht]
    ring
  rw [h7, ← mul_assoc, hvol, one_mul]

end GlobalTheory
