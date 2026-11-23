import Mathlib
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PRadicalTorusModulusDet
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PUnipotentModulusHaar
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.StatementsRadicalTorusModulus

namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open NumberField GroundTheory.Automorphic Module Matrix Topology MeasureTheory
open scoped ENNReal

noncomputable section

theorem map_eq_smul_of_coordinates {N V : Type*} [Group N] [TopologicalSpace N]
    [IsTopologicalGroup N] [LocallyCompactSpace N] [SecondCountableTopology N] [MeasurableSpace N]
    [BorelSpace N] [TopologicalSpace V] [MeasurableSpace V] [BorelSpace V] (lam : Measure V)
    [IsFiniteMeasureOnCompacts lam] [lam.IsOpenPosMeasure] (φ : V ≃ₜ N)
    (hL : ∀ n : N, MeasurePreserving (fun x => φ.symm (n * φ x)) lam lam)
    (T : V → V) (hT : Measurable T) (k : ℝ≥0∞) (hC : lam.map T = k • lam)
    (μ : Measure N) [μ.IsHaarMeasure] : μ.map (φ ∘ T ∘ φ.symm) = k • μ := by
  have hφ : Measurable φ := φ.continuous.measurable
  have hinv : (lam.map φ).IsMulLeftInvariant := by
    refine ⟨fun n => ?_⟩
    have e : (fun x => n * x) = φ ∘ (fun x => φ.symm (n * φ x)) ∘ φ.symm := by
      funext x
      simp
    rw [e, Measure.map_map (hφ.comp ((hL n).measurable.comp φ.symm.continuous.measurable)) hφ]
    have e' : (φ ∘ (fun x => φ.symm (n * φ x)) ∘ φ.symm) ∘ φ = φ ∘ (fun x => φ.symm (n * φ x)) := by
      funext x
      simp
    rw [e', ← Measure.map_map hφ (hL n).measurable, (hL n).map_eq]
  have : IsFiniteMeasureOnCompacts (lam.map φ) := by
    refine ⟨fun K hK => ?_⟩
    have e := φ.toMeasurableEquiv.map_apply (μ := lam) K
    simp only [Homeomorph.toMeasurableEquiv_coe] at e
    rw [e]
    exact (φ.isCompact_preimage.2 hK).measure_lt_top
  have : (lam.map φ).IsOpenPosMeasure := φ.continuous.isOpenPosMeasure_map φ.surjective
  have : (lam.map φ).IsHaarMeasure := {}
  rw [Measure.isMulLeftInvariant_eq_smul μ (lam.map φ), Measure.map_smul,
    Measure.map_map (hφ.comp (hT.comp φ.symm.continuous.measurable)) hφ]
  have e : (φ ∘ T ∘ φ.symm) ∘ φ = φ ∘ T := by
    funext x
    simp
  rw [e, ← Measure.map_map hφ hT, hC, Measure.map_smul, smul_comm]

variable {F E : Type*} [Field F] [Field E] [NumberField F] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [IsTotallyReal F] [IsTotallyComplex E]
variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem RadicalTorusModulus.proof (h : HermitianForm F E W) (v : Basis ι E W) :
    RadicalTorusModulus.Statement h v := by
  intro x₀ w₀ hp g α hga _ hgy μ _ f hf
  have : BorelSpace (unipRadical h v x₀) :=
    Subtype.borelSpace (unipRadical h v x₀ : Set (archUnitary h v))
  set φ := heisHomeo (v := v) hp with hφ
  set lam : Measure (HeisCoord h v x₀ w₀) :=
    (Measure.addHaar : Measure (heisY h v x₀ w₀)).prod volume with hlam
  set L : HeisCoord h v x₀ w₀ →ₗ[ℝ] HeisCoord h v x₀ w₀ :=
    (heisScale h v x₀ w₀ fun w => starRingEnd ℂ (α w)).prodMap
      (placeScale fun w => Complex.normSq (α w)) with hLdef
  have hα : ∀ w, α w ≠ 0 := by
    intro w h0
    obtain ⟨-, -, -, -, hab⟩ := hyperbolic_at_place h v hp w
    have e := congrArg (fun z => ((((g : InfinitePlace E → GL ι ℂ) w)⁻¹ : GL ι ℂ) : Matrix ι ι ℂ) *ᵥ z)
      (hga w)
    simp only [h0, zero_smul, mulVec_zero, mulVec_mulVec, Units.inv_mul, one_mulVec] at e
    rw [e, hForm, star_zero, zero_dotProduct] at hab
    exact zero_ne_one hab
  have hdet : LinearMap.det L = ∏ w, Complex.normSq (α w) ^ (Fintype.card ι - 1) := by
    rw [hLdef, LinearMap.det_prodMap, det_heisScale hp, det_placeScale, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun w _ => ?_
    have := finrank_heisYAt (v := v) hp w
    rw [Complex.normSq_conj, ← pow_succ]
    congr 1
    omega
  have hpos : 0 < LinearMap.det L := by
    rw [hdet]
    exact Finset.prod_pos fun w _ => pow_pos (Complex.normSq_pos.2 (hα w)) _
  have hLc : Measurable L := (LinearMap.continuous_of_finiteDimensional L).measurable
  have : BorelSpace (heisY h v x₀ w₀) := Subtype.borelSpace _
  have : lam.IsAddHaarMeasure := by
    rw [hlam]
    exact Measure.prod.instIsAddHaarMeasure _ _
  have hLm : lam.map L = ENNReal.ofReal |(LinearMap.det L)⁻¹| • lam :=
    Measure.map_linearMap_addHaar_eq_smul_addHaar lam hpos.ne'
  have hL : ∀ n, MeasurePreserving (fun x => φ.symm (n * φ x)) lam lam := by
    intro n
    obtain ⟨p, rfl⟩ := φ.surjective n
    set f : heisY h v x₀ w₀ → InfinitePlace E → ℝ := fun y w =>
      (hForm (gramAt h v w) ((p.1 : InfinitePlace E → ι → ℂ) w)
        ((y : InfinitePlace E → ι → ℂ) w)).im with hf
    have e : (fun x => φ.symm (φ p * φ x)) = fun x => (p.1 + x.1, (p.2 - f x.1) + x.2) := by
      funext x
      rw [hφ, heisHomeo_apply, heisHomeo_apply, heisPoint_mul, ← heisHomeo_apply,
        Homeomorph.symm_apply_apply]
      refine Prod.ext rfl ?_
      simp only [hf]
      abel
    rw [e]
    have hfc : Continuous f := continuous_pi fun w => Complex.continuous_im.comp
      (continuous_hForm_right _ _ ((continuous_apply w).comp continuous_subtype_val))
    refine MeasurePreserving.skew_product (f := fun y => p.1 + y)
      (g := fun y t => (p.2 - f y) + t) (measurePreserving_add_left _ p.1) ?_
      (Filter.Eventually.of_forall fun y => (measurePreserving_add_left volume _).map_eq)
    exact ((continuous_const.sub (hfc.comp continuous_fst)).add continuous_snd).measurable
  have hmap := map_eq_smul_of_coordinates lam φ hL L hLc _ hLm μ
  have hc : ∀ n, (((φ ∘ L ∘ φ.symm) n : unipRadical h v x₀) : archUnitary h v) = g * n * g⁻¹ := by
    intro n
    conv_rhs => rw [← φ.apply_symm_apply n]
    exact (heisPoint_torus hp g α hga hgy _).symm
  have hcm : Measurable (φ ∘ L ∘ φ.symm) :=
    φ.continuous.measurable.comp (hLc.comp φ.symm.continuous.measurable)
  have hfm : Measurable fun n : unipRadical h v x₀ => f n := hf.comp measurable_subtype_coe
  have hk : ENNReal.ofReal |(LinearMap.det L)⁻¹| =
      ∏ w, ‖α w‖ₑ⁻¹ ^ (2 * (finrank E W - 1)) := by
    rw [abs_of_pos (inv_pos.2 hpos), hdet, ← Finset.prod_inv_distrib,
      ENNReal.ofReal_prod_of_nonneg fun w _ => inv_nonneg.2 (pow_nonneg (Complex.normSq_nonneg _) _),
      Module.finrank_eq_card_basis v]
    refine Finset.prod_congr rfl fun w _ => ?_
    have hp' : 0 < ‖α w‖ := norm_pos_iff.2 (hα w)
    rw [Complex.normSq_eq_norm_sq, ← pow_mul, ← inv_pow, ENNReal.ofReal_pow (inv_nonneg.2 hp'.le),
      ENNReal.ofReal_inv_of_pos hp', ofReal_norm]
  calc ∫⁻ n, f (g * n * g⁻¹) ∂μ
      = ∫⁻ n, f (((φ ∘ L ∘ φ.symm) n : unipRadical h v x₀) : archUnitary h v) ∂μ :=
        lintegral_congr fun n => by rw [hc]
    _ = ∫⁻ n, f n ∂(μ.map (φ ∘ L ∘ φ.symm)) := (lintegral_map hfm hcm).symm
    _ = (∏ w, ‖α w‖ₑ⁻¹ ^ (2 * (finrank E W - 1))) * ∫⁻ n, f n ∂μ := by
        rw [hmap, lintegral_smul_measure, hk, smul_eq_mul]

end

end GroundTheory.Heights₂.Heights.FiniteCovolume
