import Mathlib
import GroundTheory.HeightsAndTheta.Heights.LatticeLemmas.IsProbabilityMeasureSphereLaw
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.ContinuousHermNormGroup
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial NumberField ComplexAt TensorProduct

noncomputable section

namespace HeightOfPointAlt

variable {K : Type*} [Field K] [NumberField K]

theorem adicAbv_sum_le (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) {ι : Type*} (s : Finset ι)
    (f : ι → K) {r : ℝ} (hr : 0 ≤ r)
    (hf : ∀ i ∈ s, NumberField.HeightOneSpectrum.adicAbv K v (f i) ≤ r) :
    NumberField.HeightOneSpectrum.adicAbv K v (∑ i ∈ s, f i) ≤ r := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using hr
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact (NumberField.HeightOneSpectrum.isNonarchimedean_adicAbv K v _ _).trans
      (max_le (hf a (Finset.mem_insert_self a s))
        (ih fun i hi => hf i (Finset.mem_insert_of_mem hi)))

theorem finite_adicAbv_ne_one {c : K} (hc : c ≠ 0) :
    {v : IsDedekindDomain.HeightOneSpectrum (𝓞 K) |
      NumberField.HeightOneSpectrum.adicAbv K v c ≠ 1}.Finite := by
  have hfin : (Function.mulSupport fun w : FinitePlace K => w c).Finite :=
    FinitePlace.hasFiniteMulSupport hc
  refine (hfin.preimage (FinitePlace.equivHeightOneSpectrum.symm.injective.injOn)).subset ?_
  intro v hv
  simp only [Set.mem_preimage, Function.mem_mulSupport,
    FinitePlace.equivHeightOneSpectrum_symm_apply, FinitePlace.norm_embedding]
  exact hv

variable {F : Type*} [Field F] [NumberField F] [Algebra F K]

omit [NumberField F] in

theorem adicAbv_intToField_le_one (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) (a : 𝓞 F) :
    NumberField.HeightOneSpectrum.adicAbv K v (intToField F K a) ≤ 1 := by
  let b : 𝓞 K := ⟨algebraMap F K (a : F), (RingOfIntegers.isIntegral_coe a).algebraMap⟩
  have hb : intToField F K a = algebraMap (𝓞 K) K b := rfl
  rw [hb]
  exact v.adicAbv_coe_le_one (NumberField.HeightOneSpectrum.one_lt_absNorm_nnreal v) b

variable {W : Type*} [AddCommGroup W] [Module (𝓞 F) W] [Module.Finite (𝓞 F) W]
  [Module.Projective (𝓞 F) W]

def archLinear (τ : K →+* ℂ) (yv : DualVec F W K) :
    Fibre (τ.comp (algebraMap F K)) W →ₗ[ℂ] ComplexAt (τ.comp (algebraMap F K)) where
  toFun := archFunctional τ yv
  map_add' := map_add _
  map_smul' c t := by
    induction t using TensorProduct.induction_on with
    | zero => simp only [smul_zero, map_zero]
    | tmul z e =>
      rw [TensorProduct.smul_tmul', RingHom.id_apply]
      simp only [archFunctional, TensorProduct.lift.tmul, LinearMap.mk₂_apply]
      exact smul_mul_assoc c z _
    | add s t hs ht => rw [smul_add, map_add, map_add, hs, ht, smul_add]

theorem archDualNorm_pos (h : HermitianMetric F W) (τ : K →+* ℂ) (yv : DualVec F W K) (x : W)
    (hx : yv x ≠ 0) : 0 < archDualNorm h τ yv := by
  set σ := τ.comp (algebraMap F K)
  let φ : FibreSpace h σ →ₗ[ℂ] ℂ := (ofComplex σ).symm.toLinearMap ∘ₗ archLinear τ yv ∘ₗ
    (FibreSpace.equiv h σ).symm.toLinearMap
  have hφ : ∀ ξ, φ ξ = (ofComplex σ).symm (archFunctional τ yv ((FibreSpace.equiv h σ).symm ξ)) :=
    fun _ => rfl
  let φc := LinearMap.toContinuousLinearMap φ
  have hbdd : BddAbove (Set.range fun ξ : {ξ : FibreSpace h σ // ‖ξ‖ ≤ 1} =>
      ‖(ofComplex σ).symm (archFunctional τ yv ((FibreSpace.equiv h σ).symm ξ))‖) := by
    refine ⟨‖φc‖, ?_⟩
    rintro _ ⟨ξ, rfl⟩
    show ‖φ ξ‖ ≤ _
    calc ‖φ ξ‖ = ‖φc ξ‖ := rfl
      _ ≤ ‖φc‖ * ‖(ξ : FibreSpace h σ)‖ := φc.le_opNorm _
      _ ≤ ‖φc‖ * 1 := mul_le_mul_of_nonneg_left ξ.2 (norm_nonneg φc)
      _ = ‖φc‖ := mul_one _
  set ξ₀ : FibreSpace h σ := FibreSpace.equiv h σ ((1 : ComplexAt σ) ⊗ₜ x)
  have hξ₀ : φ ξ₀ = τ (yv x) := by
    rw [hφ]
    simp only [ξ₀, LinearEquiv.symm_apply_apply, archFunctional, TensorProduct.lift.tmul,
      LinearMap.mk₂_apply, one_mul]
    rfl
  have hne : ξ₀ ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hξ₀
    exact (map_ne_zero τ).mpr hx hξ₀.symm
  set ξ₁ : FibreSpace h σ := ((‖ξ₀‖ : ℂ)⁻¹) • ξ₀
  have hξ₁ : ‖ξ₁‖ ≤ 1 := le_of_eq (norm_smul_inv_norm hne)
  have hφ₁ : φ ξ₁ ≠ 0 := by
    rw [map_smul, hξ₀, smul_eq_mul]
    refine mul_ne_zero (inv_ne_zero ?_) ((map_ne_zero τ).mpr hx)
    exact_mod_cast (norm_ne_zero_iff.mpr hne)
  calc (0 : ℝ) < ‖φ ξ₁‖ := norm_pos_iff.mpr hφ₁
    _ ≤ archDualNorm h τ yv := by
      rw [hφ]
      exact le_ciSup hbdd ⟨ξ₁, hξ₁⟩

end HeightOfPointAlt

open HeightOfPointAlt

theorem heightOfPoint : HeightOfPoint.Statement := by
  intro F _ _ W _ _ _ _ h n w hw K _ _ _ yv hyv
  have hspan : ∀ x : W, ∃ c : Fin n → 𝓞 F, ∑ k, c k • w k = x := fun x =>
    (Submodule.mem_span_range_iff_exists_fun (𝓞 F)).mp (hw ▸ Submodule.mem_top)
  have hyvx : ∀ c : Fin n → 𝓞 F, yv (∑ k, c k • w k) = ∑ k, intToField F K (c k) * yv (w k) := by
    intro c
    simp only [map_sum, map_smulₛₗ, smul_eq_mul]
  set M : IsDedekindDomain.HeightOneSpectrum (𝓞 K) → ℝ := fun v =>
    ⨆ k, NumberField.HeightOneSpectrum.adicAbv K v (yv (w k)) with hMdef
  have hM0 : ∀ v, 0 ≤ M v := fun v => Real.iSup_nonneg fun _ => AbsoluteValue.nonneg _ _
  have hleM : ∀ v k, NumberField.HeightOneSpectrum.adicAbv K v (yv (w k)) ≤ M v := fun v k =>
    by
    show _ ≤ ⨆ k, NumberField.HeightOneSpectrum.adicAbv K v (yv (w k))
    exact le_ciSup (f := fun k => NumberField.HeightOneSpectrum.adicAbv K v (yv (w k)))
      (Finite.bddAbove_range _) k
  have hle : ∀ v x, NumberField.HeightOneSpectrum.adicAbv K v (yv x) ≤ M v := by
    intro v x
    obtain ⟨c, rfl⟩ := hspan x
    rw [hyvx]
    refine adicAbv_sum_le v _ _ (hM0 v) fun k _ => ?_
    rw [map_mul]
    calc _ ≤ 1 * NumberField.HeightOneSpectrum.adicAbv K v (yv (w k)) :=
          mul_le_mul_of_nonneg_right (adicAbv_intToField_le_one v (c k)) (AbsoluteValue.nonneg _ _)
      _ ≤ M v := by rw [one_mul]; exact hleM v k
  have hdual : ∀ v, dualNormAt v yv = M v := by
    intro v
    have hbdd : BddAbove (Set.range fun x : W =>
        NumberField.HeightOneSpectrum.adicAbv K v (yv x)) := by
      refine ⟨M v, ?_⟩
      rintro _ ⟨x, rfl⟩
      exact hle v x
    unfold dualNormAt
    refine le_antisymm (Real.iSup_le (hle v) (hM0 v)) ?_
    exact Real.iSup_le (fun k => le_ciSup hbdd (w k))
      (Real.iSup_nonneg fun _ => AbsoluteValue.nonneg _ _)
  have hgauss : ∀ v, gaussNorm v (∑ k, C (yv (w k)) * X k : MvPolynomial (Fin n) K) = M v := by
    intro v
    rw [gaussNorm_eq_gaussNormOf]
    refine le_antisymm (gaussNormOf_le _ (hM0 v) fun m => ?_) ?_
    · rw [coeff_sum]
      refine adicAbv_sum_le v _ _ (hM0 v) fun k _ => ?_
      rw [coeff_C_mul, map_mul, coeff_X]
      split_ifs
      · rw [map_one, mul_one]; exact hleM v k
      · rw [map_zero, mul_zero]; exact hM0 v
    · refine Real.iSup_le (fun k => ?_) (gaussNormOf_nonneg _ _)
      have hc : coeff (Finsupp.single k 1) (∑ j, C (yv (w j)) * X j : MvPolynomial (Fin n) K) =
          yv (w k) := by
        rw [coeff_sum, Finset.sum_eq_single k]
        · rw [coeff_C_mul, coeff_X, if_pos rfl, mul_one]
        · intro j _ hj
          rw [coeff_C_mul, coeff_X, if_neg, mul_zero]
          intro hjk
          exact hj (Finsupp.single_left_injective one_ne_zero hjk)
        · intro hk; exact absurd (Finset.mem_univ k) hk
      rw [← hc]
      exact le_gaussNormOf _ _ _

  obtain ⟨k₀, hk₀⟩ : ∃ k, yv (w k) ≠ 0 := by
    by_contra hcon
    simp only [not_exists, ne_eq, not_not] at hcon
    apply hyv
    ext x
    obtain ⟨c, rfl⟩ := hspan x
    rw [hyvx]
    simp [hcon]
  have hMpos : ∀ v, 0 < M v := fun v =>
    lt_of_lt_of_le ((NumberField.HeightOneSpectrum.adicAbv K v).pos hk₀) (hleM v k₀)
  have hMfin : (Function.support fun v => Real.log (M v)).Finite := by
    refine (Set.Finite.biUnion (Set.toFinite {k | yv (w k) ≠ 0})
      fun k hk => finite_adicAbv_ne_one hk).subset ?_
    intro v hv
    by_contra hnot
    simp only [Set.mem_iUnion, Set.mem_ofPred_eq, not_exists, not_not] at hnot
    apply hv
    have h1 : M v = 1 := by
      refine le_antisymm (Real.iSup_le (fun k => ?_) zero_le_one) ?_
      · by_cases hk : yv (w k) = 0
        · rw [hk, map_zero]; exact zero_le_one
        · exact (hnot k hk).le
      · rw [← hnot k₀ hk₀]; exact hleM v k₀
    simp only [h1, Real.log_one]
  refine ⟨fun v => ⟨hdual v, (hdual v).trans (hgauss v).symm⟩, fun x hx => ?_⟩
  have hAfin : (Function.support fun v : IsDedekindDomain.HeightOneSpectrum (𝓞 K) =>
      Real.log (NumberField.HeightOneSpectrum.adicAbv K v (yv x))).Finite := by
    refine (finite_adicAbv_ne_one hx).subset ?_
    intro v hv h1
    apply hv
    simp only [h1, Real.log_one]
  have e1 : ∀ v, Real.log (NumberField.HeightOneSpectrum.adicAbv K v (yv x) / dualNormAt v yv) =
      Real.log (NumberField.HeightOneSpectrum.adicAbv K v (yv x)) - Real.log (M v) := by
    intro v
    rw [hdual, Real.log_div ((NumberField.HeightOneSpectrum.adicAbv K v).pos hx).ne' (hMpos v).ne']
  have e2 : ∀ τ : K →+* ℂ, Real.log (‖τ (yv x)‖ / archDualNorm h τ yv) =
      Real.log ‖τ (yv x)‖ - Real.log (archDualNorm h τ yv) := by
    intro τ
    exact Real.log_div (norm_ne_zero_iff.mpr ((map_ne_zero τ).mpr hx))
      (archDualNorm_pos h τ yv x hx).ne'
  have e3 : ∑ᶠ v : IsDedekindDomain.HeightOneSpectrum (𝓞 K), Real.log (dualNormAt v yv) =
      ∑ᶠ v, Real.log (M v) := finsum_congr fun v => by rw [hdual]
  unfold heightWith
  simp only [e1, e2]
  rw [finsum_sub_distrib hAfin hMfin, Finset.sum_sub_distrib, finsum_log_adicAbv hx,
    sum_log_norm_embeddings hx, e3]
  ring

theorem HeightOfPoint.proof (_h1 : GaussNormBasic.Statement) : HeightOfPoint.Statement :=
  heightOfPoint

end

end GroundTheory.Heights₂.Heights
