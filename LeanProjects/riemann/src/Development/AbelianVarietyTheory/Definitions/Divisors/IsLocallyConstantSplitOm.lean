import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilObjectsInhabited

noncomputable section

open MeasureTheory Matrix ValuativeRel Filter
open scoped NNReal Topology Kronecker

namespace GlobalTheory.WeilM

theorem isLocallyConstant_orbit {G V : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup V]
    [Module ℂ V] (om : G →* Module.End ℂ V) {v : V} (h : ∀ᶠ g in 𝓝 (1 : G), om g v = v) :
    IsLocallyConstant fun g => om g v := by
  refine (IsLocallyConstant.iff_eventually_eq _).mpr fun g₀ => ?_
  have : Tendsto (fun g => g₀⁻¹ * g) (𝓝 g₀) (𝓝 1) := Continuous.tendsto' (by fun_prop) _ _ (inv_mul_cancel _)
  filter_upwards [this.eventually h] with g hg
  conv_rhs => rw [← hg, ← Module.End.mul_apply, ← map_mul, mul_inv_cancel_left]

theorem eventually_comp_eq {P V : Type} [TopologicalSpace P] [TopologicalSpace V] {p₀ : P} (f g : P → V → V)
    (hf : Continuous fun q : P × V => f q.1 q.2) (hg : Continuous fun q : P × V => g q.1 q.2)
    (f0 : ∀ v, f p₀ v = v) (g0 : ∀ v, g p₀ v = v) (hgf : ∀ p v, g p (f p v) = v) {φ : V → ℂ} (hφ : φ ∈ SB V) :
    ∀ᶠ p in 𝓝 p₀, ∀ v, φ (f p v) = φ v := by
  have key : ∀ f : P → V → V, (Continuous fun q : P × V => f q.1 q.2) → (∀ v, f p₀ v = v) →
      ∀ᶠ p in 𝓝 p₀, ∀ v ∈ tsupport φ, φ (f p v) = φ v := fun f hf f0 => by
    refine IsCompact.eventually_forall_of_forall_eventually hφ.2 fun v _ => ?_
    filter_upwards [(hφ.1.comp_continuous hf).eventually_eq (p₀, v),
      (hφ.1.comp_continuous continuous_snd).eventually_eq (p₀, v)] with q h1 h2
    simp only [Function.comp, f0] at h1 h2
    rw [h1, h2]
  filter_upwards [key f hf f0, key g hg g0] with p h1 h2 v
  by_cases hv : v ∈ tsupport φ
  · exact h1 v hv
  · by_cases hw : f p v ∈ tsupport φ
    · rw [← h2 _ hw, hgf]
    · rw [image_eq_zero_of_notMem_tsupport hv, image_eq_zero_of_notMem_tsupport hw]

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]

theorem eventually_char_eq_one (μ : Fˣ →* Circle) (hμ : Continuous μ) :
    ∀ᶠ t in 𝓝 (1 : Fˣ), μ t = 1 ∧ distribHaarChar F t = 1 := by
  have h0 : {t : Fˣ | ‖(μ t : ℂ) - 1‖ < 1 / 2} ∈ 𝓝 (1 : Fˣ) :=
    (isOpen_lt (by fun_prop) continuous_const).mem_nhds (by simp)
  rw [Units.isEmbedding_val₀.nhds_eq_comap, mem_comap] at h0
  obtain ⟨U, hU, hUV⟩ := h0
  have h1 : (fun x : F => 1 + x) ⁻¹' U ∈ 𝓝 (0 : F) :=
    (Continuous.tendsto' (by fun_prop) _ _ (by simp) : Tendsto (fun x : F => 1 + x) (𝓝 0) (𝓝 ((1 : Fˣ) : F))) hU
  have h2 : {x : F | valuation F x < 1} ∈ 𝓝 (0 : F) := (IsValuativeTopology.mem_nhds_zero_iff _).mpr ⟨1, fun _ h => h⟩
  obtain ⟨s, hs⟩ := SplitWeil.exists_cball_subset (inter_mem h1 h2)
  have h3 : Tendsto (fun t : Fˣ => (t : F) - 1) (𝓝 1) (𝓝 0) := Continuous.tendsto' (by fun_prop) _ _ (by simp)
  filter_upwards [h3.eventually (SplitWeil.cball_mem_nhds s)] with t ht
  have hv : valuation F (t : F) = 1 := by simpa using (valuation F).map_one_add_of_lt (hs ht).2
  have hn : ∀ n : ℕ, (t : F) ^ n - 1 ∈ SplitWeil.cball s := fun n => by
    induction n with
    | zero => simp [SplitWeil.cball]
    | succ n ih =>
      rw [show (t : F) ^ (n + 1) - 1 = t * (t ^ n - 1) + (t - 1) by ring]
      refine SplitWeil.add_mem_cball ?_ ht
      show valuation F ((t : F) * ((t : F) ^ n - 1)) ≤ valuation F (s : F)
      rw [map_mul, hv, one_mul]
      exact ih
  refine ⟨Circle.coe_eq_one.mp (eq_one_of_forall_pow_near fun n => ?_),
    NNReal.coe_injective (SplitWeil.nabs_eq_one_of_valuation_eq_one hv)⟩
  have : t ^ n ∈ Units.val ⁻¹' U := by simpa using (hs (hn n)).1
  simpa using hUV this

variable {α β κ : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype κ]

omit [DecidableEq α] [Fintype κ] in

theorem isLocallyConstant_splitOm (χ : (F × F)ˣ →* Circle) (hχ : Continuous χ) (J : Matrix β β (F × F)) (σ : κ ≃ α × β)
    {φ : (κ → F) → ℂ} (hφ : φ ∈ SB (κ → F)) : IsLocallyConstant fun h => splitOm (distribHaarChar F) χ J σ h φ := by
  refine isLocallyConstant_orbit _ ?_
  have c0 : Continuous (ugFst J) :=
    (Units.continuous_map (f := ((RingHom.fst F F).mapMatrix : Matrix β β (F × F) →+* Matrix β β F).toMonoidHom)
      (continuous_id.matrix_map (f := Prod.fst) continuous_fst)).comp continuous_subtype_val
  have c1 : Continuous fun h => GeneralLinearGroup.det (ugFst J h) :=
    Units.continuous_iff.mpr ⟨(Units.continuous_val.comp c0).matrix_det, (Units.continuous_val.comp c0.inv).matrix_det⟩
  have c2 : Continuous (χ.comp (Units.map (MonoidHom.inl F F))) :=
    hχ.comp (Units.continuous_map (continuous_id.prodMk continuous_const))
  have hc : ∀ M : UG (swapA F) J → Matrix β β F, Continuous M →
      Continuous fun q : UG (swapA F) J × (κ → F) => flat σ ((flat σ).symm q.2 * (M q.1)ᵀ) := fun M hM => by
    refine continuous_pi fun k => ?_
    simp only [flat_apply, mul_apply, flat_symm_apply, transpose_apply]
    fun_prop
  filter_upwards [(c1.tendsto' 1 1 (by simp)).eventually (eventually_char_eq_one _ c2),
    eventually_comp_eq (p₀ := 1) (fun p v => flat σ ((flat σ).symm v * ((ugFst J p)⁻¹).valᵀ))
      (fun p v => flat σ ((flat σ).symm v * (ugFst J p).valᵀ)) (hc _ (Units.continuous_val.comp c0.inv)) (hc _ (Units.continuous_val.comp c0))
      (by simp) (by simp) (fun p v => by
        simp only [Function.comp, LinearEquiv.symm_apply_apply, Matrix.mul_assoc, ← transpose_mul, Units.mul_inv,
          transpose_one, Matrix.mul_one, LinearEquiv.apply_symm_apply]) hφ] with h h1 h2
  funext u
  have h3 : splitChar (distribHaarChar F) χ (Fintype.card α) (GeneralLinearGroup.det (ugFst J h)) = 1 := by
    have := h1.1
    simp only [MonoidHom.comp_apply] at this
    simp [splitChar, this, h1.2]
  rw [splitOm_apply, h3, one_mul]
  exact h2 u

theorem isUnitaryOn_splitOm (χ : (F × F)ˣ →* Circle) (J : Matrix β β (F × F)) (σ : κ ≃ α × β) :
    IsUnitaryOn (sbClass F) (splitOm (distribHaarChar F) χ J σ) := by
  classical
  borelize F
  have := SplitWeil.secondCountable F
  have := SplitWeil.t2Space F
  unfold IsUnitaryOn
  rw [← (BorelSpace.measurable_eq : (MeasurableSpace.pi : MeasurableSpace (κ → F)) = borel _)]
  intro μ hμ h φ hφ
  set t := ugFst J h
  let G : Matrix κ κ F := ((1 : Matrix α α F) ⊗ₖ (t⁻¹).val).submatrix σ σ
  have hG : (((GeneralLinearGroup.det t)⁻¹ ^ Fintype.card α : Fˣ) : F) = G.det := by
    rw [det_submatrix_equiv_self, det_kronecker, det_one, one_pow, one_mul, ← map_inv, Units.val_pow_eq_pow_val]
    rfl
  have hgx : ∀ u, flat σ ((flat σ).symm u * (t⁻¹).valᵀ) = G.mulVec u := by
    intro u
    obtain ⟨X, rfl⟩ := (flat σ).surjective u
    funext k
    show _ = ∑ k', ((1 : Matrix α α F) ⊗ₖ (t⁻¹).val) (σ k) (σ k') * X (σ k').1 (σ k').2
    rw [Fintype.sum_equiv σ _ (fun q => ((1 : Matrix α α F) ⊗ₖ (t⁻¹).val) (σ k) q * X q.1 q.2) fun _ => rfl,
      Fintype.sum_prod_type, LinearEquiv.symm_apply_apply, flat_apply, mul_apply]
    simp [kroneckerMap_apply, one_apply, mul_comm]
  have hs : ‖splitChar (distribHaarChar F) χ (Fintype.card α) (GeneralLinearGroup.det t)‖ₑ ^ 2 =
      distribHaarChar F ((GeneralLinearGroup.det t)⁻¹ ^ Fintype.card α) := by
    rw [enorm_eq_nnnorm, ← ENNReal.coe_pow, ENNReal.coe_inj, ← NNReal.coe_inj]
    have p : (0 : ℝ) ≤ distribHaarChar F (GeneralLinearGroup.det t) := NNReal.coe_nonneg _
    simp only [splitChar, MonoidHom.coe_mk, OneHom.coe_mk, NNReal.coe_pow, coe_nnnorm, norm_mul, Circle.norm_coe, one_mul,
      Complex.norm_real, Real.norm_of_nonneg (Real.rpow_nonneg p _), map_pow, map_inv, NNReal.coe_inv]
    rw [← Real.rpow_natCast, ← Real.rpow_mul p, inv_pow, ← Real.rpow_natCast, ← Real.rpow_neg p]
    congr 1
    push_cast
    ring
  have hm : Measurable fun x => ‖φ x‖ₑ ^ 2 := (hφ.1.continuous.measurable.enorm).pow_const 2
  rw [Measure.isAddLeftInvariant_eq_smul μ (Measure.pi fun _ : κ => (Measure.addHaar : Measure F)),
    lintegral_smul_measure, lintegral_smul_measure]
  congr 1
  conv_rhs => rw [← smul_map_mulVec_pi Measure.addHaar G _ hG, lintegral_smul_measure,
    lintegral_map hm (show Measurable G.mulVec from (continuous_const.matrix_mulVec continuous_id).measurable)]
  simp only [splitOm_apply, enorm_mul, mul_pow]
  rw [lintegral_const_mul' _ _ (by simp [enorm_eq_nnnorm]), hs]
  simp only [← hgx]
  rfl

variable [Invertible (2 : F)] {JA : Matrix α α (F × F)} {JB : Matrix β β (F × F)}

theorem isUSplitting_splitOm (ψ : AddChar F ℂ) (hA : IsHerm (swapA F) JA) (hB : IsHerm (swapA F) JB) (σ : κ ≃ α × β)
    (χ : (F × F)ˣ →* Circle) (hχ : Continuous χ) :
    IsUSplitting (sbClass F) ψ (splitDarboux hA hB σ) (actB (swapA F)) (splitOm (distribHaarChar F) χ JB σ) :=
  ⟨isSplitting_splitOm _ χ hA hB σ ψ, isUnitaryOn_splitOm χ JB σ,
    .of_isLocallyConstant fun _ hφ => isLocallyConstant_splitOm χ hχ JB σ hφ⟩

theorem isUWeilSplit_split (ψ : AddChar F ℂ) (hψ : Continuous ψ) (hψ1 : ψ ≠ 1) (hA : IsHerm (swapA F) JA)
    (hB : IsHerm (swapA F) JB) (σ : κ ≃ α × β) (χ : (F × F)ˣ →* Circle) (hc : Continuous χ)
    (hχ : ResEtaPow (⊥ : Subgroup Fˣ) χ (Fintype.card α)) :
    IsUWeilSplit (swapA F) (sbClass F) ψ (1, -1) JA (dbl JB) (splitDarboux hA hB.dbl (dblNum σ)) χ (diagCols β)
      (splitOm (distribHaarChar F) χ (dbl JB) (dblNum σ)) :=
  ⟨isLagr_diagCols _ JB, isUSplitting_splitOm ψ hA hB.dbl _ χ hc,
    siegelRule_split ψ hψ hψ1 hA hB σ χ ((resEtaPow_split_iff _ _).mp hχ)⟩

end GlobalTheory.WeilM

end
