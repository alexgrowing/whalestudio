import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsLatMeasurableConst
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MeasurableSetDetNormPos
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.DetMatrixSandwichLinearMapStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsLatticeTraceDualAndTraceDualTraceDualStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TraceFormDualTranslatedLatticeEqInverseTransposeStatement

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.MeanDual

namespace GlobalTheory.MeanDual

theorem measurePreserving_of_fderiv {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    [MeasurableSpace V] [BorelSpace V] (μ : Measure V) [μ.IsAddHaarMeasure] (U : Set V) (hU : MeasurableSet U)
    (φ : V → V) (hφ : Measurable φ) (φ' : V → V →L[ℝ] V) (hd : ∀ x ∈ U, HasFDerivAt φ (φ' x) x)
    (hi : Set.InjOn φ U) (him : φ '' U = U) (ρ : V → ENNReal)
    (hρ : ∀ x ∈ U, ENNReal.ofReal |(φ' x).det| * ρ (φ x) = ρ x) :
    MeasurePreserving φ ((μ.withDensity ρ).restrict U) ((μ.withDensity ρ).restrict U) := by
  refine ⟨hφ, Measure.ext fun s hs => ?_⟩
  have h1 : MeasurableSet (φ ⁻¹' s ∩ U) := (hφ hs).inter hU
  rw [Measure.map_apply hφ hs, Measure.restrict_apply (hφ hs), Measure.restrict_apply hs,
    withDensity_apply _ h1, withDensity_apply _ (hs.inter hU)]
  have h2 : s ∩ U = φ '' (φ ⁻¹' s ∩ U) := by rw [Set.image_preimage_inter, him]
  rw [h2, lintegral_image_eq_lintegral_abs_det_fderiv_mul μ h1
    (fun x hx => (hd x hx.2).hasFDerivWithinAt) (hi.mono Set.inter_subset_right)]
  exact setLIntegral_congr_fun h1 fun x hx => (hρ x hx.2).symm

noncomputable def sandwich {ι : Type} {j : ℕ} (A B : ι → Matrix (Fin j) (Fin j) ℂ) :
    (ι → Fin j → Fin j → ℂ) →ₗ[ℝ] (ι → Fin j → Fin j → ℂ) where
  toFun h w a b := (A w * Matrix.of (h w) * B w) a b
  map_add' h k := by
    funext w a b
    change (A w * (Matrix.of (h w) + Matrix.of (k w)) * B w) a b = _
    rw [Matrix.mul_add, Matrix.add_mul]; rfl
  map_smul' c h := by
    funext w a b
    change (A w * (c • Matrix.of (h w)) * B w) a b = _
    rw [Matrix.mul_smul, Matrix.smul_mul]; rfl

noncomputable def transp (ι : Type) (j : ℕ) : (ι → Fin j → Fin j → ℂ) →ₗ[ℝ] (ι → Fin j → Fin j → ℂ) where
  toFun h w a b := h w b a
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem abs_det_transp (ι : Type) (j : ℕ) : |LinearMap.det (transp ι j)| = 1 := by
  have h : LinearMap.det (transp ι j) * LinearMap.det (transp ι j) = 1 := by
    rw [← LinearMap.det_comp]
    exact LinearMap.det_id
  rcases mul_self_eq_one_iff.1 h with h | h <;> simp [h]

open scoped Matrix.Norms.Operator in
theorem hasFDerivAt_matrix_inv_of_det_ne_zero {j : ℕ} (A : Matrix (Fin j) (Fin j) ℂ) (hA : A.det ≠ 0) :
    ∃ L : Matrix (Fin j) (Fin j) ℂ →L[ℝ] Matrix (Fin j) (Fin j) ℂ, (∀ h, L h = -A⁻¹ * h * A⁻¹) ∧
      HasFDerivAt (fun x : Matrix (Fin j) (Fin j) ℂ => x⁻¹) L A := by
  obtain ⟨u, rfl⟩ := (Matrix.isUnit_iff_isUnit_det A).2 (isUnit_iff_ne_zero.2 hA)
  have h := hasFDerivAt_ringInverse (𝕜 := ℝ) u
  simp only [Matrix.nonsing_inv_eq_ringInverse]
  refine ⟨_, fun h => ?_, h⟩
  rw [Ring.inverse_unit, Matrix.neg_mul, Matrix.neg_mul]
  rfl

theorem hasFDerivAt_inv {j : ℕ} (A : Fin j → Fin j → ℂ) (hA : (Matrix.of A).det ≠ 0) :
    ∃ L : (Fin j → Fin j → ℂ) →L[ℝ] (Fin j → Fin j → ℂ),
      (∀ h, Matrix.of (L h) = -(Matrix.of A)⁻¹ * Matrix.of h * (Matrix.of A)⁻¹) ∧
      HasFDerivAt (fun (x : Fin j → Fin j → ℂ) a b => (Matrix.of x)⁻¹ a b) L A :=
  hasFDerivAt_matrix_inv_of_det_ne_zero (Matrix.of A) hA

theorem isAddHaarMeasure_volume (ι : Type) [Fintype ι] (j : ℕ) :
    (volume : Measure (ι → Fin j → Fin j → ℂ)).IsAddHaarMeasure := by
  haveI : (volume : Measure (Fin j → ℂ)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
  haveI : (volume : Measure (Fin j → Fin j → ℂ)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
  exact Measure.pi.isAddHaarMeasure _

variable (E : Type) [Field E] [NumberField E] (j : ℕ)

theorem measurePreserving_mul_left (γ : MatInf E j) (hγ : 0 < detNorm E j γ) :
    MeasurePreserving (fun g : MatInf E j => γ * g) ((haarGL E j).restrict {g | 0 < detNorm E j g})
      ((haarGL E j).restrict {g | 0 < detNorm E j g}) := by
  let L := LinearMap.toContinuousLinearMap (sandwich (fun w => Matrix.of (γ w)) fun _ => 1)
  have hL : (fun g : MatInf E j => γ * g) = L := by
    funext g
    apply matInf_ext
    intro w
    exact (Matrix.mul_one _).symm
  have hu := fun w => isUnit_iff_ne_zero.2 ((detNorm_pos_iff E j γ).1 hγ w)
  haveI := isAddHaarMeasure_volume (InfinitePlace E) j
  refine measurePreserving_of_fderiv (V := InfinitePlace E → Fin j → Fin j → ℂ) volume _
    (measurableSet_detNorm_pos E j) _ (by rw [hL]; exact L.continuous.measurable) (fun _ => L)
    (fun x _ => by rw [hL]; exact L.hasFDerivAt) ?_ ?_ _ ?_
  · intro x _ y _ hxy
    apply matInf_ext
    intro w
    have : Matrix.of (γ w) * Matrix.of (x w) = Matrix.of (γ w) * Matrix.of (y w) :=
      congrArg (fun z : MatInf E j => Matrix.of (z w)) hxy
    rw [← Matrix.nonsing_inv_mul_cancel_left _ (Matrix.of (x w)) (hu w), this,
      Matrix.nonsing_inv_mul_cancel_left _ _ (hu w)]
  · ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact (mul_pos hγ hx).trans_eq (detNorm_mul E j γ x).symm
    · intro hy
      have h : γ * (show MatInf E j from fun w a b => ((Matrix.of (γ w))⁻¹ * Matrix.of (y w)) a b) = y := by
        apply matInf_ext
        intro w
        exact Matrix.mul_nonsing_inv_cancel_left _ _ (hu w)
      refine ⟨_, ?_, h⟩
      have hy' : 0 < detNorm E j y := hy
      rw [← h, detNorm_mul] at hy'
      exact (mul_pos_iff_of_pos_left hγ).1 hy'
  · intro x hx
    have hx' : 0 < detNorm E j x := hx
    have hdet : L.det = detNorm E j γ ^ j := by
      rw [ContinuousLinearMap.det, LinearMap.coe_toContinuousLinearMap, GlobalTheory.T.det_matrix_sandwich_linear_map _ _ _ _ _ fun _ _ => rfl]
      simp [detNorm, Finset.prod_pow]
    have hm := detNorm_mul E j γ x
    rw [hdet]
    refine (congrArg (fun t : ℝ => _ * ENNReal.ofReal (t⁻¹ ^ j)) hm).trans ?_
    rw [← ENNReal.ofReal_mul (abs_nonneg _), abs_of_pos (pow_pos hγ _), ← mul_pow]
    congr 2
    field_simp

theorem measurable_invT : Measurable (invT E j) := by
  have h : Measurable fun (g : InfinitePlace E → Fin j → Fin j → ℂ) w a b => (Matrix.of (g w))⁻¹ b a := by
    refine measurable_pi_lambda _ fun w => measurable_pi_lambda _ fun a => measurable_pi_lambda _ fun b => ?_
    simp only [Matrix.inv_def, Ring.inverse_eq_inv', Matrix.smul_apply, smul_eq_mul]
    have hc : Continuous fun g : InfinitePlace E → Fin j → Fin j → ℂ => Matrix.of (g w) := continuous_apply w
    exact hc.matrix_det.measurable.inv.mul (hc.matrix_adjugate.matrix_elem b a).measurable
  exact h

theorem detNorm_invT (g : MatInf E j) : detNorm E j (invT E j g) = (detNorm E j g)⁻¹ := by
  simp only [detNorm, of_invT, Matrix.det_transpose, Matrix.det_nonsing_inv, Ring.inverse_eq_inv', norm_inv,
    inv_pow, Finset.prod_inv_distrib]

theorem measurePreserving_invT :
    MeasurePreserving (invT E j) ((haarGL E j).restrict {g | 0 < detNorm E j g})
      ((haarGL E j).restrict {g | 0 < detNorm E j g}) := by
  let L := fun x : InfinitePlace E → Fin j → Fin j → ℂ => LinearMap.toContinuousLinearMap
    (sandwich (fun w => -(Matrix.of (x w))⁻¹) fun w => (Matrix.of (x w))⁻¹)
  let T := LinearMap.toContinuousLinearMap (transp (InfinitePlace E) j)
  haveI := isAddHaarMeasure_volume (InfinitePlace E) j
  refine measurePreserving_of_fderiv (V := InfinitePlace E → Fin j → Fin j → ℂ) volume _
    (measurableSet_detNorm_pos E j) _ (measurable_invT E j) (fun x => T.comp (L x)) ?_ ?_ ?_ _ ?_
  · intro x hx
    have h1 : HasFDerivAt (fun (g : InfinitePlace E → Fin j → Fin j → ℂ) w a b => (Matrix.of (g w))⁻¹ a b)
        (L x) x := by
      rw [hasFDerivAt_pi']
      intro w
      obtain ⟨M, hM, hd⟩ := hasFDerivAt_inv (x w) ((detNorm_pos_iff E j x).1 hx w)
      have := hd.comp x (hasFDerivAt_apply (𝕜 := ℝ) w x)
      refine this.congr_fderiv ?_
      ext1 h
      exact Matrix.of.injective (hM (h w))
    exact T.hasFDerivAt.comp x h1
  · intro x hx y hy hxy
    rw [← invT_invT E j hx, hxy, invT_invT E j hy]
  · ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact (detNorm_invT_pos_iff E j x).2 hx
    · intro hy
      exact ⟨invT E j y, (detNorm_invT_pos_iff E j y).2 hy, invT_invT E j hy⟩
  · intro x hx
    have hx' : 0 < detNorm E j x := hx
    have hdet : |(T.comp (L x)).det| = ((detNorm E j x)⁻¹ * (detNorm E j x)⁻¹) ^ j := by
      change |LinearMap.det ((transp (InfinitePlace E) j).comp
        (sandwich (fun w => -(Matrix.of (x w))⁻¹) fun w => (Matrix.of (x w))⁻¹))| = _
      rw [LinearMap.det_comp, abs_mul, abs_det_transp,
        one_mul, GlobalTheory.T.det_matrix_sandwich_linear_map _ _ _ _ _ fun _ _ => rfl, abs_of_nonneg (Finset.prod_nonneg fun _ _ => by positivity)]
      simp [detNorm, Finset.prod_pow, Matrix.det_neg, Finset.prod_mul_distrib, mul_pow]
    have hm := detNorm_invT E j x
    rw [hdet]
    refine (congrArg (fun t : ℝ => _ * ENNReal.ofReal (t⁻¹ ^ j)) hm).trans ?_
    rw [← ENNReal.ofReal_mul (by positivity), ← mul_pow]
    congr 2
    field_simp

end GlobalTheory.MeanDual

namespace GlobalTheory.MeanDual

theorem covol_le_of_map {G : Type} [Mul G] [MeasurableSpace G] (Γ Γ' : Set G) (μ : Measure G) (U : Set G)
    (hU : MeasurableSet U) (φ : G → G) (hφ : MeasurePreserving φ (μ.restrict U) (μ.restrict U))
    (hφU : ∀ x ∈ U, φ x ∈ U) (f f' : G → ENNReal) (hf : ∀ x ∈ U, f x = f' (φ x))
    (hm : Measurable (U.indicator f'))
    (hΓ : ∀ γ' ∈ Γ', ∃ γ ∈ Γ, ∀ x ∈ U, γ * x ∈ U ∧ φ (γ * x) = γ' * φ x) :
    covol Γ (μ.withDensity f) U ≤ covol Γ' (μ.withDensity f') U := by
  unfold covol
  refine le_iInf fun D' => le_iInf fun hD' => le_iInf fun hc => ?_
  have hD : MeasurableSet (φ ⁻¹' D' ∩ U) := (hφ.measurable hD').inter hU
  refine iInf_le_of_le (φ ⁻¹' D' ∩ U) (iInf_le_of_le hD (iInf_le_of_le ?_ ?_))
  · intro x hx
    obtain ⟨γ', hγ', hx'⟩ := hc (φ x) (hφU x hx)
    obtain ⟨γ, hγ, H⟩ := hΓ γ' hγ'
    exact ⟨γ, hγ, by rw [Set.mem_preimage, (H x hx).2]; exact hx', (H x hx).1⟩
  · rw [withDensity_apply _ hD, withDensity_apply _ hD']
    calc ∫⁻ x in φ ⁻¹' D' ∩ U, f x ∂μ
        = ∫⁻ x in φ ⁻¹' D' ∩ U, U.indicator f' (φ x) ∂μ :=
          setLIntegral_congr_fun hD fun x hx => by
            rw [Set.indicator_of_mem (hφU x hx.2), hf x hx.2]
      _ = ∫⁻ x in φ ⁻¹' D', U.indicator f' (φ x) ∂(μ.restrict U) := by
          rw [Measure.restrict_restrict (hφ.measurable hD')]
      _ = ∫⁻ x in D', U.indicator f' x ∂(μ.restrict U) := hφ.setLIntegral_comp_preimage hD' hm
      _ ≤ ∫⁻ x in D', f' x ∂μ :=
          lintegral_mono' (Measure.restrict_mono subset_rfl Measure.restrict_le_self)
            (Set.indicator_le_self _ _)

variable (E : Type) [Field E] [NumberField E] (j : ℕ)

noncomputable def embInf (γ : GL (Fin j) E) : MatInf E j :=
  fun w a b => w.embedding ((γ : Matrix (Fin j) (Fin j) E) a b)

omit [NumberField E] in
theorem of_embInf (γ : GL (Fin j) E) (w : InfinitePlace E) :
    Matrix.of (embInf E j γ w) = (γ : Matrix (Fin j) (Fin j) E).map w.embedding := rfl

omit [NumberField E] in
theorem embInf_mul (γ δ : GL (Fin j) E) : embInf E j (γ * δ) = embInf E j γ * embInf E j δ := by
  funext w
  apply Matrix.of.injective
  change Matrix.of (embInf E j (γ * δ) w) = Matrix.of (embInf E j γ w) * Matrix.of (embInf E j δ w)
  rw [of_embInf, of_embInf, of_embInf, Units.val_mul, Matrix.map_mul]

omit [NumberField E] in
theorem embInf_inv_mul (γ : GL (Fin j) E) (w : InfinitePlace E) :
    Matrix.of (embInf E j γ⁻¹ w) * Matrix.of (embInf E j γ w) = 1 := by
  rw [of_embInf, of_embInf, ← Matrix.map_mul, Units.inv_mul,
    Matrix.map_one _ (map_zero _) (map_one _)]

omit [NumberField E] in
theorem inv_embInf (γ : GL (Fin j) E) (w : InfinitePlace E) :
    (Matrix.of (embInf E j γ w))⁻¹ = Matrix.of (embInf E j γ⁻¹ w) :=
  Matrix.inv_eq_left_inv (embInf_inv_mul E j γ w)

theorem detNorm_embInf (γ : GL (Fin j) E) : 0 < detNorm E j (embInf E j γ) := by
  rw [detNorm_pos_iff]
  intro w h
  have := congrArg Matrix.det (embInf_inv_mul E j γ w)
  rw [Matrix.det_mul, h] at this
  simp at this

theorem mem_autGL {Λ : Submodule (𝓞 E) (Fin j → E)} {x : MatInf E j} :
    x ∈ autGL E j Λ ↔ ∃ γ : GL (Fin j) E,
      (∀ y, (γ : Matrix (Fin j) (Fin j) E) *ᵥ y ∈ Λ ↔ y ∈ Λ) ∧ x = embInf E j γ := by
  refine exists_congr fun γ => and_congr_right fun _ => ⟨fun h => ?_, fun h => ?_⟩
  · funext w a b; exact h w a b
  · intro w a b; rw [h]; rfl

def Carries (γ : GL (Fin j) E) (Λ Λ' : Submodule (𝓞 E) (Fin j → E)) : Prop :=
  ∀ y, (γ : Matrix (Fin j) (Fin j) E) *ᵥ y ∈ Λ' ↔ y ∈ Λ

variable {E j}

theorem Carries.inv {γ : GL (Fin j) E} {Λ Λ' : Submodule (𝓞 E) (Fin j → E)} (h : Carries E j γ Λ Λ') :
    Carries E j γ⁻¹ Λ' Λ := fun y => by
  rw [← h, Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]

theorem Carries.mul {γ δ : GL (Fin j) E} {Λ Λ' Λ'' : Submodule (𝓞 E) (Fin j → E)}
    (h' : Carries E j δ Λ' Λ'') (h : Carries E j γ Λ Λ') : Carries E j (δ * γ) Λ Λ'' := fun y => by
  rw [Units.val_mul, ← Matrix.mulVec_mulVec, h', h]

def glInvT (γ : GL (Fin j) E) : GL (Fin j) E :=
  ⟨((γ⁻¹ : GL (Fin j) E) : Matrix (Fin j) (Fin j) E)ᵀ, (γ : Matrix (Fin j) (Fin j) E)ᵀ,
    by rw [← Matrix.transpose_mul, Units.mul_inv, Matrix.transpose_one],
    by rw [← Matrix.transpose_mul, Units.inv_mul, Matrix.transpose_one]⟩

theorem invT_embInf (γ : GL (Fin j) E) : invT E j (embInf E j γ) = embInf E j (glInvT γ) := by
  apply matInf_ext
  intro w
  rw [of_invT, inv_embInf, of_embInf, of_embInf, ← Matrix.transpose_map]
  rfl

theorem Carries.trDual {γ : GL (Fin j) E} {Λ Λ' : Submodule (𝓞 E) (Fin j → E)} (h : Carries E j γ Λ Λ') :
    Carries E j (glInvT γ) (trDual E j Λ) (trDual E j Λ') := fun y => by
  have key : ∀ x : Fin j → E, x ⬝ᵥ ((glInvT γ : GL (Fin j) E) : Matrix (Fin j) (Fin j) E) *ᵥ y =
      (((γ⁻¹ : GL (Fin j) E) : Matrix (Fin j) (Fin j) E) *ᵥ x) ⬝ᵥ y := fun x => by
    change x ⬝ᵥ ((γ⁻¹ : GL (Fin j) E) : Matrix (Fin j) (Fin j) E)ᵀ *ᵥ y = _
    rw [Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]
  rw [mem_trDual, mem_trDual]
  constructor
  · intro H x hx
    have := H _ ((h x).2 hx)
    rwa [key, Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec] at this
  · intro H x hx
    rw [key]
    exact H _ ((h.inv x).2 hx)

theorem Carries.latAt {γ : GL (Fin j) E} {Λ Λ' : Submodule (𝓞 E) (Fin j → E)} (h : Carries E j γ Λ Λ')
    (g : MatInf E j) : latAt E j Λ' (embInf E j γ * g) = latAt E j Λ g := by
  have key : ∀ (y : Fin j → E) (w : InfinitePlace E),
      (Matrix.of ((embInf E j γ * g) w))⁻¹ *ᵥ (fun a => w.embedding (y a)) =
      (Matrix.of (g w))⁻¹ *ᵥ fun a =>
        w.embedding ((((γ⁻¹ : GL (Fin j) E) : Matrix (Fin j) (Fin j) E) *ᵥ y) a) := fun y w => by
    rw [of_mul, Matrix.mul_inv_rev, inv_embInf, of_embInf, ← Matrix.mulVec_mulVec]
    congr 1
    funext a
    exact (RingHom.map_mulVec w.embedding _ y a).symm
  unfold FlagBase.latAt
  congr 1
  ext v
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨_, (h.inv y).2 hy, funext fun w => (key y w).symm⟩
  · rintro ⟨y, hy, rfl⟩
    refine ⟨_, (h y).2 hy, funext fun w => ?_⟩
    simp only []
    rw [key, Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]

variable (E j)

noncomputable def term (F : Submodule ℤ (VecInf E j) → ENNReal) (Λ : Submodule (𝓞 E) (Fin j → E)) : ENNReal :=
  covol (autGL E j Λ) ((haarGL E j).withDensity fun g => F (latAt E j Λ g)) {g | 0 < detNorm E j g}

variable {E j}

theorem term_le_of_carries {γ : GL (Fin j) E} {Λ Λ' : Submodule (𝓞 E) (Fin j → E)} (h : Carries E j γ Λ Λ')
    (F : Submodule ℤ (VecInf E j) → ENNReal)
    (hm : Measurable ({g | 0 < detNorm E j g}.indicator fun g => F (latAt E j Λ' g))) :
    term E j F Λ ≤ term E j F Λ' := by
  have hp : ∀ (δ : GL (Fin j) E), ∀ x ∈ {g | 0 < detNorm E j g}, embInf E j δ * x ∈ {g | 0 < detNorm E j g} :=
    fun δ x hx => by
      rw [Set.mem_setOf_eq, detNorm_mul]; exact mul_pos (detNorm_embInf E j δ) hx
  refine covol_le_of_map _ _ _ _ (measurableSet_detNorm_pos E j) _
    (measurePreserving_mul_left E j _ (detNorm_embInf E j γ)) (hp γ) _ _ (fun x _ => by rw [h.latAt]) hm ?_
  intro x hx
  obtain ⟨δ, hδ, rfl⟩ := (mem_autGL E j).1 hx
  refine ⟨embInf E j (γ⁻¹ * δ * γ), (mem_autGL E j).2 ⟨_, (h.inv.mul hδ).mul h, rfl⟩, fun x hx => ⟨hp _ x hx, ?_⟩⟩
  apply matInf_ext
  intro w
  simp only [of_mul, embInf_mul, ← Matrix.mul_assoc]
  have := embInf_inv_mul E j γ⁻¹ w
  rw [inv_inv] at this
  rw [this, Matrix.one_mul]

theorem covol_invT_le {Λ Λ' : Submodule (𝓞 E) (Fin j → E)} (h : trDual E j Λ' = Λ)
    (f f' : MatInf E j → ENNReal) (hf : ∀ x ∈ {g | 0 < detNorm E j g}, f x = f' (invT E j x))
    (hm : Measurable ({g | 0 < detNorm E j g}.indicator f')) :
    covol (autGL E j Λ) ((haarGL E j).withDensity f) {g | 0 < detNorm E j g} ≤
      covol (autGL E j Λ') ((haarGL E j).withDensity f') {g | 0 < detNorm E j g} := by
  refine covol_le_of_map _ _ _ _ (measurableSet_detNorm_pos E j) _ (measurePreserving_invT E j)
    (fun x hx => (detNorm_invT_pos_iff E j x).2 hx) _ _ hf hm ?_
  intro x hx
  obtain ⟨δ, hδ, rfl⟩ := (mem_autGL E j).1 hx
  refine ⟨embInf E j (glInvT δ), (mem_autGL E j).2 ⟨_, ?_, rfl⟩, fun x hx => ⟨?_, ?_⟩⟩
  · rw [← h]; exact Carries.trDual hδ
  · rw [Set.mem_setOf_eq, detNorm_mul]; exact mul_pos (detNorm_embInf E j _) hx
  · rw [invT_mul, ← invT_embInf, invT_invT E j (detNorm_embInf E j _)]

theorem term_dual (hE : IsTotallyComplex E) {Λ : Submodule (𝓞 E) (Fin j → E)} (hΛ : Submodule.IsLattice E Λ)
    (F : Submodule ℤ (VecInf E j) → ENNReal)
    (hm : Measurable ({g | 0 < detNorm E j g}.indicator fun g => F (latAt E j (trDual E j Λ) g))) :
    term E j (fun L => F (dualAt E j L)) Λ = term E j F (trDual E j Λ) := by
  apply le_antisymm
  · exact covol_invT_le (GlobalTheory.T.isLattice_traceDual_and_traceDual_traceDual E j Λ hΛ).2 _ _ (fun x hx => congrArg F (GlobalTheory.T.traceFormDual_translatedLattice_eq_inverseTranspose E hE j Λ hΛ x hx)) hm
  · refine covol_invT_le rfl _ _ (fun x hx => ?_) ?_
    · beta_reduce
      rw [GlobalTheory.T.traceFormDual_translatedLattice_eq_inverseTranspose E hE j Λ hΛ _ ((detNorm_invT_pos_iff E j x).2 hx), invT_invT E j hx]
    · have := hm.comp (measurePreserving_invT E j).measurable
      convert this using 1
      funext x
      by_cases hx : x ∈ {g | 0 < detNorm E j g}
      · rw [Function.comp, Set.indicator_of_mem hx,
          Set.indicator_of_mem (show invT E j x ∈ {g | 0 < detNorm E j g} from
            (detNorm_invT_pos_iff E j x).2 hx)]
        exact congrArg F (GlobalTheory.T.traceFormDual_translatedLattice_eq_inverseTranspose E hE j Λ hΛ x hx)
      · rw [Function.comp, Set.indicator_of_notMem hx, Set.indicator_of_notMem
          (show invT E j x ∉ {g | 0 < detNorm E j g} from fun h => hx ((detNorm_invT_pos_iff E j x).1 h))]

theorem latMean_dualAt : ∀ (E : Type) [Field E] [NumberField E], IsTotallyComplex E → ∀ j : ℕ, ∀ F : Submodule ℤ (VecInf E j) → ENNReal, (∀ Λ : Submodule (𝓞 E) (Fin j → E), Submodule.IsLattice E Λ → Measurable (fun g : MatInf E j => {g | 0 < detNorm E j g}.indicator (fun g => F (latAt E j Λ g)) g)) → latMean E j (fun L => F (dualAt E j L)) = latMean E j F := by
  intro E _ _ hE j F hF
  let X := {Λ : Submodule (𝓞 E) (Fin j → E) // Submodule.IsLattice E Λ}
  let r : X → X → Prop := fun Λ Λ' => ∃ γ : GL (Fin j) E, Carries E j γ Λ.1 Λ'.1
  let d : X → X := fun Λ => ⟨trDual E j Λ.1, (GlobalTheory.T.isLattice_traceDual_and_traceDual_traceDual E j Λ.1 Λ.2).1⟩
  have hdd : ∀ Λ, d (d Λ) = Λ := fun Λ => Subtype.ext (GlobalTheory.T.isLattice_traceDual_and_traceDual_traceDual E j Λ.1 Λ.2).2
  have hd : ∀ ⦃a b⦄, r a b → r (d a) (d b) := fun a b ⟨γ, h⟩ => ⟨_, h.trDual⟩
  let D : Quot r → Quot r := Quot.map d hd
  have hD : Function.Involutive D := by
    rintro ⟨Λ⟩
    exact congrArg (Quot.mk r) (hdd Λ)
  let t : Quot r → ENNReal := Quot.lift (fun Λ => term E j F Λ.1) fun a b ⟨γ, h⟩ =>
    le_antisymm (term_le_of_carries h F (hF _ b.2)) (term_le_of_carries h.inv F (hF _ a.2))
  change ∑' c : Quot r, term E j (fun L => F (dualAt E j L)) (Quot.out c).1 =
    ∑' c : Quot r, term E j F (Quot.out c).1
  have h1 : ∀ c : Quot r, term E j F (Quot.out c).1 = t c := fun c => by
    conv_rhs => rw [← Quot.out_eq c]
  have h2 : ∀ c : Quot r, term E j (fun L => F (dualAt E j L)) (Quot.out c).1 = t (D c) := fun c => by
    rw [term_dual hE (Quot.out c).2 F (hF _ (d (Quot.out c)).2)]
    conv_rhs => rw [← Quot.out_eq c]
    rfl
  simp only [h1, h2]
  exact hD.toPerm.tsum_eq t

end GlobalTheory.MeanDual
