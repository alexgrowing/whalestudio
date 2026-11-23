import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsLatMeasurableConst
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase

noncomputable section

namespace GlobalTheory.LatDom

variable {E : Type} [Field E] [NumberField E] {j : ℕ}

theorem of_mul (x y : MatInf E j) (w : InfinitePlace E) :
    Matrix.of ((x * y) w) = Matrix.of (x w) * Matrix.of (y w) := rfl

theorem matInf_ext {x y : MatInf E j} (h : ∀ w, Matrix.of (x w) = Matrix.of (y w)) : x = y :=
  funext fun w => Matrix.of.injective (h w)

theorem detNorm_mul (x y : MatInf E j) : detNorm E j (x * y) = detNorm E j x * detNorm E j y := by
  unfold detNorm
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun w _ => ?_
  rw [of_mul, Matrix.det_mul, norm_mul, mul_pow]

theorem detNorm_pos_iff (x : MatInf E j) : 0 < detNorm E j x ↔ ∀ w, (Matrix.of (x w)).det ≠ 0 := by
  unfold detNorm
  constructor
  · intro h w hw
    rw [Finset.prod_eq_zero (Finset.mem_univ w) (by simp [hw])] at h
    exact lt_irrefl _ h
  · intro h
    exact Finset.prod_pos fun w _ => pow_pos (norm_pos_iff.2 (h w)) 2

theorem continuous_detNorm :
    Continuous fun x : InfinitePlace E → Fin j → Fin j → ℂ => detNorm E j x := by
  unfold detNorm
  refine continuous_finset_prod _ fun w _ => ?_
  refine (Continuous.norm ?_).pow 2
  exact Continuous.matrix_det (A := fun x : InfinitePlace E → Fin j → Fin j → ℂ => Matrix.of (x w))
    (continuous_apply w)

theorem measurable_detNorm : Measurable (detNorm E j) := continuous_detNorm.measurable

def mulLin (γ : MatInf E j) :
    (InfinitePlace E → Fin j → Fin j → ℂ) →ₗ[ℂ] (InfinitePlace E → Fin j → Fin j → ℂ) where
  toFun x := fun w a b => ∑ c, γ w a c * x w c b
  map_add' x y := by
    funext w a b
    simp [mul_add, Finset.sum_add_distrib]
  map_smul' t x := by
    funext w a b
    simp [Finset.mul_sum, mul_left_comm]

def reidx (E : Type) [Field E] (j : ℕ) :
    (InfinitePlace E → Fin j → Fin j → ℂ) ≃ₗ[ℂ] (Fin j × (InfinitePlace E × Fin j) → ℂ) where
  toFun x := fun p => x p.2.1 p.1 p.2.2
  invFun y := fun w a b => y (a, (w, b))
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

theorem det_mulLin (γ : MatInf E j) :
    LinearMap.det (mulLin γ) = (∏ w, (Matrix.of (γ w)).det) ^ j := by
  classical
  have h : (reidx E j : _ →ₗ[ℂ] _) ∘ₗ mulLin γ ∘ₗ ((reidx E j).symm : _ →ₗ[ℂ] _) =
      Matrix.toLin' (Matrix.blockDiagonal fun p : InfinitePlace E × Fin j => Matrix.of (γ p.1)) := by
    apply LinearMap.ext
    intro y
    funext ⟨a, w, b⟩
    rw [Matrix.toLin'_apply]
    change ∑ c, γ w a c * y (c, (w, b)) = _
    simp only [Matrix.mulVec, dotProduct, Matrix.blockDiagonal_apply]
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun c _ => ?_
    simp [ite_mul]
  rw [← LinearMap.det_conj (mulLin γ) (reidx E j), h, LinearMap.det_toLin', Matrix.det_blockDiagonal,
    Fintype.prod_prod_type, ← Finset.prod_pow]
  simp

theorem det_mulLin_real (γ : MatInf E j) :
    LinearMap.det ((mulLin γ).restrictScalars ℝ) = detNorm E j γ ^ j := by
  rw [LinearMap.det_restrictScalars, det_mulLin, Algebra.norm_complex_apply, map_pow, Complex.normSq_eq_norm_sq,
    norm_prod, ← Finset.prod_pow]
  rfl

theorem measurable_mul_left (γ : MatInf E j) : Measurable fun x : MatInf E j => γ * x :=
  (mulLin γ).continuous_of_finiteDimensional.measurable

theorem measurable_dens :
    Measurable fun x : MatInf E j => ENNReal.ofReal ((detNorm E j x)⁻¹ ^ j) :=
  (measurable_detNorm.inv.pow_const j).ennreal_ofReal

theorem lintegral_haarGL_mul_left (γ : MatInf E j) (hγ : 0 < detNorm E j γ) (F : MatInf E j → ENNReal)
    (hF : Measurable F) : ∫⁻ x, F (γ * x) ∂(haarGL E j) = ∫⁻ x, F x ∂(haarGL E j) := by
  have hd : 0 < detNorm E j γ ^ j := pow_pos hγ j
  haveI i1 : (volume : Measure (Fin j → ℂ)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
  haveI i2 : (volume : Measure (Fin j → Fin j → ℂ)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
  haveI i3 : (volume : Measure (InfinitePlace E → Fin j → Fin j → ℂ)).IsAddHaarMeasure :=
    Measure.pi.isAddHaarMeasure _
  have hmap := Measure.map_linearMap_addHaar_eq_smul_addHaar
    (volume : Measure (InfinitePlace E → Fin j → Fin j → ℂ)) (f := (mulLin γ).restrictScalars ℝ)
    (by rw [det_mulLin_real]; exact hd.ne')
  rw [det_mulLin_real, abs_of_pos (inv_pos.2 hd)] at hmap
  let vol : Measure (MatInf E j) := (volume : Measure (InfinitePlace E → Fin j → Fin j → ℂ))
  set ρ : MatInf E j → ENNReal := fun x => ENNReal.ofReal ((detNorm E j x)⁻¹ ^ j) with hρ
  have hρm : Measurable ρ := measurable_dens
  have h1 : ∀ F : MatInf E j → ENNReal, Measurable F → ∫⁻ x, F x ∂(haarGL E j) =
      ∫⁻ x, ρ x * F x ∂vol := fun F hF =>
    lintegral_withDensity_eq_lintegral_mul _ hρm hF
  have h2 : ∀ x, ρ x = ENNReal.ofReal (detNorm E j γ ^ j) * ρ (γ * x) := by
    intro x
    simp only [hρ]
    rw [← ENNReal.ofReal_mul hd.le, detNorm_mul, ← mul_pow, mul_inv, mul_inv_cancel_left₀ hγ.ne']
  rw [h1 (fun x => F (γ * x)) (hF.comp (measurable_mul_left γ)), h1 _ hF]
  have h3 : ∫⁻ x, ρ (γ * x) * F (γ * x) ∂vol =
      ENNReal.ofReal (detNorm E j γ ^ j)⁻¹ *
        ∫⁻ x, ρ x * F x ∂vol := by
    have := lintegral_map (μ := (volume : Measure (InfinitePlace E → Fin j → Fin j → ℂ)))
      (f := fun x : InfinitePlace E → Fin j → Fin j → ℂ => ρ x * F x)
      (g := (mulLin γ).restrictScalars ℝ) (hρm.mul hF) (measurable_mul_left γ)
    rw [hmap, lintegral_smul_measure] at this
    exact this.symm
  calc _ = ∫⁻ x, ENNReal.ofReal (detNorm E j γ ^ j) * (ρ (γ * x) * F (γ * x))
        ∂vol := by
        refine lintegral_congr fun x => ?_
        rw [← mul_assoc, ← h2]
    _ = _ := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, h3, ← mul_assoc, ← ENNReal.ofReal_mul hd.le,
          mul_inv_cancel₀ hd.ne', ENNReal.ofReal_one, one_mul]

def emb (γ : GL (Fin j) E) : MatInf E j := fun w a b => w.embedding ((γ : Matrix (Fin j) (Fin j) E) a b)

theorem of_emb (γ : GL (Fin j) E) (w : InfinitePlace E) :
    Matrix.of (emb γ w) = w.embedding.mapMatrix (γ : Matrix (Fin j) (Fin j) E) := rfl

theorem matInf_mul_assoc (x y z : MatInf E j) : x * y * z = x * (y * z) :=
  matInf_ext fun w => by simp only [of_mul, Matrix.mul_assoc]

theorem emb_mul (γ δ : GL (Fin j) E) : emb (γ * δ) = emb γ * emb δ :=
  matInf_ext fun w => by simp only [of_mul, of_emb, Units.val_mul, map_mul]

theorem emb_one_mul (x : MatInf E j) : emb (1 : GL (Fin j) E) * x = x :=
  matInf_ext fun w => by simp only [of_mul, of_emb, Units.val_one, map_one, Matrix.one_mul]

theorem detNorm_emb_pos (γ : GL (Fin j) E) : 0 < detNorm E j (emb γ) := by
  rw [detNorm_pos_iff]
  intro w
  rw [of_emb, ← RingHom.map_det]
  exact (map_ne_zero _).2 (Matrix.GeneralLinearGroup.det_ne_zero γ)

theorem detNorm_emb_mul_pos (γ : GL (Fin j) E) (x : MatInf E j) :
    0 < detNorm E j (emb γ * x) ↔ 0 < detNorm E j x := by
  rw [detNorm_mul]
  exact mul_pos_iff_of_pos_left (detNorm_emb_pos γ)

theorem eq_of_emb_mul_eq {γ δ : GL (Fin j) E} {x : MatInf E j} (hx : 0 < detNorm E j x)
    (h : emb γ * x = emb δ * x) : γ = δ := by
  obtain ⟨w⟩ : Nonempty (InfinitePlace E) := inferInstance
  have h1 := congrArg (fun y : MatInf E j => Matrix.of (y w)) h
  simp only [of_mul] at h1
  have hu : IsUnit (Matrix.of (x w)) :=
    (Matrix.isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 ((detNorm_pos_iff x).1 hx w))
  have h2 := hu.mul_right_cancel h1
  apply Units.ext
  ext a b
  exact w.embedding.injective (congrFun (congrFun h2 a) b)

def autSub (Λ : Submodule (𝓞 E) (Fin j → E)) : Subgroup (GL (Fin j) E) where
  carrier := {γ | ∀ y, (γ : Matrix (Fin j) (Fin j) E) *ᵥ y ∈ Λ ↔ y ∈ Λ}
  one_mem' := by intro y; simp
  mul_mem' := by
    intro γ δ hγ hδ y
    rw [Units.val_mul, ← Matrix.mulVec_mulVec, hγ, hδ]
  inv_mem' := by
    intro γ hγ y
    rw [← hγ, Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]

theorem mem_autGL {Λ : Submodule (𝓞 E) (Fin j → E)} {x : MatInf E j} :
    x ∈ autGL E j Λ ↔ ∃ γ ∈ autSub Λ, x = emb γ := by
  constructor
  · rintro ⟨γ, h, h'⟩
    exact ⟨γ, h, funext fun w => funext fun a => funext fun b => h' w a b⟩
  · rintro ⟨γ, h, rfl⟩
    exact ⟨γ, h, fun _ _ _ => rfl⟩

theorem exists_denominator (Λ : Submodule (𝓞 E) (Fin j → E)) (hΛ : Submodule.IsLattice E Λ) :
    ∃ N : E, N ≠ 0 ∧ ∀ γ ∈ autSub Λ, ∀ a b, IsIntegral ℤ (N * (γ : Matrix (Fin j) (Fin j) E) a b) := by
  classical
  obtain ⟨S, hS⟩ := hΛ.fg
  obtain ⟨d, hd⟩ := IsLocalization.exist_integer_multiples (nonZeroDivisors (𝓞 E))
    (S ×ˢ (Finset.univ : Finset (Fin j))) (fun p : (Fin j → E) × Fin j => p.1 p.2)
  have h1 : ∀ y ∈ Λ, ∀ a, IsIntegral ℤ (((d : 𝓞 E) : E) * y a) := by
    intro y hy a
    rw [← hS] at hy
    induction hy using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨z, hz⟩ := hd (x, a) (by simpa using hx)
      have : ((d : 𝓞 E) : E) * x a = (z : E) := by
        rw [Algebra.smul_def] at hz
        exact hz.symm
      rw [this]
      exact z.isIntegral_coe
    | zero => simpa using isIntegral_zero
    | add x y _ _ hx hy => simpa [mul_add] using hx.add hy
    | smul c x _ hx =>
      have : ((d : 𝓞 E) : E) * (c • x) a = (c : E) * (((d : 𝓞 E) : E) * x a) := by
        rw [Pi.smul_apply, Algebra.smul_def]
        exact mul_left_comm _ _ _
      rw [this]
      exact c.isIntegral_coe.mul hx
  have h2 : ∀ v : Fin j → E, ∃ c : 𝓞 E, c ≠ 0 ∧ c • v ∈ Λ := by
    intro v
    have hv : v ∈ Submodule.span E (Λ : Set (Fin j → E)) := by
      rw [hΛ.span_eq_top]; trivial
    obtain ⟨t, ht⟩ := multiple_mem_span_of_mem_localization_span (nonZeroDivisors (𝓞 E)) E _ v hv
    rw [Submodule.span_eq] at ht
    exact ⟨t, nonZeroDivisors.coe_ne_zero t, ht⟩
  choose c hc0 hc using fun b : Fin j => h2 (Pi.single b 1)
  refine ⟨((d : 𝓞 E) : E) * ((∏ b, c b : 𝓞 E) : E), ?_, ?_⟩
  · refine mul_ne_zero ?_ ?_
    · exact RingOfIntegers.coe_ne_zero_iff.2 (nonZeroDivisors.coe_ne_zero d)
    · exact RingOfIntegers.coe_ne_zero_iff.2 (Finset.prod_ne_zero_iff.2 fun b _ => hc0 b)
  · intro γ hγ a b
    have h3 : (∏ b, c b) • (Pi.single b 1 : Fin j → E) ∈ Λ := by
      rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ b), mul_smul]
      exact Λ.smul_mem _ (hc b)
    have h4 := h1 _ ((hγ _).2 h3) a
    rw [Matrix.mulVec_smul, Matrix.mulVec_single_one, Pi.smul_apply, Algebra.smul_def] at h4
    rw [mul_assoc]
    exact h4

theorem finite_bounded (Λ : Submodule (𝓞 E) (Fin j → E)) (hΛ : Submodule.IsLattice E Λ) (C : ℝ) :
    {γ : GL (Fin j) E | γ ∈ autSub Λ ∧ ∀ w a b, ‖emb γ w a b‖ ≤ C}.Finite := by
  obtain ⟨N, hN, h⟩ := exists_denominator Λ hΛ
  set B : ℝ := (∑ φ : E →+* ℂ, ‖φ N‖) * C
  have hf := NumberField.Embeddings.finite_of_norm_le E ℂ B
  refine Set.Finite.of_finite_image (f := fun γ : GL (Fin j) E => fun a b => N * (γ : Matrix (Fin j) (Fin j) E) a b)
    ((Set.Finite.pi' fun _ => Set.Finite.pi' fun _ => hf).subset ?_) ?_
  · rintro _ ⟨γ, ⟨hγ, hb⟩, rfl⟩ a b
    refine ⟨h γ hγ a b, fun φ => ?_⟩
    rw [map_mul, norm_mul]
    have h1 : ‖φ ((γ : Matrix (Fin j) (Fin j) E) a b)‖ ≤ C := by
      have := hb (InfinitePlace.mk φ) a b
      rwa [emb, InfinitePlace.norm_embedding_eq, InfinitePlace.apply] at this
    refine mul_le_mul ?_ h1 (norm_nonneg _) (Finset.sum_nonneg fun _ _ => norm_nonneg _)
    exact Finset.single_le_sum (f := fun φ : E →+* ℂ => ‖φ N‖) (fun _ _ => norm_nonneg _) (Finset.mem_univ φ)
  · intro γ _ δ _ hγδ
    apply Units.ext
    ext a b
    exact mul_left_cancel₀ hN (congrFun (congrFun hγδ a) b)

def nrm (x : MatInf E j) : ℝ := ‖(show InfinitePlace E → Fin j → Fin j → ℂ from x)‖

theorem entry_le_nrm (x : MatInf E j) (w a b) : ‖x w a b‖ ≤ nrm x :=
  (norm_le_pi_norm (x w a) b).trans ((norm_le_pi_norm (x w) a).trans
    (norm_le_pi_norm (show InfinitePlace E → Fin j → Fin j → ℂ from x) w))

theorem finite_orbit (Λ : Submodule (𝓞 E) (Fin j → E)) (hΛ : Submodule.IsLattice E Λ) (x : MatInf E j)
    (hx : 0 < detNorm E j x) (C : ℝ) :
    {γ : GL (Fin j) E | γ ∈ autSub Λ ∧ nrm (emb γ * x) ≤ C}.Finite := by
  let y : MatInf E j := fun w a b => (Matrix.of (x w))⁻¹ a b
  refine (finite_bounded Λ hΛ (∑ _c : Fin j, C * nrm y)).subset ?_
  rintro γ ⟨hγ, hC⟩
  refine ⟨hγ, fun w a b => ?_⟩
  have h1 : Matrix.of (emb γ w) = Matrix.of ((emb γ * x) w) * Matrix.of (y w) := by
    rw [of_mul, Matrix.mul_assoc]
    change _ = _ * (_ * (Matrix.of (x w))⁻¹)
    rw [Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 ((detNorm_pos_iff x).1 hx w)), Matrix.mul_one]
  have h2 : emb γ w a b = ∑ c, (emb γ * x) w a c * y w c b := congrFun (congrFun h1 a) b
  rw [h2]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun c _ => ?_)
  rw [norm_mul]
  have h3 := (entry_le_nrm (emb γ * x) w a c).trans hC
  exact mul_le_mul h3 (entry_le_nrm y w c b) (norm_nonneg _) ((norm_nonneg _).trans h3)

def scl (t : ℝ) (x : MatInf E j) : MatInf E j := fun w a b => (t : ℂ) * x w a b

theorem nrm_scl (t : ℝ) (ht : 0 < t) (x : MatInf E j) : nrm (scl t x) = t * nrm x := by
  unfold nrm
  change ‖t • (show InfinitePlace E → Fin j → Fin j → ℂ from x)‖ = _
  rw [norm_smul, Real.norm_of_nonneg ht.le]

theorem scl_scl (s t : ℝ) (x : MatInf E j) : scl s (scl t x) = scl (s * t) x := by
  funext w a b
  simp [scl, mul_assoc]

theorem mul_scl (t : ℝ) (y x : MatInf E j) : y * scl t x = scl t (y * x) := by
  funext w a b
  change ∑ c, y w a c * ((t : ℂ) * x w c b) = (t : ℂ) * ∑ c, y w a c * x w c b
  simp [Finset.mul_sum, mul_left_comm]

theorem detNorm_scl_pos {t : ℝ} (ht : 0 < t) {x : MatInf E j} (hx : 0 < detNorm E j x) :
    0 < detNorm E j (scl t x) := by
  rw [detNorm_pos_iff] at hx ⊢
  intro w
  have : Matrix.of (scl t x w) = (t : ℂ) • Matrix.of (x w) := rfl
  rw [this, Matrix.det_smul]
  exact mul_ne_zero (pow_ne_zero _ (Complex.ofReal_ne_zero.2 ht.ne')) (hx w)

theorem measurable_nrm : Measurable (nrm : MatInf E j → ℝ) :=
  (measurable_norm : Measurable fun x : InfinitePlace E → Fin j → Fin j → ℂ => ‖x‖)

instance standardBorel : StandardBorelSpace (InfinitePlace E → Fin j → Fin j → ℂ) :=
  haveI : StandardBorelSpace (Fin j → ℂ) := StandardBorelSpace.pi_countable
  haveI : StandardBorelSpace (Fin j → Fin j → ℂ) := StandardBorelSpace.pi_countable
  StandardBorelSpace.pi_countable

def dir (x : MatInf E j) : ℝ :=
  embeddingReal (InfinitePlace E → Fin j → Fin j → ℂ) (scl (nrm x)⁻¹ x)

theorem measurable_dir : Measurable (dir : MatInf E j → ℝ) := by
  refine (measurable_embeddingReal (InfinitePlace E → Fin j → Fin j → ℂ)).comp ?_
  refine measurable_pi_lambda _ fun w => measurable_pi_lambda _ fun a => measurable_pi_lambda _ fun b => ?_
  have h : Measurable fun x : InfinitePlace E → Fin j → Fin j → ℂ => x w a b := by fun_prop
  exact (Complex.measurable_ofReal.comp measurable_nrm.inv).mul h

theorem dir_scl (t : ℝ) (ht : 0 < t) (x : MatInf E j) : dir (scl t x) = dir x := by
  unfold dir
  rw [nrm_scl t ht, scl_scl, mul_inv, mul_right_comm, inv_mul_cancel₀ ht.ne', one_mul]

theorem eq_of_nrm_dir {x y : MatInf E j} (h : nrm x = nrm y) (h' : dir x = dir y) : x = y := by
  have h1 := (measurableEmbedding_embeddingReal (InfinitePlace E → Fin j → Fin j → ℂ)).injective h'
  by_cases h0 : nrm x = 0
  · have hx : (show InfinitePlace E → Fin j → Fin j → ℂ from x) = 0 := norm_eq_zero.1 h0
    have hy : (show InfinitePlace E → Fin j → Fin j → ℂ from y) = 0 := norm_eq_zero.1 (h.symm.trans h0)
    exact hx.trans hy.symm
  · rw [← h] at h1
    funext w a b
    exact mul_left_cancel₀ (Complex.ofReal_ne_zero.2 (inv_ne_zero h0)) (congrFun (congrFun (congrFun h1 w) a) b)

def key (x : MatInf E j) : ℝ ×ₗ ℝ := toLex (nrm x, dir x)

theorem key_le {x y : MatInf E j} : key x ≤ key y ↔ nrm x < nrm y ∨ nrm x = nrm y ∧ dir x ≤ dir y :=
  Prod.Lex.toLex_le_toLex

theorem key_inj {x y : MatInf E j} (h : key x = key y) : x = y := by
  have := toLex.injective h
  exact eq_of_nrm_dir (congrArg Prod.fst this) (congrArg Prod.snd this)

def dom (Λ : Submodule (𝓞 E) (Fin j → E)) : Set (MatInf E j) :=
  {x | 0 < detNorm E j x ∧ ∀ γ : autSub Λ, key x ≤ key (emb (γ : GL (Fin j) E) * x)}

theorem countable_GL : Countable (GL (Fin j) E) := by
  haveI : Countable E := (Module.finBasis ℚ E).equivFun.toEquiv.injective.countable
  haveI : Countable (Matrix (Fin j) (Fin j) E) := inferInstanceAs (Countable (Fin j → Fin j → E))
  exact Units.val_injective.countable

theorem measurableSet_pos : MeasurableSet {g | 0 < detNorm E j g} :=
  measurableSet_lt measurable_const measurable_detNorm

theorem measurableSet_dom (Λ : Submodule (𝓞 E) (Fin j → E)) : MeasurableSet (dom Λ) := by
  haveI := countable_GL (E := E) (j := j)
  have : dom Λ = {g | 0 < detNorm E j g} ∩ ⋂ γ : autSub Λ, ({x | nrm x < nrm (emb (γ : GL (Fin j) E) * x)} ∪
      ({x | nrm x = nrm (emb (γ : GL (Fin j) E) * x)} ∩ {x | dir x ≤ dir (emb (γ : GL (Fin j) E) * x)})) := by
    ext x
    simp [dom, key_le]
  rw [this]
  refine measurableSet_pos.inter (MeasurableSet.iInter fun γ => ?_)
  have hm := measurable_mul_left (emb (γ : GL (Fin j) E))
  exact (measurableSet_lt measurable_nrm (measurable_nrm.comp hm)).union
    ((measurableSet_eq_fun measurable_nrm (measurable_nrm.comp hm)).inter
      (measurableSet_le measurable_dir (measurable_dir.comp hm)))

theorem exists_mul_mem_dom (Λ : Submodule (𝓞 E) (Fin j → E)) (hΛ : Submodule.IsLattice E Λ) (x : MatInf E j)
    (hx : 0 < detNorm E j x) : ∃ γ ∈ autSub Λ, emb γ * x ∈ dom Λ := by
  have h1 : (1 : GL (Fin j) E) ∈ {γ : GL (Fin j) E | γ ∈ autSub Λ ∧ nrm (emb γ * x) ≤ nrm x} :=
    ⟨one_mem _, by rw [emb_one_mul]⟩
  obtain ⟨γ, hγ, hmin⟩ := Set.exists_min_image _ (fun γ => key (emb γ * x)) (finite_orbit Λ hΛ x hx (nrm x))
    ⟨1, h1⟩
  refine ⟨γ, hγ.1, (detNorm_emb_mul_pos γ x).2 hx, fun δ => ?_⟩
  rw [← matInf_mul_assoc, ← emb_mul]
  by_cases h : nrm (emb ((δ : GL (Fin j) E) * γ) * x) ≤ nrm x
  · exact hmin _ ⟨mul_mem δ.2 hγ.1, h⟩
  · exact key_le.2 (Or.inl (hγ.2.trans_lt (not_le.1 h)))

theorem eq_one_of_mem_dom {Λ : Submodule (𝓞 E) (Fin j → E)} {x : MatInf E j} {γ : autSub Λ} (hx : x ∈ dom Λ)
    (h : emb (γ : GL (Fin j) E) * x ∈ dom Λ) : γ = 1 := by
  have h1 := h.2 γ⁻¹
  rw [← matInf_mul_assoc, ← emb_mul, Subgroup.coe_inv, inv_mul_cancel, emb_one_mul] at h1
  have h2 := key_inj (le_antisymm h1 (hx.2 γ))
  exact Subtype.ext (eq_of_emb_mul_eq hx.1 (h2.trans (emb_one_mul x).symm))

theorem scl_mem_dom {Λ : Submodule (𝓞 E) (Fin j → E)} {x : MatInf E j} (hx : x ∈ dom Λ) {t : ℝ} (ht : 0 < t) :
    scl t x ∈ dom Λ := by
  refine ⟨detNorm_scl_pos ht hx.1, fun γ => ?_⟩
  have := hx.2 γ
  rw [key_le] at this ⊢
  rw [mul_scl, nrm_scl t ht, nrm_scl t ht, dir_scl t ht, dir_scl t ht]
  rcases this with h | ⟨h, h'⟩
  · exact Or.inl (mul_lt_mul_of_pos_left h ht)
  · exact Or.inr ⟨by rw [h], h'⟩

@[reducible] def act (Λ : Submodule (𝓞 E) (Fin j → E)) : MulAction (autSub Λ) (MatInf E j) where
  smul γ x := emb (γ : GL (Fin j) E) * x
  one_smul x := emb_one_mul x
  mul_smul γ δ x := by
    change emb ((γ : GL (Fin j) E) * (δ : GL (Fin j) E)) * x = emb (γ : GL (Fin j) E) * (emb (δ : GL (Fin j) E) * x)
    rw [emb_mul, matInf_mul_assoc]

open scoped Pointwise in
theorem covol_eq (Λ : Submodule (𝓞 E) (Fin j → E)) (hΛ : Submodule.IsLattice E Λ) (ν : Measure (MatInf E j))
    (hν : ∀ γ ∈ autSub Λ, ν.map (fun x => emb γ * x) = ν) (h0 : ν {g | 0 < detNorm E j g}ᶜ = 0)
    (A : Set (MatInf E j)) (hA : MeasurableSet A) (hAX : A ⊆ {g | 0 < detNorm E j g})
    (hinv : ∀ γ ∈ autGL E j Λ, ∀ g ∈ A, γ * g ∈ A) : covol (autGL E j Λ) ν A = ν (A ∩ dom Λ) := by
  letI := act Λ
  haveI := countable_GL (E := E) (j := j)
  have : MeasurableConstSMul (autSub Λ) (MatInf E j) := ⟨fun γ => measurable_mul_left _⟩
  have : SMulInvariantMeasure (autSub Λ) (MatInf E j) ν := ⟨fun γ s hs => by
    have h := hν γ γ.2
    conv_rhs => rw [← h]
    rw [Measure.map_apply (measurable_mul_left _) hs]
    rfl⟩
  have hF : IsFundamentalDomain (autSub Λ) (dom Λ) ν := by
    refine IsFundamentalDomain.mk'' (measurableSet_dom Λ).nullMeasurableSet ?_ ?_ ?_
    · filter_upwards [(h0 : ∀ᵐ g ∂ν, g ∈ {g | 0 < detNorm E j g})] with y hy
      obtain ⟨γ, hγ, h⟩ := exists_mul_mem_dom Λ hΛ y hy
      exact ⟨⟨γ, hγ⟩, h⟩
    · intro γ hγ
      refine Disjoint.aedisjoint (Set.disjoint_left.2 ?_)
      rintro _ ⟨x, hx, rfl⟩ h
      exact hγ (eq_one_of_mem_dom hx h)
    · intro γ
      exact (measurePreserving_smul γ ν).quasiMeasurePreserving
  apply le_antisymm
  · unfold covol
    refine iInf_le_of_le (A ∩ dom Λ) (iInf_le_of_le (hA.inter (measurableSet_dom Λ)) (iInf_le_of_le ?_ le_rfl))
    intro x hx
    obtain ⟨γ, hγ, h⟩ := exists_mul_mem_dom Λ hΛ x (hAX hx)
    have hγ' : emb γ ∈ autGL E j Λ := mem_autGL.2 ⟨γ, hγ, rfl⟩
    exact ⟨emb γ, hγ', hinv _ hγ' x hx, h⟩
  · unfold covol
    refine le_iInf fun D => le_iInf fun _ => le_iInf fun hD => ?_
    rw [hF.measure_eq_tsum D]
    refine le_trans (measure_mono ?_) (measure_iUnion_le _)
    rintro x ⟨hx, hxf⟩
    obtain ⟨_, hγ', h⟩ := hD x hx
    obtain ⟨γ, hγ, rfl⟩ := mem_autGL.1 hγ'
    refine Set.mem_iUnion.2 ⟨(⟨γ, hγ⟩ : autSub Λ)⁻¹, ?_, hxf⟩
    rw [Set.mem_inv_smul_set_iff]
    exact h

theorem exists_cone_domain : ∀ (E : Type) [Field E] [NumberField E], IsTotallyComplex E → ∀ j : ℕ, ∀ Λ : Submodule (𝓞 E) (Fin j → E), Submodule.IsLattice E Λ → ∃ D : Set (MatInf E j), MeasurableSet D ∧ D ⊆ {g | 0 < detNorm E j g} ∧ (∀ g, 0 < detNorm E j g → ∃ γ ∈ autGL E j Λ, γ * g ∈ D) ∧ (∀ g ∈ D, ∀ t : ℝ, 0 < t → (fun w a b => (t : ℂ) * g w a b) ∈ D) ∧ ∀ (G : MatInf E j → ENNReal) (A : Set (MatInf E j)), Measurable (fun g => {g | 0 < detNorm E j g}.indicator G g) → (∀ γ ∈ autGL E j Λ, ∀ g, 0 < detNorm E j g → G (γ * g) = G g) → MeasurableSet A → A ⊆ {g | 0 < detNorm E j g} → (∀ γ ∈ autGL E j Λ, ∀ g ∈ A, γ * g ∈ A) → covol (autGL E j Λ) (((haarGL E j).restrict {g | 0 < detNorm E j g}).withDensity G) A = ∫⁻ g in A ∩ D, G g ∂(haarGL E j) := by
  intro E _ _ _ j Λ hΛ
  refine ⟨dom Λ, measurableSet_dom Λ, fun x hx => hx.1, ?_, fun g hg t ht => scl_mem_dom hg ht, ?_⟩
  · intro g hg
    obtain ⟨γ, hγ, h⟩ := exists_mul_mem_dom Λ hΛ g hg
    exact ⟨emb γ, mem_autGL.2 ⟨γ, hγ, rfl⟩, h⟩
  intro G A hG hGinv hA hAX hinv
  have hAD := hA.inter (measurableSet_dom Λ)
  rw [covol_eq Λ hΛ _ ?_ ?_ A hA hAX hinv]
  · rw [withDensity_apply _ hAD, Measure.restrict_restrict hAD,
      Set.inter_eq_left.2 (Set.inter_subset_left.trans hAX)]
  · intro γ hγ
    rw [← withDensity_indicator measurableSet_pos]
    set G' : MatInf E j → ENNReal := {g | 0 < detNorm E j g}.indicator G with hG'
    have hG1 : Measurable G' := hG
    have hG2 : ∀ x, G' (emb γ * x) = G' x := by
      intro x
      by_cases hx : 0 < detNorm E j x
      · rw [hG', Set.indicator_of_mem (show x ∈ {g | 0 < detNorm E j g} from hx),
          Set.indicator_of_mem (show emb γ * x ∈ {g | 0 < detNorm E j g} from (detNorm_emb_mul_pos γ x).2 hx)]
        exact hGinv _ (mem_autGL.2 ⟨γ, hγ, rfl⟩) x hx
      · rw [hG', Set.indicator_of_notMem (show x ∉ {g | 0 < detNorm E j g} from hx),
          Set.indicator_of_notMem
            (show emb γ * x ∉ {g | 0 < detNorm E j g} from fun h => hx ((detNorm_emb_mul_pos γ x).1 h))]
    ext s hs
    have hm := measurable_mul_left (emb γ)
    rw [Measure.map_apply hm hs, withDensity_apply _ hs, withDensity_apply _ (hm hs), ← lintegral_indicator hs,
      ← lintegral_indicator (hm hs), ← lintegral_haarGL_mul_left (emb γ) (detNorm_emb_pos γ) _ (hG1.indicator hs)]
    refine lintegral_congr fun x => ?_
    by_cases hx : emb γ * x ∈ s
    · rw [Set.indicator_of_mem hx, Set.indicator_of_mem (show x ∈ (fun x => emb γ * x) ⁻¹' s from hx), hG2]
    · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem (show x ∉ (fun x => emb γ * x) ⁻¹' s from hx)]
  · refine withDensity_absolutelyContinuous _ _ ?_
    rw [Measure.restrict_apply measurableSet_pos.compl, Set.compl_inter_self, measure_empty]

end GlobalTheory.LatDom
