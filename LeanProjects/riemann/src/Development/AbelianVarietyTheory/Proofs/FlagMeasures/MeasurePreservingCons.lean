import Mathlib
open MeasureTheory Matrix
open scoped ENNReal

namespace GlobalTheory.GLFirstColumn

theorem lintegral_linear {ι κ : Type} [Fintype ι] [Fintype κ]
    (L : (κ → ι → ℂ) →ₗ[ℂ] (κ → ι → ℂ)) (hL : LinearMap.det L ≠ 0)
    (F : (κ → ι → ℂ) → ℝ≥0∞) (hF : Measurable F) :
    ∫⁻ c, F c = ENNReal.ofReal (‖LinearMap.det L‖ ^ 2) * ∫⁻ z, F (L z) := by
  have hdet : LinearMap.det (L.restrictScalars ℝ) = ‖LinearMap.det L‖ ^ 2 := by
    rw [LinearMap.det_restrictScalars, Algebra.norm_complex_apply, Complex.normSq_eq_norm_sq]
  have hpos : 0 < ‖LinearMap.det L‖ ^ 2 := pow_pos (norm_pos_iff.2 hL) _
  haveI : (volume : Measure (ι → ℂ)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
  haveI : (volume : Measure (κ → ι → ℂ)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
  have hmap := Measure.map_linearMap_addHaar_eq_smul_addHaar (volume : Measure (κ → ι → ℂ))
    (f := L.restrictScalars ℝ) (by rw [hdet]; exact hpos.ne')
  have hm : Measurable (L.restrictScalars ℝ) :=
    (LinearMap.continuous_of_finiteDimensional _).measurable
  have h1 := lintegral_map (μ := volume) hF hm
  rw [hmap, lintegral_smul_measure, hdet, abs_of_pos (inv_pos.2 hpos)] at h1
  simp only [LinearMap.restrictScalars_apply] at h1
  rw [← h1, smul_eq_mul, ← mul_assoc,
    ← ENNReal.ofReal_mul hpos.le, mul_inv_cancel₀ hpos.ne', ENNReal.ofReal_one, one_mul]

theorem lintegral_right {n k : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (hA : A.det ≠ 0)
    (F : (Fin k → Fin n → ℂ) → ℝ≥0∞) (hF : Measurable F) :
    ∫⁻ c, F c = ENNReal.ofReal ((‖A.det‖ ^ 2) ^ k) *
      ∫⁻ z : Fin k → Fin n → ℂ, F (fun a b => (Matrix.of z * A) a b) := by
  let L : (Fin k → Fin n → ℂ) →ₗ[ℂ] (Fin k → Fin n → ℂ) :=
    LinearMap.pi fun i => (Matrix.toLin' Aᵀ).comp (LinearMap.proj i)
  have hL : LinearMap.det L = A.det ^ k := by
    rw [LinearMap.det_pi]; simp [LinearMap.det_toLin']
  have h2 : ∀ z : Fin k → Fin n → ℂ, L z = fun a b => (Matrix.of z * A) a b := by
    intro z; ext a b
    simp [L, Matrix.toLin'_apply, mulVec_transpose, vecMul, dotProduct, Matrix.mul_apply]
  rw [lintegral_linear L (hL ▸ pow_ne_zero _ hA) F hF, hL, norm_pow, ← pow_mul, ← pow_mul, mul_comm k]
  simp only [h2]

theorem lintegral_left {n k : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (hA : A.det ≠ 0)
    (F : (Fin n → Fin k → ℂ) → ℝ≥0∞) (hF : Measurable F) :
    ∫⁻ c, F c = ENNReal.ofReal ((‖A.det‖ ^ 2) ^ k) *
      ∫⁻ z : Fin n → Fin k → ℂ, F (fun a b => (A * Matrix.of z) a b) := by
  let P : (Fin k → Fin n → ℂ) →ₗ[ℂ] (Fin k → Fin n → ℂ) :=
    LinearMap.pi fun c => (Matrix.toLin' A).comp (LinearMap.proj c)
  let e : (Fin k → Fin n → ℂ) ≃ₗ[ℂ] (Fin n → Fin k → ℂ) :=
    { toFun := fun x a b => x b a
      invFun := fun x a b => x b a
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  let L : (Fin n → Fin k → ℂ) →ₗ[ℂ] (Fin n → Fin k → ℂ) :=
    (e : _ →ₗ[ℂ] _) ∘ₗ P ∘ₗ (e.symm : _ →ₗ[ℂ] _)
  have hL : LinearMap.det L = A.det ^ k := by
    rw [LinearMap.det_conj, LinearMap.det_pi]
    simp
  have h2 : ∀ z : Fin n → Fin k → ℂ, L z = fun a b => (A * Matrix.of z) a b := fun z => rfl
  rw [lintegral_linear L (hL ▸ pow_ne_zero _ hA) F hF, hL, norm_pow, ← pow_mul, ← pow_mul, mul_comm k]
  simp only [h2]

def mulM {m : ℕ} (x y : Fin m → Fin m → ℂ) : Fin m → Fin m → ℂ :=
  fun i j => (Matrix.of x * Matrix.of y) i j

noncomputable def invM {m : ℕ} (x : Fin m → Fin m → ℂ) : Fin m → Fin m → ℂ :=
  fun i j => (Matrix.of x)⁻¹ i j

lemma of_mulM {m : ℕ} (x y : Fin m → Fin m → ℂ) :
    Matrix.of (mulM x y) = Matrix.of x * Matrix.of y := rfl

lemma of_invM {m : ℕ} (x : Fin m → Fin m → ℂ) : Matrix.of (invM x) = (Matrix.of x)⁻¹ := rfl

lemma measurable_mulM {m : ℕ} {α : Type*} [MeasurableSpace α] {u v : α → Fin m → Fin m → ℂ}
    (hu : Measurable u) (hv : Measurable v) : Measurable fun a => mulM (u a) (v a) := by
  refine measurable_pi_lambda _ fun i => measurable_pi_lambda _ fun j => ?_
  simp only [mulM, Matrix.mul_apply, Matrix.of_apply]
  refine Finset.measurable_sum _ fun k _ => Measurable.mul ?_ ?_
  · exact (measurable_pi_apply k).comp ((measurable_pi_apply i).comp hu)
  · exact (measurable_pi_apply j).comp ((measurable_pi_apply k).comp hv)

lemma continuous_detM {m : ℕ} : Continuous fun x : Fin m → Fin m → ℂ => (Matrix.of x).det :=
  Continuous.matrix_det continuous_id

lemma measurable_invM {m : ℕ} :
    Measurable (invM : (Fin m → Fin m → ℂ) → Fin m → Fin m → ℂ) := by
  refine measurable_pi_lambda _ fun i => measurable_pi_lambda _ fun j => ?_
  have hof : Continuous fun x : Fin m → Fin m → ℂ =>
    (Matrix.of x : Matrix (Fin m) (Fin m) ℂ) := continuous_id
  have h1 : Measurable fun x : Fin m → Fin m → ℂ => (Matrix.of x).det := hof.matrix_det.measurable
  have h2 : Measurable fun x : Fin m → Fin m → ℂ => (Matrix.of x).adjugate i j :=
    (hof.matrix_adjugate.matrix_elem i j).measurable
  simp only [invM, Matrix.inv_def, Ring.inverse_eq_inv', Matrix.smul_apply, smul_eq_mul]
  exact h1.inv.mul h2

noncomputable def wt {m : ℕ} (x : Fin m → Fin m → ℂ) : ℝ≥0∞ :=
  ENNReal.ofReal ((‖(Matrix.of x).det‖ ^ 2)⁻¹ ^ m)

lemma measurable_wt {m : ℕ} : Measurable (wt : (Fin m → Fin m → ℂ) → ℝ≥0∞) :=
  (((continuous_detM.norm.measurable.pow_const 2).inv).pow_const m).ennreal_ofReal

lemma wt_mul {m : ℕ} (a y : Fin m → Fin m → ℂ) : wt (mulM a y) = wt a * wt y := by
  unfold wt
  rw [of_mulM, det_mul, norm_mul, mul_pow, mul_inv, mul_pow, ENNReal.ofReal_mul (by positivity)]

lemma wt_cancel {m : ℕ} (a : Fin m → Fin m → ℂ) (ha : (Matrix.of a).det ≠ 0) :
    ENNReal.ofReal ((‖(Matrix.of a).det‖ ^ 2) ^ m) * wt a = 1 := by
  have : ‖(Matrix.of a).det‖ ^ 2 ≠ 0 := pow_ne_zero _ (norm_ne_zero_iff.2 ha)
  unfold wt
  rw [← ENNReal.ofReal_mul (by positivity), ← mul_pow, mul_inv_cancel₀ this, one_pow,
    ENNReal.ofReal_one]

lemma wt_eq_zero {m : ℕ} (a : Fin m → Fin m → ℂ) (ha : (Matrix.of a).det = 0) : wt a = 0 := by
  rcases m with _ | m
  · simp at ha
  · simp [wt, ha]

theorem lintegral_inv {m : ℕ} (f : (Fin m → Fin m → ℂ) → ℝ≥0∞) (hf : Measurable f) :
    ∫⁻ s, f (invM s) * wt s = ∫⁻ s, f s * wt s := by
  set μ : Measure (Fin m → Fin m → ℂ) := volume.withDensity wt with hμ
  have hint : ∀ g : (Fin m → Fin m → ℂ) → ℝ≥0∞, Measurable g →
      ∫⁻ y, g y ∂μ = ∫⁻ y, g y * wt y := by
    intro g hg
    rw [hμ, lintegral_withDensity_eq_lintegral_mul _ measurable_wt hg]
    simp only [Pi.mul_apply, mul_comm]
  haveI : SigmaFinite μ := SigmaFinite.withDensity_of_ne_top
    (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_ne_top)
  have hae : ∀ᵐ x ∂μ, (Matrix.of x).det ≠ 0 := by
    rw [hμ, ae_withDensity_iff measurable_wt]
    exact Filter.Eventually.of_forall fun x hx h => hx (wt_eq_zero x h)
  have hne : μ ≠ 0 := by
    intro h
    rw [hμ, withDensity_eq_zero_iff measurable_wt.aemeasurable] at h
    haveI : (volume : Measure (Fin m → ℂ)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
    haveI : (volume : Measure (Fin m → Fin m → ℂ)).IsAddHaarMeasure :=
      Measure.pi.isAddHaarMeasure _
    have ho : IsOpen {x : Fin m → Fin m → ℂ | (Matrix.of x).det ≠ 0} :=
      isOpen_ne_fun continuous_detM continuous_const
    have hp := ho.measure_pos volume ⟨(1 : Matrix (Fin m) (Fin m) ℂ), by
      show (1 : Matrix (Fin m) (Fin m) ℂ).det ≠ 0
      simp⟩
    refine hp.ne' (measure_mono_null (fun x hx => ?_) h)
    intro h0
    have := wt_cancel x hx
    simp only [Set.mem_setOf_eq, Pi.zero_apply] at h0
    rw [h0, mul_zero] at this
    exact zero_ne_one this
  have left : ∀ a : Fin m → Fin m → ℂ, (Matrix.of a).det ≠ 0 →
      ∀ g : (Fin m → Fin m → ℂ) → ℝ≥0∞, Measurable g →
      ∫⁻ y, g (mulM a y) ∂μ = ∫⁻ y, g y ∂μ := by
    intro a ha g hg
    have hm : Measurable fun y => g (mulM a y) :=
      hg.comp (measurable_mulM (measurable_const (a := a)) measurable_id')
    rw [hint _ hm, hint _ hg, lintegral_left _ ha (fun y => g y * wt y) (hg.mul measurable_wt),
      ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine lintegral_congr fun y => ?_
    show g (mulM a y) * wt y = _ * (g (mulM a y) * wt (mulM a y))
    rw [wt_mul, mul_left_comm, ← mul_assoc _ (wt a), wt_cancel a ha, one_mul]
  have right : ∀ a : Fin m → Fin m → ℂ, (Matrix.of a).det ≠ 0 →
      ∀ g : (Fin m → Fin m → ℂ) → ℝ≥0∞, Measurable g →
      ∫⁻ y, g (mulM y a) ∂μ = ∫⁻ y, g y ∂μ := by
    intro a ha g hg
    have hm : Measurable fun y => g (mulM y a) :=
      hg.comp (measurable_mulM measurable_id' (measurable_const (a := a)))
    rw [hint _ hm, hint _ hg, lintegral_right _ ha (fun y => g y * wt y) (hg.mul measurable_wt),
      ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine lintegral_congr fun y => ?_
    show g (mulM y a) * wt y = _ * (g (mulM y a) * wt (mulM y a))
    rw [wt_mul, mul_left_comm, mul_comm (wt y), ← mul_assoc _ (wt a), wt_cancel a ha, one_mul]
  have hfi : Measurable fun x => f (invM x) := hf.comp measurable_invM
  rw [← hint _ hfi, ← hint _ hf]
  obtain ⟨t, ht, -, ht0, ht1⟩ := Measure.exists_subset_measure_lt_top (μ := μ) (r := 0)
    MeasurableSet.univ (Measure.measure_univ_pos.mpr hne)
  set g : (Fin m → Fin m → ℂ) → ℝ≥0∞ := t.indicator 1 with hgdef
  have hg : Measurable g := measurable_one.indicator ht
  have hgi : ∫⁻ y, g y ∂μ = μ t := lintegral_indicator_one ht
  have key : (∫⁻ x, f (invM x) ∂μ) * μ t = (∫⁻ x, f x ∂μ) * μ t := by
    calc (∫⁻ x, f (invM x) ∂μ) * μ t
        = ∫⁻ x, ∫⁻ y, f (invM x) * g (mulM x y) ∂μ ∂μ := by
          rw [← lintegral_mul_const _ hfi]
          refine lintegral_congr_ae (hae.mono fun x hx => ?_)
          simp only
          have hm : Measurable fun y => g (mulM x y) :=
            hg.comp (measurable_mulM measurable_const measurable_id')
          rw [lintegral_const_mul _ hm, left x hx g hg, hgi]
      _ = ∫⁻ y, ∫⁻ x, f (invM x) * g (mulM x y) ∂μ ∂μ := by
          refine lintegral_lintegral_swap (Measurable.aemeasurable ?_)
          exact (hfi.comp measurable_fst).mul
            (hg.comp (measurable_mulM measurable_fst measurable_snd))
      _ = ∫⁻ y, ∫⁻ x, f (mulM y (invM x)) * g x ∂μ ∂μ := by
          refine lintegral_congr_ae (hae.mono fun y hy => ?_)
          simp only
          rw [← right y hy (fun x => f (mulM y (invM x)) * g x)
            ((hf.comp (measurable_mulM measurable_const measurable_invM)).mul hg)]
          refine lintegral_congr fun x => ?_
          congr 2
          apply Matrix.of.injective
          rw [of_mulM, of_invM, of_invM, of_mulM, Matrix.mul_inv_rev, ← Matrix.mul_assoc,
            Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 hy), Matrix.one_mul]
      _ = ∫⁻ x, ∫⁻ y, f (mulM y (invM x)) * g x ∂μ ∂μ := by
          refine lintegral_lintegral_swap (Measurable.aemeasurable ?_)
          exact (hf.comp (measurable_mulM measurable_fst
            (measurable_invM.comp measurable_snd))).mul (hg.comp measurable_snd)
      _ = ∫⁻ x, (∫⁻ y, f y ∂μ) * g x ∂μ := by
          refine lintegral_congr_ae (hae.mono fun x hx => ?_)
          simp only
          have hm : Measurable fun y => f (mulM y (invM x)) :=
            hf.comp (measurable_mulM measurable_id' measurable_const)
          have hx' : (Matrix.of (invM x)).det ≠ 0 :=
            (Matrix.isUnit_nonsing_inv_det _ (isUnit_iff_ne_zero.2 hx)).ne_zero
          rw [lintegral_mul_const _ hm, right (invM x) hx' f hf]
      _ = (∫⁻ x, f x ∂μ) * μ t := by rw [lintegral_const_mul _ hg, hgi]
  exact (ENNReal.mul_left_inj ht0.ne' ht1.ne).mp key

theorem exists_section (k : ℕ) (hk : 1 ≤ k) :
    ∃ s : (Fin (k + 1) → ℂ) → Fin (k + 1) → Fin (k + 1) → ℂ, Measurable s ∧
      ∀ x, x ≠ 0 → (Matrix.of (s x)).det = 1 ∧ ∀ a, s x a 0 = x a := by
  classical
  let B : Fin (k + 1) → (Fin (k + 1) → ℂ) → Fin (k + 1) → Fin (k + 1) → ℂ := fun i x =>
    ((1 : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ).updateCol i x).submatrix id (Equiv.swap 0 i)
  have hBm : ∀ i, Measurable (B i) := fun i => by
    refine measurable_pi_lambda _ fun a => measurable_pi_lambda _ fun b => ?_
    simp only [B, submatrix_apply, updateCol_apply, id]
    split_ifs
    · exact measurable_pi_apply a
    · exact measurable_const
  have hBd : ∀ i x, x i ≠ 0 → (Matrix.of (B i x)).det ≠ 0 := fun i x hx => by
    show (((1 : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ).updateCol i x).submatrix id
      (Equiv.swap 0 i)).det ≠ 0
    rw [det_permute', ← cramer_apply, cramer_one]
    refine mul_ne_zero ?_ hx
    rcases Int.units_eq_one_or (Equiv.Perm.sign (Equiv.swap 0 i)) with h | h <;> simp [h]
  have hex : ∀ x : Fin (k + 1) → ℂ, ∃ n : ℕ, x = 0 ∨ x (Fin.ofNat (k + 1) n) ≠ 0 := fun x => by
    by_cases h : x = 0
    · exact ⟨0, Or.inl h⟩
    · obtain ⟨i, hi⟩ := Function.ne_iff.1 h
      exact ⟨i, Or.inr (by simpa using hi)⟩
  let C : (Fin (k + 1) → ℂ) → Fin (k + 1) → Fin (k + 1) → ℂ := fun x =>
    B (Fin.ofNat (k + 1) (Nat.find (hex x))) x
  have hCm : Measurable C := by
    refine Measurable.find (f := fun n x => B (Fin.ofNat (k + 1) n) x)
      (p := fun n x => x = 0 ∨ x (Fin.ofNat (k + 1) n) ≠ 0) (fun n => hBm _) (fun n => ?_) hex
    have h1 : Measurable fun x : Fin (k + 1) → ℂ => x (Fin.ofNat (k + 1) n) :=
      measurable_pi_apply _
    exact (measurableSet_singleton 0).union (h1 (measurableSet_singleton (0 : ℂ)).compl)
  have hl : (0 : Fin (k + 1)) ≠ Fin.last k := by
    intro h
    have := congrArg Fin.val h
    simp at this
    omega
  refine ⟨fun x => (Matrix.of (C x)).updateCol (Fin.last k)
    (((Matrix.of (C x)).det)⁻¹ • fun a => C x a (Fin.last k)), ?_, fun x hx => ⟨?_, fun a => ?_⟩⟩
  · refine measurable_pi_lambda _ fun a => measurable_pi_lambda _ fun b => ?_
    have h1 : ∀ b, Measurable fun x => C x a b := fun b =>
      (measurable_pi_apply b).comp ((measurable_pi_apply a).comp hCm)
    simp only [updateCol_apply, of_apply, Pi.smul_apply, smul_eq_mul]
    split_ifs
    · exact (continuous_detM.measurable.comp hCm).inv.mul (h1 _)
    · exact h1 _
  · have hd : (Matrix.of (C x)).det ≠ 0 := hBd _ x ((Nat.find_spec (hex x)).resolve_left hx)
    show ((Matrix.of (C x)).updateCol (Fin.last k)
      (((Matrix.of (C x)).det)⁻¹ • fun a => (Matrix.of (C x)) a (Fin.last k))).det = 1
    rw [det_updateCol_smul, updateCol_eq_self, inv_mul_cancel₀ hd]
  · refine (updateCol_ne hl).trans ?_
    show (1 : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ).updateCol _ x a (Equiv.swap 0 _ 0) = x a
    rw [Equiv.swap_apply_left, updateCol_self]

theorem measurePreserving_cons (X : Type) [MeasureSpace X] [SigmaFinite (volume : Measure X)]
    (n : ℕ) : MeasurePreserving
      (fun p : X × (Fin n → X) => (Fin.cons p.1 p.2 : Fin (n + 1) → X)) volume volume := by
  have h := (volume_preserving_piFinSuccAbove (fun _ : Fin (n + 1) => X) 0).symm
  have e : (fun p : X × (Fin n → X) => (Fin.cons p.1 p.2 : Fin (n + 1) → X)) =
      (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => X) 0).symm := by
    funext p
    simp [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv, Fin.insertNth_zero']
  rw [e]
  exact h

theorem lintegral_first_col {n k : ℕ} (F : (Fin n → Fin (k + 1) → ℂ) → ℝ≥0∞) (hF : Measurable F) :
    ∫⁻ y, F y = ∫⁻ x : Fin n → ℂ, ∫⁻ Y : Fin n → Fin k → ℂ, F fun a => Fin.cons (x a) (Y a) := by
  have h1 := volume_preserving_pi (ι := Fin n) (α' := fun _ => ℂ × (Fin k → ℂ))
    (β' := fun _ => Fin (k + 1) → ℂ) (fun _ => measurePreserving_cons ℂ k)
  have h2 := (volume_measurePreserving_arrowProdEquivProdArrow ℂ (Fin k → ℂ) (Fin n)).symm
  have h3 := h1.comp h2
  rw [← h3.lintegral_comp hF, Measure.volume_eq_prod]
  exact lintegral_prod _ (hF.comp h3.measurable).aemeasurable

theorem lintegral_first_row {n k : ℕ} (F : (Fin (n + 1) → Fin k → ℂ) → ℝ≥0∞) (hF : Measurable F) :
    ∫⁻ y, F y = ∫⁻ m : Fin n → Fin k → ℂ, ∫⁻ r : Fin k → ℂ, F (Fin.cons r m) := by
  have h3 := measurePreserving_cons (Fin k → ℂ) n
  rw [← h3.lintegral_comp hF, Measure.volume_eq_prod]
  exact lintegral_prod_symm _ (hF.comp h3.measurable).aemeasurable

def blk {k : ℕ} (r : Fin k → ℂ) (m : Fin k → Fin k → ℂ) : Fin (k + 1) → Fin (k + 1) → ℂ :=
  Fin.cons (Fin.cons 1 r) fun a => Fin.cons 0 (m a)

lemma det_blk {k : ℕ} (r : Fin k → ℂ) (m : Fin k → Fin k → ℂ) :
    (Matrix.of (blk r m)).det = (Matrix.of m).det := by
  rw [det_succ_column_zero, Fin.sum_univ_succ]
  simp only [blk, of_apply, Fin.cons_zero, Fin.cons_succ, mul_zero, zero_mul,
    Finset.sum_const_zero, add_zero, Fin.val_zero, pow_zero, one_mul]
  congr 1

lemma inv_blk {k : ℕ} (T : Fin k → ℂ) (m : Fin k → Fin k → ℂ) (hm : (Matrix.of m).det ≠ 0) :
    (Matrix.of (blk (-T) m))⁻¹ = Matrix.of (blk (T ᵥ* Matrix.of (invM m)) (invM m)) := by
  refine Matrix.inv_eq_right_inv ?_
  have h := Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 hm)
  ext a b
  refine Fin.cases ?_ (fun a => ?_) a <;> refine Fin.cases ?_ (fun b => ?_) b
  · simp [blk, Matrix.mul_apply, Fin.sum_univ_succ]
  · simp [blk, Matrix.mul_apply, Fin.sum_univ_succ, vecMul, dotProduct, Matrix.one_apply,
      (Fin.succ_ne_zero b).symm]
  · simp [blk, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.one_apply]
  · have := congrFun (congrFun h a) b
    simpa [blk, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.one_apply, invM] using this

lemma measurable_blk {k : ℕ} {α : Type*} [MeasurableSpace α] {u : α → Fin k → ℂ}
    {v : α → Fin k → Fin k → ℂ} (hu : Measurable u) (hv : Measurable v) :
    Measurable fun t => blk (u t) (v t) := by
  refine measurable_pi_lambda _ fun a => measurable_pi_lambda _ fun b => ?_
  refine Fin.cases ?_ (fun a => ?_) a <;> refine Fin.cases ?_ (fun b => ?_) b
  · exact measurable_const
  · exact (measurable_pi_apply b).comp hu
  · exact measurable_const
  · exact (measurable_pi_apply b).comp ((measurable_pi_apply a).comp hv)

theorem lintegral_blk_inv {k : ℕ} (ψ : (Fin (k + 1) → Fin (k + 1) → ℂ) → ℝ≥0∞)
    (hψ : Measurable ψ) :
    ∫⁻ m : Fin k → Fin k → ℂ, ∫⁻ r : Fin k → ℂ, ψ (invM (blk r m)) * wt (blk r m) =
      ∫⁻ h : Fin k → Fin k → ℂ, ∫⁻ T : Fin k → ℂ, ψ (blk (T ᵥ* Matrix.of h) h) *
        ENNReal.ofReal (‖(Matrix.of h).det‖ ^ 2 * (‖(Matrix.of h).det‖ ^ 2)⁻¹ ^ k) := by
  have hv : Measurable fun p : (Fin k → Fin k → ℂ) × (Fin k → ℂ) => p.2 ᵥ* Matrix.of p.1 := by
    refine Continuous.measurable (continuous_pi fun b => ?_)
    simp only [vecMul, dotProduct, of_apply]
    fun_prop
  have hb : Measurable fun p : (Fin k → Fin k → ℂ) × (Fin k → ℂ) =>
      ψ (blk (p.2 ᵥ* Matrix.of p.1) p.1) := hψ.comp (measurable_blk hv measurable_fst)
  let G : (Fin k → Fin k → ℂ) → ℝ≥0∞ := fun h =>
    (∫⁻ T : Fin k → ℂ, ψ (blk (T ᵥ* Matrix.of h) h)) * ENNReal.ofReal (‖(Matrix.of h).det‖ ^ 2)
  have hG : Measurable G := hb.lintegral_prod_right'.mul
    (continuous_detM.norm.measurable.pow_const 2).ennreal_ofReal
  calc _ = ∫⁻ m, G (invM m) * wt m := by
        refine lintegral_congr fun m => ?_
        by_cases hm : (Matrix.of m).det = 0
        · simp only [wt_eq_zero m hm, wt_eq_zero _ ((det_blk _ m).trans hm), mul_zero,
            lintegral_zero]
        · have hw : ∀ r : Fin k → ℂ, wt (blk r m) =
              ENNReal.ofReal (‖(Matrix.of (invM m)).det‖ ^ 2) * wt m := fun r => by
            unfold wt
            rw [det_blk, of_invM, det_nonsing_inv, Ring.inverse_eq_inv', norm_inv, inv_pow _ 2,
              ← ENNReal.ofReal_mul (by positivity), pow_succ']
          simp only [hw, G]
          rw [lintegral_mul_const' _ _ (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
            (show wt m ≠ ⊤ from ENNReal.ofReal_ne_top)), mul_assoc, ← lintegral_neg_eq_self]
          congr 1
          refine lintegral_congr fun T => ?_
          exact congrArg ψ (inv_blk T m hm)
    _ = ∫⁻ h, G h * wt h := lintegral_inv G hG
    _ = _ := by
        refine lintegral_congr fun h => ?_
        rw [lintegral_mul_const' _ _ ENNReal.ofReal_ne_top, ENNReal.ofReal_mul (by positivity),
          ← mul_assoc]
        rfl

theorem haar_first_column : ∀ (k : ℕ), 1 ≤ k → ∃ s : (Fin (k + 1) → ℂ) → Fin (k + 1) → Fin (k + 1) → ℂ, Measurable s ∧ (∀ x, x ≠ 0 → (Matrix.of (s x)).det = 1 ∧ ∀ a, s x a 0 = x a) ∧ ∀ φ : (Fin (k + 1) → Fin (k + 1) → ℂ) → ENNReal, Measurable φ → ∫⁻ g, φ g * ENNReal.ofReal ((‖(Matrix.of g).det‖ ^ 2)⁻¹ ^ (k + 1)) = ∫⁻ x : Fin (k + 1) → ℂ, ∫⁻ h : Fin k → Fin k → ℂ, ∫⁻ T : Fin k → ℂ, φ (fun a b => (Matrix.of (Fin.cons (Fin.cons 1 (T ᵥ* Matrix.of h)) (fun a' => Fin.cons 0 (h a')) : Fin (k + 1) → Fin (k + 1) → ℂ) * (Matrix.of (s x))⁻¹) a b) * ENNReal.ofReal (‖(Matrix.of h).det‖ ^ 2 * (‖(Matrix.of h).det‖ ^ 2)⁻¹ ^ k) := by
  intro k hk
  obtain ⟨s, hsm, hs⟩ := exists_section k hk
  refine ⟨s, hsm, hs, fun φ hφ => ?_⟩
  have hF : Measurable fun y => φ (invM y) * wt y := (hφ.comp measurable_invM).mul measurable_wt
  refine (lintegral_inv φ hφ).symm.trans ((lintegral_first_col _ hF).trans ?_)
  have hae : ∀ᵐ x : Fin (k + 1) → ℂ, x ≠ 0 := by
    rw [ae_iff]
    simp
  refine lintegral_congr_ae (hae.mono fun x hx => ?_)
  obtain ⟨hd, h0⟩ := hs x hx
  have hc : Measurable fun (Y : Fin (k + 1) → Fin k → ℂ) (a : Fin (k + 1)) =>
      (Fin.cons (x a) (Y a) : Fin (k + 1) → ℂ) := by
    refine measurable_pi_lambda _ fun a => measurable_pi_lambda _ fun b => ?_
    refine Fin.cases ?_ (fun b => ?_) b
    · exact measurable_const
    · exact (measurable_pi_apply b).comp (measurable_pi_apply a)
  have hl : Measurable fun (Y : Fin (k + 1) → Fin k → ℂ) (a : Fin (k + 1)) (b : Fin k) =>
      (Matrix.of (s x) * Matrix.of Y) a b := by
    refine Continuous.measurable (continuous_pi fun a => continuous_pi fun b => ?_)
    simp only [Matrix.mul_apply, of_apply]
    fun_prop
  have h1 := lintegral_left (Matrix.of (s x)) (hd ▸ one_ne_zero) _ (hF.comp hc)
  have h2 := lintegral_first_row _ ((hF.comp hc).comp hl)
  have h3 := lintegral_blk_inv (fun g => φ (mulM g (invM (s x))))
    (hφ.comp (measurable_mulM measurable_id' measurable_const))
  rw [hd, norm_one, one_pow, one_pow, ENNReal.ofReal_one, one_mul] at h1
  refine h1.trans (h2.trans (Eq.trans ?_ h3))
  refine lintegral_congr fun m => lintegral_congr fun r => ?_
  have e : (fun a => (Fin.cons (x a) fun b => (Matrix.of (s x) *
      Matrix.of (Fin.cons r m : Fin (k + 1) → Fin k → ℂ)) a b : Fin (k + 1) → ℂ)) =
      mulM (s x) (blk r m) := by
    funext a b
    refine Fin.cases ?_ (fun b => ?_) b
    · simp [mulM, blk, Matrix.mul_apply, Fin.sum_univ_succ, h0]
    · simp [mulM, blk, Matrix.mul_apply, Fin.sum_univ_succ]
  simp only [Function.comp_apply]
  rw [e, wt_mul]
  have hw : wt (s x) = 1 := by simp [wt, hd]
  have hi : invM (mulM (s x) (blk r m)) = mulM (invM (blk r m)) (invM (s x)) := by
    apply Matrix.of.injective
    rw [of_invM, of_mulM, of_mulM, of_invM, of_invM, Matrix.mul_inv_rev]
  rw [hw, one_mul, hi]

end GlobalTheory.GLFirstColumn
