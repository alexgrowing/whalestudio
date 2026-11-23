import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.TiledBoundaries.MemSpanBn
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.TiledBoundaries.TileIntegral

namespace ReciprocityTheory.ChartRestriction.G.I2.TiledBoundaries

open ReciprocityTheory.ChartRestriction.G.I2 MeasureTheory MeasureTheory.Measure Complex Module Set Submodule

noncomputable section

variable {E : Type} [Field E] [NumberField E]

theorem mem_span_map {V : Type} [AddCommGroup V] [Module ℝ V] {ι : Type} (b : Basis ι ℝ V)
    (e : V ≃ₗ[ℝ] V) (x : V) : x ∈ span ℤ (range (b.map e)) ↔ e.symm x ∈ span ℤ (range b) := by
  have h : range (b.map e) = ((e.restrictScalars ℤ : V ≃ₗ[ℤ] V) : V →ₗ[ℤ] V) '' range b := by
    ext y
    simp [Basis.map_apply]
  rw [h, Submodule.span_image, Submodule.mem_map_equiv]
  try rfl

section PiR

def piR (X : PT E) {q : ℕ} {π : Vsp X.dim →ₗ[ℂ] Vsp X.dim} (hq : 1 ≤ q) (hπ : IsPi X q π) : Vsp X.dim ≃ₗ[ℝ] Vsp X.dim :=
  LinearEquiv.ofBijective (π.restrictScalars ℝ) (pi_bij X hq hπ)

theorem piR_apply (X : PT E) {q : ℕ} {π : Vsp X.dim →ₗ[ℂ] Vsp X.dim} (hq : 1 ≤ q) (hπ : IsPi X q π) (v : Vsp X.dim) : piR X hq hπ v = π v := rfl

def bP (X : PT E) {q : ℕ} {π : Vsp X.dim →ₗ[ℂ] Vsp X.dim} (hq : 1 ≤ q) (hπ : IsPi X q π) : Basis (Fin (2 * Fintype.card (Idx X.dim))) ℝ (Vsp X.dim) := X.b.map (piR X hq hπ).symm

theorem mem_P (X : PT E) {q : ℕ} {π : Vsp X.dim →ₗ[ℂ] Vsp X.dim} (hq : 1 ≤ q) (hπ : IsPi X q π) (x : Vsp X.dim) : x ∈ span ℤ (range (bP X hq hπ)) ↔ π x ∈ X.L := by
  unfold bP
  exact (mem_span_map _ _ _).trans Iff.rfl

theorem L_le_P (X : PT E) {q : ℕ} {π : Vsp X.dim →ₗ[ℂ] Vsp X.dim} (hq : 1 ≤ q) (hπ : IsPi X q π) : span ℤ (range X.b) ≤ span ℤ (range (bP X hq hπ)) := fun x hx => (mem_P X hq hπ x).mpr (hπ.2.1 x hx)

theorem fdP (X : PT E) {q : ℕ} {π : Vsp X.dim →ₗ[ℂ] Vsp X.dim} (hq : 1 ≤ q) (hπ : IsPi X q π) : ZSpan.fundamentalDomain (bP X hq hπ) = piR X hq hπ ⁻¹' ZSpan.fundamentalDomain X.b := by
  unfold bP
  rw [← ZSpan.map_fundamentalDomain, LinearEquiv.image_symm_eq_preimage]
  try rfl

theorem norm_pi (X : PT E) {q : ℕ} {π : Vsp X.dim →ₗ[ℂ] Vsp X.dim} (hπ : IsPi X q π) (x : Vsp X.dim) : ‖π x‖ = Real.sqrt q * ‖x‖ := by
  have hn : ∀ v : Vsp X.dim, Hf v v = @inner ℂ _ _ v v := fun v => by
    simp only [Hf, PiLp.inner_apply, RCLike.inner_apply, mul_comm]
  have h := hπ.2.2.1 x x
  rw [hn, hn, inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K] at h
  have h2 : ‖π x‖ ^ 2 = (q : ℝ) * ‖x‖ ^ 2 := by
    have h' : ((‖π x‖ ^ 2 : ℝ) : ℂ) = (((q : ℝ) * ‖x‖ ^ 2 : ℝ) : ℂ) := by push_cast; exact h
    exact Complex.ofReal_injective h'
  rw [← Real.sqrt_sq (norm_nonneg (π x)), h2, Real.sqrt_mul (Nat.cast_nonneg q), Real.sqrt_sq (norm_nonneg x)]

theorem sqrt_q_pos {q : ℕ} (hq : 1 ≤ q) : 0 < Real.sqrt q := Real.sqrt_pos.mpr (Nat.cast_pos.mpr (by omega))

def Ui (X : PT E) {q : ℕ} {π : Vsp X.dim →ₗ[ℂ] Vsp X.dim} (hq : 1 ≤ q) (hπ : IsPi X q π) : Vsp X.dim ≃ₗᵢ[ℝ] Vsp X.dim where
  toLinearEquiv := (piR X hq hπ).trans
    (LinearEquiv.smulOfNeZero ℝ _ (Real.sqrt q)⁻¹ (inv_ne_zero (sqrt_q_pos hq).ne'))
  norm_map' x := by
    show ‖(Real.sqrt q)⁻¹ • π x‖ = ‖x‖
    rw [norm_smul, norm_pi X hπ, Real.norm_eq_abs, abs_inv, abs_of_pos (sqrt_q_pos hq), ← mul_assoc,
      inv_mul_cancel₀ (sqrt_q_pos hq).ne', one_mul]

theorem Ui_apply (X : PT E) {q : ℕ} {π : Vsp X.dim →ₗ[ℂ] Vsp X.dim} (hq : 1 ≤ q) (hπ : IsPi X q π) (x : Vsp X.dim) : Ui X hq hπ x = (Real.sqrt q)⁻¹ • π x := rfl

theorem piR_preimage (X : PT E) {q : ℕ} {π : Vsp X.dim →ₗ[ℂ] Vsp X.dim} (hq : 1 ≤ q) (hπ : IsPi X q π) (S : Set (Vsp X.dim)) :
    piR X hq hπ ⁻¹' S = Ui X hq hπ ⁻¹' ((fun x => Real.sqrt q • x) ⁻¹' S) := by
  ext x
  simp only [Set.mem_preimage, Ui_apply, piR_apply, smul_smul, mul_inv_cancel₀ (sqrt_q_pos hq).ne', one_smul]

theorem finrank_V (X : PT E) : finrank ℝ (Vsp X.dim) = 2 * Fintype.card (Idx X.dim) := by
  rw [Module.finrank_eq_card_basis X.b, Fintype.card_fin]

theorem vol_fdP (X : PT E) {q : ℕ} {π : Vsp X.dim →ₗ[ℂ] Vsp X.dim} (hq : 1 ≤ q) (hπ : IsPi X q π) : volume.real (ZSpan.fundamentalDomain (bP X hq hπ)) =
    ((q : ℝ) ^ Fintype.card (Idx X.dim))⁻¹ * volume.real (ZSpan.fundamentalDomain X.b) := by
  have hmeas : MeasurableSet ((fun x => Real.sqrt q • x) ⁻¹' ZSpan.fundamentalDomain X.b) :=
    (ZSpan.fundamentalDomain_measurableSet X.b).preimage (measurable_const_smul _)
  rw [fdP, piR_preimage, measureReal_def,
    ((Ui X hq hπ).measurePreserving).measure_preimage hmeas.nullMeasurableSet,
    Measure.addHaar_preimage_smul volume (sqrt_q_pos hq).ne', finrank_V, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (abs_nonneg _), measureReal_def]
  congr 1
  rw [abs_inv, pow_mul, Real.sq_sqrt (Nat.cast_nonneg q),
    abs_of_pos (pow_pos (Nat.cast_pos.mpr (by omega)) _)]

end PiR

private theorem setAverage_preimage_linearEquiv_comp (X : PT E) (f : Vsp X.dim ≃ₗ[ℝ] Vsp X.dim) (g : Vsp X.dim → ℝ)
    (hg : Continuous g) (S : Set (Vsp X.dim)) (hS : MeasurableSet S) :
    ⨍ x in f ⁻¹' S, g (f x) ∂(volume : Measure (Vsp X.dim)) = ⨍ x in S, g x ∂volume := by
  have hdet : LinearMap.det (f : Vsp X.dim →ₗ[ℝ] Vsp X.dim) ≠ 0 := (LinearEquiv.isUnit_det' f).ne_zero
  have hmap : Measure.map f volume = ENNReal.ofReal |(LinearMap.det (f : Vsp X.dim →ₗ[ℝ] Vsp X.dim))⁻¹| •
      (volume : Measure (Vsp X.dim)) :=
    Measure.map_linearMap_addHaar_eq_smul_addHaar volume hdet
  have hfm : Measurable f := (LinearMap.continuous_of_finiteDimensional (f : Vsp X.dim →ₗ[ℝ] Vsp X.dim)).measurable
  have h1 : ∫ x in f ⁻¹' S, g (f x) ∂volume = ∫ x in S, g x ∂(Measure.map f volume) :=
    (setIntegral_map hS hg.aestronglyMeasurable hfm.aemeasurable).symm
  have h2 : volume (f ⁻¹' S) = (Measure.map f volume) S := (Measure.map_apply hfm hS).symm
  have hc0 : (ENNReal.ofReal |(LinearMap.det (f : Vsp X.dim →ₗ[ℝ] Vsp X.dim))⁻¹|).toReal ≠ 0 := by
    rw [ENNReal.toReal_ofReal (abs_nonneg _)]
    exact abs_ne_zero.mpr (inv_ne_zero hdet)
  rw [setAverage_eq, setAverage_eq, h1, measureReal_def, h2, hmap, Measure.restrict_smul, integral_smul_measure,
    Measure.smul_apply, smul_eq_mul (α := ENNReal), ENNReal.toReal_mul, ← measureReal_def]
  simp only [smul_eq_mul, mul_inv]
  linear_combination ((volume.real S)⁻¹ * ∫ x in S, g x) * inv_mul_cancel₀ hc0

theorem stepP : StepP := by
  intro E _ _ X q π hq hπ g hg hper
  have hgp : Continuous fun w => g (π w) := hg.comp (LinearMap.continuous_of_finiteDimensional π)
  rw [tile_average (μ := volume) X.b (bP X hq hπ) (L_le_P X hq hπ) (fun w => g (π w)) hgp ?_]
  · rw [fdP]
    exact setAverage_preimage_linearEquiv_comp X (piR X hq hπ) g hg _ (ZSpan.fundamentalDomain_measurableSet X.b)
  · intro β hβ x
    have h1 := (mem_P X hq hπ β).mp hβ
    simp only [map_add]
    exact hper _ h1 _

section Q

theorem q_ne {q : ℕ} (hq : 1 ≤ q) : (q : ℝ) ≠ 0 := by
  exact Nat.cast_ne_zero.mpr (by omega)

def bQ (X : PT E) {q : ℕ} (hq : 1 ≤ q) : Basis (Fin (2 * Fintype.card (Idx X.dim))) ℝ (Vsp X.dim) :=
  X.b.map (LinearEquiv.smulOfNeZero ℝ _ (q : ℝ) (q_ne hq)).symm

theorem mem_Q (X : PT E) {q : ℕ} (hq : 1 ≤ q) (x : Vsp X.dim) : x ∈ span ℤ (range (bQ X hq)) ↔ (q : ℝ) • x ∈ X.L := by
  unfold bQ
  exact (mem_span_map _ _ _).trans Iff.rfl

theorem fdQ (X : PT E) {q : ℕ} (hq : 1 ≤ q) : ZSpan.fundamentalDomain (bQ X hq) =
    (fun x => (q : ℝ) • x) ⁻¹' ZSpan.fundamentalDomain X.b := by
  unfold bQ
  rw [← ZSpan.map_fundamentalDomain, LinearEquiv.image_symm_eq_preimage]
  try rfl

theorem vol_fdQ (X : PT E) {q : ℕ} (hq : 1 ≤ q) : volume.real (ZSpan.fundamentalDomain (bQ X hq)) =
    (((q : ℝ) ^ Fintype.card (Idx X.dim)) ^ 2)⁻¹ * volume.real (ZSpan.fundamentalDomain X.b) := by
  rw [fdQ, measureReal_def, Measure.addHaar_preimage_smul volume (q_ne hq), finrank_V, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (abs_nonneg _), measureReal_def]
  congr 1
  rw [abs_inv, abs_of_pos (pow_pos (Nat.cast_pos.mpr (by omega)) _)]
  ring

end Q

theorem P_le_Q (X : PT E) {q : ℕ} {π : Vsp X.dim →ₗ[ℂ] Vsp X.dim} (hq : 1 ≤ q) (hπ : IsPi X q π) :
    span ℤ (range (bP X hq hπ)) ≤ span ℤ (range (bQ X hq)) := by
  intro x hx
  rw [mem_P] at hx
  rw [mem_Q]
  have hH : ∀ a c : Vsp X.dim, Hf a c = @inner ℂ _ _ c a := fun a c => by
    simp only [Hf, PiLp.inner_apply, RCLike.inner_apply, mul_comm]
  have hround : ∀ y : Vsp X.dim, y ∈ X.L →
      ((round (Hf (π x) (π y)).im : ℤ) : ℝ) = (Hf (π x) (π y)).im := by
    intro y hy
    obtain ⟨k, hk⟩ := X.integral _ _ hx (hπ.2.1 y hy)
    rw [hk, round_intCast]
  have hadd : ∀ y1 y2 : Vsp X.dim,
      (Hf (π x) (π (y1 + y2))).im = (Hf (π x) (π y1)).im + (Hf (π x) (π y2)).im := by
    intro y1 y2
    rw [hH, hH, hH, map_add, inner_add_left, Complex.add_im]
  let φ : X.L →+ ℤ :=
    { toFun := fun y => round (Hf (π x) (π y)).im
      map_zero' := by simp [hH]
      map_add' := fun y1 y2 => by
        apply Int.cast_injective (α := ℝ)
        simp only [Submodule.coe_add, Int.cast_add]
        rw [hround _ (X.L.add_mem y1.2 y2.2), hround _ y1.2, hround _ y2.2]
        exact hadd _ _ }
  obtain ⟨w, hwL, hw⟩ := X.perfect φ
  have hLu : ∀ y ∈ X.L, (@inner ℂ _ _ y (w - (q : ℝ) • x)).im = 0 := by
    intro y hy
    have h1 := hw ⟨y, hy⟩
    have h2 := hπ.2.2.1 x y
    simp only [φ, AddMonoidHom.coe_mk, ZeroHom.coe_mk] at h1
    rw [hround _ hy, h2, hH, hH] at h1
    rw [inner_sub_right, ← Complex.coe_smul, inner_smul_right, Complex.sub_im, ← h1]
    simp
  let Lf : Vsp X.dim →ₗ[ℝ] ℝ := Complex.imLm.comp ((innerₛₗ ℂ (w - (q : ℝ) • x)).restrictScalars ℝ)
  have hLf : Lf = 0 := X.b.ext fun i => by
    have h := hLu _ (Submodule.subset_span (Set.mem_range_self i))
    rw [← inner_conj_symm, Complex.conj_im, neg_eq_zero] at h
    simpa [Lf, inner_sub_left] using h
  have hall : ∀ y, (@inner ℂ _ _ (w - (q : ℝ) • x) y).im = 0 := fun y => by
    exact LinearMap.congr_fun hLf y
  have hu0 : w - (q : ℝ) • x = 0 := by
    have h1 := hall (Complex.I • (w - (q : ℝ) • x))
    rw [inner_smul_right] at h1
    simp only [Complex.mul_im, Complex.I_re, Complex.I_im, zero_mul, one_mul, zero_add] at h1
    have h2 : ‖w - (q : ℝ) • x‖ ^ 2 = 0 := by
      rw [← inner_self_eq_norm_sq (𝕜 := ℂ)]
      exact h1
    exact norm_eq_zero.mp (pow_eq_zero_iff (by norm_num) |>.mp h2)
  rw [← sub_eq_zero.mp hu0]
  exact hwL

theorem stepK : StepK := by
  intro E _ _ X q n π hq hπ K hK
  have hq0 : (q : ℝ) ≠ 0 := q_ne hq
  have hQ : (0 : ℝ) < (q : ℝ) ^ Fintype.card (Idx X.dim) := pow_pos (Nat.cast_pos.mpr (by omega)) _
  have hQ' : (q : ℝ) ^ Fintype.card (Idx X.dim) ≠ 0 := hQ.ne'
  have hV : 0 < volume.real (ZSpan.fundamentalDomain X.b) := by
    rw [measureReal_def]
    exact ENNReal.toReal_pos (ZSpan.measure_fundamentalDomain_ne_zero X.b)
      (ZSpan.fundamentalDomain_isBounded X.b).measure_lt_top.ne
  have ht := tile_measure (μ := volume) (bP X hq hπ) (bQ X hq) (P_le_Q X hq hπ)
  rw [vol_fdP, vol_fdQ] at ht
  have hcR : ((reps (bP X hq hπ) (bQ X hq)).card : ℝ) = (q : ℝ) ^ Fintype.card (Idx X.dim) := by
    have h3 : ((reps (bP X hq hπ) (bQ X hq)).card : ℝ) *
        ((((q : ℝ) ^ Fintype.card (Idx X.dim)) ^ 2)⁻¹ * volume.real (ZSpan.fundamentalDomain X.b)) =
        ((q : ℝ) ^ Fintype.card (Idx X.dim)) *
        ((((q : ℝ) ^ Fintype.card (Idx X.dim)) ^ 2)⁻¹ * volume.real (ZSpan.fundamentalDomain X.b)) := by
      rw [← ht]
      field_simp
      try ring
    exact mul_right_cancel₀ (mul_pos (inv_pos.mpr (pow_pos hQ 2)) hV).ne' h3
  have hcR' : (reps (bP X hq hπ) (bQ X hq)).card = q ^ Fintype.card (Idx X.dim) := by exact_mod_cast hcR
  have hmemQ : ∀ c ∈ reps (bP X hq hπ) (bQ X hq), (q : ℂ) • c ∈ X.L := by
    intro c hc
    have h1 := (mem_Q X hq c).mp (mem_reps.mp hc).2
    rwa [Nat.cast_smul_eq_nsmul ℝ, ← Nat.cast_smul_eq_nsmul ℂ] at h1
  classical
  let T := Fintype.piFinset (fun _ : Fin n => reps (bP X hq hπ) (bQ X hq))
  have hT : ∀ c ∈ T, ∀ k, (q : ℂ) • c k ∈ X.L := fun c hc k =>
    hmemQ _ (Fintype.mem_piFinset.mp hc k)
  let f : (Fin n → Vsp X.dim) → (Fin n → Vsp X.dim) := fun c =>
    if h : ∀ k, (q : ℂ) • c k ∈ X.L then Classical.choose (hK.2 c h).exists else 0
  have hf : ∀ c ∈ T, f c ∈ K ∧ ∀ k, π (c k - f c k) ∈ X.L := by
    intro c hc
    have h := hT c hc
    simp only [f, dif_pos h]
    exact Classical.choose_spec (hK.2 c h).exists
  have hcard : T.card ≤ K.card := by
    apply Finset.card_le_card_of_injOn f
    · intro c hc
      have hc' : c ∈ T := by first | exact hc | exact Finset.mem_coe.mp hc
      exact (hf c hc').1
    · intro c1 hc1 c2 hc2 heq
      have hc1' : c1 ∈ T := by first | exact hc1 | exact Finset.mem_coe.mp hc1
      have hc2' : c2 ∈ T := by first | exact hc2 | exact Finset.mem_coe.mp hc2
      funext k
      have e1 := (hf c1 hc1').2 k
      have e2 := (hf c2 hc2').2 k
      rw [heq] at e1
      have e3 : π (c1 k - c2 k) ∈ X.L := by
        have h4 := X.L.sub_mem e1 e2
        rwa [← map_sub, sub_sub_sub_cancel_right] at h4
      have hP := (mem_P X hq hπ _).mpr e3
      have hc1k := (mem_reps.mp (Fintype.mem_piFinset.mp hc1' k)).1
      have hc2k := (mem_reps.mp (Fintype.mem_piFinset.mp hc2' k)).1
      have h5 := fd_uniq (bP X hq hπ) (x := c2 k) hP (Submodule.zero_mem _)
        (by rw [sub_add_cancel]; exact hc1k) (by rw [zero_add]; exact hc2k)
      exact sub_eq_zero.mp h5
  have hTc : T.card = q ^ (Fintype.card (Idx X.dim) * n) := by
    simp only [T, Fintype.card_piFinset, Finset.prod_const, Finset.card_univ, Fintype.card_fin, hcR', pow_mul]
  rw [← hTc]
  exact hcard

end

end ReciprocityTheory.ChartRestriction.G.I2.TiledBoundaries
