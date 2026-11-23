import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SecondCountableHermC
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TupCoordApply
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousSeminormDiffSLe
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DetConjUnitary
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.PiDens

open MeasureTheory
open GlobalTheory.CompanionTheory.SiegelND.Integ.Arch
open scoped ComplexOrder
noncomputable section
namespace GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.Bound

theorem exists_schwartz_coord : ∀ (W : Type) [Fintype W] (n M N : ℕ) (e : (W → Fin n → Fin M → ℂ) ≃+ (Fin N → ℝ)),
    Continuous e → Continuous e.symm → ∀ f : SchwartzMap (Fin N → ℝ) ℂ,
    ∃ g : SchwartzMap (TupV W n M) ℂ, ∀ x, g x = f (e (tupCoord x)) := by
  intro W _ n M N e he he' f
  refine ⟨SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (tupCoord.trans (e.toRealLinearEquiv he he')) f,
    fun x => rfl⟩

theorem integral_eq_coord : ∀ (W : Type) [Fintype W] (n M : ℕ) (μ : Measure (W → Fin n → Fin M → ℂ)),
    μ.IsAddHaarMeasure → ∃ c : ℝ, 0 ≤ c ∧ ∀ F : (W → Fin n → Fin M → ℂ) → ℂ,
    ∫ X, F X ∂μ = (c : ℂ) * ∫ x : TupV W n M, F (tupCoord x) := by
  intro W _ n M μ hμ
  have hν : (Measure.map tupCoord (volume : Measure (TupV W n M))).IsAddHaarMeasure :=
    tupCoord.isAddHaarMeasure_map _
  obtain ⟨c, hc⟩ : ∃ c : NNReal, μ = c • Measure.map tupCoord (volume : Measure (TupV W n M)) :=
    ⟨_, Measure.isAddLeftInvariant_eq_smul μ (Measure.map tupCoord (volume : Measure (TupV W n M)))⟩
  refine ⟨(c : ℝ), NNReal.coe_nonneg _, fun F => ?_⟩
  have hemb : MeasurableEmbedding (tupCoord : TupV W n M → (W → Fin n → Fin M → ℂ)) :=
    tupCoord.toHomeomorph.measurableEmbedding
  rw [hc, integral_smul_nnreal_measure, hemb.integral_map, NNReal.smul_def, Complex.real_smul]

private theorem two_mul_sum_quarter_inv_mul_two_mul_sum_eq {M : ℕ} (A : Matrix (Fin M) (Fin M) ℂ) (hA : A.det ≠ 0)
    (v : Fin M → ℂ) (p : Fin M) :
    (2 : ℂ) * ∑ j, ((4 : ℂ)⁻¹ • A⁻¹) p j * ((2 : ℂ) * ∑ l, A j l * v l) = v p := by
  have h1 : ∑ j, A⁻¹ p j * ∑ l, A j l * v l = v p := by
    have h := congrFun (Matrix.mulVec_mulVec v A⁻¹ A) p
    rw [Matrix.nonsing_inv_mul A (isUnit_iff_ne_zero.mpr hA), Matrix.one_mulVec] at h
    simpa [Matrix.mulVec, dotProduct] using h
  calc (2 : ℂ) * ∑ j, ((4 : ℂ)⁻¹ • A⁻¹) p j * ((2 : ℂ) * ∑ l, A j l * v l)
      = ∑ j, A⁻¹ p j * ∑ l, A j l * v l := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [Matrix.smul_apply, smul_eq_mul]
        ring
    _ = v p := h1

theorem norm_diag_le_polar : ∀ (W : Type) [Fintype W] (n M : ℕ) (J : W → Matrix (Fin M) (Fin M) ℂ),
    (∀ w, (J w).det ≠ 0) → ∃ C : ℝ, 1 ≤ C ∧ ∀ (b : W → Matrix (Fin n) (Fin n) ℂ) (y : TupV W n M)
      (k : W × Fin M), ‖Matrix.toEuclideanLin (b k.1).transpose (y k)‖ ≤ C * ‖polarOp J b y‖ := by
  intro W _ n M J hJ
  have hinv : ∀ z : TupV W n M,
      mixOp (fun w => (4 : ℂ)⁻¹ • (J w)⁻¹) (mixOp J z) = z := by
    intro z
    ext k a
    obtain ⟨w, p⟩ := k
    simp only [mixOp_apply]
    simp
    exact two_mul_sum_quarter_inv_mul_two_mul_sum_eq (J w) (hJ w) (fun l => z (w, l) a) p
  let T : TupV W n M →L[ℝ] TupV W n M :=
    LinearMap.toContinuousLinearMap ((mixOp (fun w => (4 : ℂ)⁻¹ • (J w)⁻¹)).restrictScalars ℝ)
  refine ⟨max 1 ‖T‖, le_max_left _ _, fun b y k => ?_⟩
  rw [← diagOp_apply]
  calc ‖diagOp b y k‖ ≤ ‖diagOp b y‖ := PiLp.norm_apply_le _ _
    _ = ‖T (polarOp J b y)‖ := by
        rw [polarOp_apply]
        simp only [T, LinearMap.coe_toContinuousLinearMap', LinearMap.coe_restrictScalars, hinv]
    _ ≤ ‖T‖ * ‖polarOp J b y‖ := T.le_opNorm _
    _ ≤ max 1 ‖T‖ * ‖polarOp J b y‖ :=
        mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg _)

theorem lintegral_prod_le : ∀ (W : Type) [Fintype W] (n M : ℕ), ∃ C : ℝ, 0 ≤ C ∧
    ∀ h : W × Fin M → EuclideanSpace ℂ (Fin n) → ENNReal, (∀ k, Measurable (h k)) →
    ∫⁻ y : TupV W n M, ∏ k, h k (y k) ≤ ENNReal.ofReal C * ∏ k, ∫⁻ z, h k z := by
  intro W _ n M
  let L := PiLp.continuousLinearEquiv 2 ℝ (fun _ : W × Fin M => EuclideanSpace ℂ (Fin n))
  have hν : (Measure.map L (volume : Measure (TupV W n M))).IsAddHaarMeasure :=
    L.isAddHaarMeasure_map _
  have hπ : (Measure.pi fun _ : W × Fin M => (volume : Measure (EuclideanSpace ℂ (Fin n)))).IsAddHaarMeasure := by
    haveI : ∀ _ : W × Fin M, (volume : Measure (EuclideanSpace ℂ (Fin n))).IsAddHaarMeasure :=
      fun _ => inferInstance
    haveI : MeasurableAdd (EuclideanSpace ℂ (Fin n)) := inferInstance
    first
      | exact Measure.pi.isAddHaarMeasure _
      | exact Measure.pi.isAddHaarMeasure
      | exact @Measure.pi.isAddHaarMeasure (W × Fin M) _ (fun _ => EuclideanSpace ℂ (Fin n)) _
          (fun _ => volume) _ _ _ _ _
  have hνπ := Measure.isAddLeftInvariant_eq_smul (Measure.map L (volume : Measure (TupV W n M)))
    (Measure.pi fun _ : W × Fin M => (volume : Measure (EuclideanSpace ℂ (Fin n))))
  refine ⟨(Measure.addHaarScalarFactor (Measure.map L (volume : Measure (TupV W n M)))
    (Measure.pi fun _ : W × Fin M => (volume : Measure (EuclideanSpace ℂ (Fin n)))) : ℝ),
    NNReal.coe_nonneg _, fun h hh => le_of_eq ?_⟩
  have hm : Measurable fun Y : W × Fin M → EuclideanSpace ℂ (Fin n) => ∏ k, h k (Y k) :=
    Finset.measurable_prod _ fun k _ => (hh k).comp (measurable_pi_apply k)
  have hmap := lintegral_map hm L.continuous.measurable (μ := (volume : Measure (TupV W n M)))
  rw [hνπ] at hmap
  rw [lintegral_smul_measure, PI.AprimeInfG.lintegral_fintype_prod h hh] at hmap
  rw [ENNReal.ofReal_coe_nnreal]
  exact hmap.symm.trans (by rw [ENNReal.smul_def, smul_eq_mul])

theorem sum_four_swap_pairs_alt {α β : Type} [Fintype α] [Fintype β] (t : α → β → α → β → ℂ) :
    ∑ i, ∑ c, ∑ j, ∑ a, t i c j a = ∑ j, ∑ a, ∑ i, ∑ c, t i c j a := by
  calc ∑ i, ∑ c, ∑ j, ∑ a, t i c j a = ∑ i, ∑ j, ∑ c, ∑ a, t i c j a :=
        Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = ∑ j, ∑ i, ∑ c, ∑ a, t i c j a := Finset.sum_comm
    _ = ∑ j, ∑ i, ∑ a, ∑ c, t i c j a :=
        Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = ∑ j, ∑ a, ∑ i, ∑ c, t i c j a := Finset.sum_congr rfl fun _ _ => Finset.sum_comm

def sesq {n M : ℕ} (J : Matrix (Fin M) (Fin M) ℂ) (b : Matrix (Fin n) (Fin n) ℂ)
    (X Y : Fin n → Fin M → ℂ) : ℂ :=
  ∑ i, ∑ c, ∑ j, ∑ a, (starRingEnd ℂ) (X c i) * J i j * b a c * Y a j

theorem trace_gram {n M : ℕ} (J : Matrix (Fin M) (Fin M) ℂ) (b : Matrix (Fin n) (Fin n) ℂ)
    (X : Fin n → Fin M → ℂ) : Matrix.trace (b * gramC J X) = sesq J b X X := by
  have h : Matrix.trace (b * gramC J X) =
      ∑ a, ∑ c, ∑ i, ∑ j, b a c * ((starRingEnd ℂ) (X c i) * J i j * X a j) := by
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, gramC, Finset.mul_sum]
  rw [h]
  unfold sesq
  calc ∑ a, ∑ c, ∑ i, ∑ j, b a c * ((starRingEnd ℂ) (X c i) * J i j * X a j)
      = ∑ c, ∑ a, ∑ i, ∑ j, b a c * ((starRingEnd ℂ) (X c i) * J i j * X a j) := Finset.sum_comm
    _ = ∑ c, ∑ i, ∑ a, ∑ j, b a c * ((starRingEnd ℂ) (X c i) * J i j * X a j) :=
        Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = ∑ i, ∑ c, ∑ a, ∑ j, b a c * ((starRingEnd ℂ) (X c i) * J i j * X a j) := Finset.sum_comm
    _ = ∑ i, ∑ c, ∑ j, ∑ a, b a c * ((starRingEnd ℂ) (X c i) * J i j * X a j) :=
        Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = _ := Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
        Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

theorem sesq_add_left {n M : ℕ} (J : Matrix (Fin M) (Fin M) ℂ) (b : Matrix (Fin n) (Fin n) ℂ)
    (X X' Y : Fin n → Fin M → ℂ) : sesq J b (X + X') Y = sesq J b X Y + sesq J b X' Y := by
  simp only [sesq, Pi.add_apply, map_add, add_mul, Finset.sum_add_distrib]

theorem sesq_add_right {n M : ℕ} (J : Matrix (Fin M) (Fin M) ℂ) (b : Matrix (Fin n) (Fin n) ℂ)
    (X Y Y' : Fin n → Fin M → ℂ) : sesq J b X (Y + Y') = sesq J b X Y + sesq J b X Y' := by
  simp only [sesq, Pi.add_apply, mul_add, Finset.sum_add_distrib]

theorem sesq_conj {n M : ℕ} {J : Matrix (Fin M) (Fin M) ℂ} {b : Matrix (Fin n) (Fin n) ℂ}
    (hJ : J.IsHermitian) (hb : b.IsHermitian) (X Y : Fin n → Fin M → ℂ) :
    (starRingEnd ℂ) (sesq J b Y X) = sesq J b X Y := by
  have hJ' : ∀ i j, (starRingEnd ℂ) (J i j) = J j i := fun i j => by
    rw [starRingEnd_apply]; exact hJ.apply j i
  have hb' : ∀ i j, (starRingEnd ℂ) (b i j) = b j i := fun i j => by
    rw [starRingEnd_apply]; exact hb.apply j i
  simp only [sesq, map_sum, map_mul, Complex.conj_conj, hJ', hb']
  refine Eq.trans ?_ (sum_four_swap_pairs_alt _).symm
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
    Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

theorem sesq_re_add {n M : ℕ} {J : Matrix (Fin M) (Fin M) ℂ} {b : Matrix (Fin n) (Fin n) ℂ}
    (hJ : J.IsHermitian) (hb : b.IsHermitian) (X Y : Fin n → Fin M → ℂ) :
    (sesq J b (X + Y) (X + Y)).re =
      (sesq J b X X).re + (sesq J b Y Y).re + 2 * (sesq J b X Y).re := by
  rw [sesq_add_left, sesq_add_right, sesq_add_right]
  have h := congrArg Complex.re (sesq_conj hJ hb X Y)
  rw [Complex.conj_re] at h
  simp only [Complex.add_re]
  rw [h]
  ring

theorem inner_polarOp {W : Type} [Fintype W] {n M : ℕ} (J : W → Matrix (Fin M) (Fin M) ℂ)
    (b : W → Matrix (Fin n) (Fin n) ℂ) (x y : TupV W n M) :
    inner ℝ x (polarOp J b y) =
      ∑ w, 2 * (sesq (J w) (b w) (tupCoord x w) (tupCoord y w)).re := by
  rw [polarOp_apply, PiLp.inner_apply, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun w _ => ?_
  have hre : ∀ u v : EuclideanSpace ℂ (Fin n), inner ℝ u v = RCLike.re (inner ℂ u v) := by
    intro u v
    first
      | rfl
      | (simp only [PiLp.inner_apply, map_sum]
         exact Finset.sum_congr rfl fun a _ => by first | rfl | exact Complex.real_inner_eq_re_inner _ _)
  have key : ∑ p, inner ℂ (x (w, p)) (mixOp J (diagOp b y) (w, p)) =
      2 * sesq (J w) (b w) (tupCoord x w) (tupCoord y w) := by
    simp only [PiLp.inner_apply, mixOp_apply, diagOp_apply, tupCoord_apply]
    simp [sesq, Matrix.toEuclideanLin_apply, Matrix.mulVec, dotProduct, Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
      Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  calc ∑ p, inner ℝ (x (w, p)) (mixOp J (diagOp b y) (w, p))
      = ∑ p, RCLike.re (inner ℂ (x (w, p)) (mixOp J (diagOp b y) (w, p))) :=
        Finset.sum_congr rfl fun p _ => hre _ _
    _ = RCLike.re (∑ p, inner ℂ (x (w, p)) (mixOp J (diagOp b y) (w, p))) := (map_sum _ _ _).symm
    _ = 2 * (sesq (J w) (b w) (tupCoord x w) (tupCoord y w)).re := by rw [key]; simp

theorem phase_polar : ∀ (W : Type) [Fintype W] (n M : ℕ) (J : W → Matrix (Fin M) (Fin M) ℂ),
    (∀ w, (J w).IsHermitian) → ∀ b : W → Matrix (Fin n) (Fin n) ℂ, (∀ w, (b w).IsHermitian) →
    ∀ x y : TupV W n M, phaseM J b (tupCoord (x + y)) =
      phaseM J b (tupCoord x) + phaseM J b (tupCoord y) + inner ℝ x (polarOp J b y) := by
  intro W _ n M J hJ b hb x y
  simp only [phaseM, trace_gram, map_add, Pi.add_apply, inner_polarOp]
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun w _ => sesq_re_add (hJ w) (hb w) _ _

theorem continuous_phase {W : Type} [Fintype W] {n M : ℕ} (J : W → Matrix (Fin M) (Fin M) ℂ)
    (b : W → Matrix (Fin n) (Fin n) ℂ) :
    Continuous fun x : TupV W n M => phaseM J b (tupCoord x) := by
  have h : Continuous (fun X : W → Fin n → Fin M → ℂ => phaseM J b X) := by
    simp only [phaseM, trace_gram, sesq]
    refine continuous_finsetSum _ fun w _ => Complex.continuous_re.comp ?_
    fun_prop
  exact h.comp tupCoord.continuous

theorem detW_transpose {n : ℕ} (b : Matrix (Fin n) (Fin n) ℂ) : detW b.transpose = detW b := by
  unfold detW
  rw [show (1 : Matrix (Fin n) (Fin n) ℂ) + b.transpose * b.transpose = (1 + b * b).transpose by
    rw [Matrix.transpose_add, Matrix.transpose_one, Matrix.transpose_mul], Matrix.det_transpose]

theorem detW_pos {n : ℕ} {b : Matrix (Fin n) (Fin n) ℂ} (hb : b.IsHermitian) : 0 < detW b := by
  rw [Vol.detW_eq hb]
  exact Finset.prod_pos fun i _ => by positivity

theorem weight_le (κ : Type) [Fintype κ] (L : ℕ) (C r s : ℝ) (u v : κ → ℝ) (hC : 1 ≤ C)
    (hr : 0 ≤ r) (hs : 0 ≤ s) (hu : ∀ k, 0 ≤ u k) (hv : ∀ k, 0 ≤ v k) (hur : ∀ k, u k ≤ r)
    (hvs : ∀ k, v k ≤ C * s) :
    ((1 + r) ^ (Fintype.card κ * L))⁻¹ * ((1 + s) ^ (Fintype.card κ * L))⁻¹ ≤
      (C ^ L) ^ Fintype.card κ * ∏ k, (((1 + u k) ^ L)⁻¹ * ((1 + v k) ^ L)⁻¹) := by
  have hr1 : 0 < 1 + r := by linarith
  have hs1 : 0 < 1 + s := by linarith
  have hC0 : 0 < C := by linarith
  have hD : C ^ L ≠ 0 := pow_ne_zero _ hC0.ne'
  have key : ∀ k, ((1 + r) ^ L)⁻¹ * ((C ^ L)⁻¹ * ((1 + s) ^ L)⁻¹) ≤
      ((1 + u k) ^ L)⁻¹ * ((1 + v k) ^ L)⁻¹ := by
    intro k
    have hu1 : 0 < 1 + u k := by linarith [hu k]
    have hv1 : 0 < 1 + v k := by linarith [hv k]
    have h1 : ((1 + r) ^ L)⁻¹ ≤ ((1 + u k) ^ L)⁻¹ := by
      apply inv_anti₀ (pow_pos hu1 L)
      exact pow_le_pow_left₀ hu1.le (by linarith [hur k]) L
    have h2 : (C ^ L)⁻¹ * ((1 + s) ^ L)⁻¹ ≤ ((1 + v k) ^ L)⁻¹ := by
      rw [← mul_inv, ← mul_pow]
      apply inv_anti₀ (pow_pos hv1 L)
      apply pow_le_pow_left₀ hv1.le
      nlinarith [hvs k]
    exact mul_le_mul h1 h2 (mul_nonneg (inv_nonneg.mpr (pow_nonneg hC0.le L))
      (inv_nonneg.mpr (pow_nonneg hs1.le L))) (inv_nonneg.mpr (pow_nonneg hu1.le L))
  calc ((1 + r) ^ (Fintype.card κ * L))⁻¹ * ((1 + s) ^ (Fintype.card κ * L))⁻¹
      = (C ^ L) ^ Fintype.card κ *
          ∏ _k : κ, (((1 + r) ^ L)⁻¹ * ((C ^ L)⁻¹ * ((1 + s) ^ L)⁻¹)) := by
        rw [Finset.prod_const, Finset.card_univ,
          show ((1 + r) ^ L)⁻¹ * ((C ^ L)⁻¹ * ((1 + s) ^ L)⁻¹) =
            (C ^ L)⁻¹ * (((1 + r) ^ L)⁻¹ * ((1 + s) ^ L)⁻¹) by ring,
          mul_pow, ← mul_assoc, ← mul_pow, mul_inv_cancel₀ hD, one_pow, one_mul, mul_pow,
          inv_pow, inv_pow, ← pow_mul, ← pow_mul, mul_comm L]
    _ ≤ (C ^ L) ^ Fintype.card κ * ∏ k, (((1 + u k) ^ L)⁻¹ * ((1 + v k) ^ L)⁻¹) := by
        apply mul_le_mul_of_nonneg_left _ (pow_nonneg (pow_nonneg hC0.le L) _)
        exact Finset.prod_le_prod (fun k _ => mul_nonneg (inv_nonneg.mpr (pow_nonneg hr1.le L))
          (mul_nonneg (inv_nonneg.mpr (pow_nonneg hC0.le L)) (inv_nonneg.mpr (pow_nonneg hs1.le L))))
          (fun k _ => key k)

theorem sq_prod_rpow {W : Type} [Fintype W] (M : ℕ) (D : W → ℝ) (hD : ∀ w, 0 < D w) :
    (∏ w, D w ^ (-(M : ℝ) / 2)) ^ 2 = ∏ w, ((D w)⁻¹) ^ M := by
  rw [← Finset.prod_pow]
  apply Finset.prod_congr rfl
  intro w _
  have h0 := (hD w).le
  rw [← Real.rpow_mul_natCast h0, show (-(M : ℝ) / 2 * ((2 : ℕ) : ℝ)) = -(M : ℝ) by push_cast; ring,
    Real.rpow_neg h0, Real.rpow_natCast, inv_pow]

private theorem coreC_comp_eq_integral_tupCoord_phase {W : Type} [Fintype W] {n M N : ℕ} (J : W → Matrix (Fin M) (Fin M) ℂ)
    (μ : Measure (W → Fin n → Fin M → ℂ)) (e : (W → Fin n → Fin M → ℂ) ≃+ (Fin N → ℝ))
    (f : SchwartzMap (Fin N → ℝ) ℂ) (g : SchwartzMap (TupV W n M) ℂ)
    (hg : ∀ x, g x = f (e (tupCoord x))) (c : ℝ)
    (hc : ∀ F : (W → Fin n → Fin M → ℂ) → ℂ, ∫ X, F X ∂μ = (c : ℂ) * ∫ x : TupV W n M, F (tupCoord x))
    (b : W → hermC n) :
    coreC J μ (fun X => f (e X)) b = (c : ℂ) * ∫ x, g x * Complex.exp (2 * Real.pi * Complex.I *
      ((phaseM J (fun w => (b w : Matrix (Fin n) (Fin n) ℂ)) (tupCoord x) : ℝ) : ℂ)) := by
  unfold coreC
  rw [hc]
  simp only [hg]

theorem core_bound : ∀ (W : Type) [Fintype W] (n M : ℕ) (J : W → Matrix (Fin M) (Fin M) ℂ), (∀ w, (J w).IsHermitian) → (∀ w, (J w).det ≠ 0) →
  ∀ (N : ℕ) (e : (W → Fin n → Fin M → ℂ) ≃+ (Fin N → ℝ)), Continuous e → Continuous e.symm →
  ∀ (f : SchwartzMap (Fin N → ℝ) ℂ) (μ : Measure (W → Fin n → Fin M → ℂ)), μ.IsAddHaarMeasure →
  ∃ C : ℝ, ∀ b : W → hermC n, ‖coreC J μ (fun X => f (e X)) b‖ ≤
    C * ∏ w, detW (b w : Matrix (Fin n) (Fin n) ℂ) ^ (-(M : ℝ) / 2) := by
  intro W _ n M J hJ hJd N e he he' f μ hμ
  obtain ⟨c, hc0, hc⟩ := integral_eq_coord W n M μ hμ
  obtain ⟨g, hg⟩ := exists_schwartz_coord W n M N e he he' f
  obtain ⟨C2, hC2, hdiag⟩ := norm_diag_le_polar W n M J hJd
  obtain ⟨C3, hC3, hprod⟩ := lintegral_prod_le W n M
  obtain ⟨C1, hC1, hweyl⟩ :=
    Weyl.weyl_differencing (TupV W n M) g (Fintype.card (W × Fin M) * (3 * n))
  obtain ⟨C4, hC4, hvol⟩ :=
    Vol.volume_bound n (3 * n) le_rfl (volume : Measure (EuclideanSpace ℂ (Fin n))) inferInstance
  have hA0 : 0 ≤ (C2 ^ (3 * n)) ^ Fintype.card (W × Fin M) :=
    pow_nonneg (pow_nonneg (by linarith) _) _
  have hK0 : 0 ≤ C1 * (C2 ^ (3 * n)) ^ Fintype.card (W × Fin M) * C3 * C4 ^ Fintype.card (W × Fin M) :=
    mul_nonneg (mul_nonneg (mul_nonneg hC1 hA0) hC3) (pow_nonneg hC4 _)
  refine ⟨c * Real.sqrt (C1 * (C2 ^ (3 * n)) ^ Fintype.card (W × Fin M) * C3 *
    C4 ^ Fintype.card (W × Fin M)), fun b => ?_⟩
  have hB : ∀ w, (b w : Matrix (Fin n) (Fin n) ℂ).IsHermitian := fun w => mem_hermC.mp (b w).2
  have hd : ∀ w, 0 < detW (b w : Matrix (Fin n) (Fin n) ℂ) := fun w => detW_pos (hB w)
  have hcore := coreC_comp_eq_integral_tupCoord_phase J μ e f g hg c hc b
  have hhm : ∀ k : W × Fin M, Measurable fun z : EuclideanSpace ℂ (Fin n) =>
      ENNReal.ofReal (((1 + ‖z‖) ^ (3 * n))⁻¹ *
        ((1 + ‖Matrix.toEuclideanLin (b k.1 : Matrix (Fin n) (Fin n) ℂ).transpose z‖) ^ (3 * n))⁻¹) := by
    intro k
    have hlin : Continuous (Matrix.toEuclideanLin (b k.1 : Matrix (Fin n) (Fin n) ℂ).transpose) :=
      LinearMap.continuous_of_finiteDimensional _
    fun_prop
  have hpt : ∀ y : TupV W n M,
      ENNReal.ofReal (((1 + ‖y‖) ^ (Fintype.card (W × Fin M) * (3 * n)))⁻¹ *
        ((1 + ‖polarOp J (fun w => (b w : Matrix (Fin n) (Fin n) ℂ)) y‖) ^
          (Fintype.card (W × Fin M) * (3 * n)))⁻¹) ≤
      ENNReal.ofReal ((C2 ^ (3 * n)) ^ Fintype.card (W × Fin M)) *
        ∏ k, ENNReal.ofReal (((1 + ‖y k‖) ^ (3 * n))⁻¹ *
          ((1 + ‖Matrix.toEuclideanLin (b k.1 : Matrix (Fin n) (Fin n) ℂ).transpose (y k)‖) ^
            (3 * n))⁻¹) := by
    intro y
    have hwl := weight_le (W × Fin M) (3 * n) C2 ‖y‖
      ‖polarOp J (fun w => (b w : Matrix (Fin n) (Fin n) ℂ)) y‖ (fun k => ‖y k‖)
      (fun k => ‖Matrix.toEuclideanLin (b k.1 : Matrix (Fin n) (Fin n) ℂ).transpose (y k)‖) hC2
      (norm_nonneg _) (norm_nonneg _) (fun _ => norm_nonneg _) (fun _ => norm_nonneg _)
      (fun k => PiLp.norm_apply_le y k) (fun k => hdiag (fun w => (b w : Matrix (Fin n) (Fin n) ℂ)) y k)
    rw [← ENNReal.ofReal_prod_of_nonneg (fun k _ => by positivity), ← ENNReal.ofReal_mul hA0]
    exact ENNReal.ofReal_le_ofReal hwl
  have hkv : ∀ k : W × Fin M, ∫⁻ z : EuclideanSpace ℂ (Fin n),
      ENNReal.ofReal (((1 + ‖z‖) ^ (3 * n))⁻¹ *
        ((1 + ‖Matrix.toEuclideanLin (b k.1 : Matrix (Fin n) (Fin n) ℂ).transpose z‖) ^ (3 * n))⁻¹) ≤
      ENNReal.ofReal (C4 * (detW (b k.1 : Matrix (Fin n) (Fin n) ℂ))⁻¹) := by
    intro k
    have h := hvol _ (hB k.1).transpose
    rwa [detW_transpose] at h
  have hP0 : ∀ k : W × Fin M, 0 ≤ C4 * (detW (b k.1 : Matrix (Fin n) (Fin n) ℂ))⁻¹ :=
    fun k => mul_nonneg hC4 (inv_nonneg.mpr (hd k.1).le)
  have hint : ∫⁻ y : TupV W n M,
      ENNReal.ofReal (((1 + ‖y‖) ^ (Fintype.card (W × Fin M) * (3 * n)))⁻¹ *
        ((1 + ‖polarOp J (fun w => (b w : Matrix (Fin n) (Fin n) ℂ)) y‖) ^
          (Fintype.card (W × Fin M) * (3 * n)))⁻¹) ≤
      ENNReal.ofReal ((C2 ^ (3 * n)) ^ Fintype.card (W × Fin M) *
        (C3 * ∏ k : W × Fin M, (C4 * (detW (b k.1 : Matrix (Fin n) (Fin n) ℂ))⁻¹))) := by
    calc _ ≤ ∫⁻ y : TupV W n M, ENNReal.ofReal ((C2 ^ (3 * n)) ^ Fintype.card (W × Fin M)) *
            ∏ k, ENNReal.ofReal (((1 + ‖y k‖) ^ (3 * n))⁻¹ *
              ((1 + ‖Matrix.toEuclideanLin (b k.1 : Matrix (Fin n) (Fin n) ℂ).transpose (y k)‖) ^
                (3 * n))⁻¹) := lintegral_mono hpt
      _ = ENNReal.ofReal ((C2 ^ (3 * n)) ^ Fintype.card (W × Fin M)) *
            ∫⁻ y : TupV W n M, ∏ k, ENNReal.ofReal (((1 + ‖y k‖) ^ (3 * n))⁻¹ *
              ((1 + ‖Matrix.toEuclideanLin (b k.1 : Matrix (Fin n) (Fin n) ℂ).transpose (y k)‖) ^
                (3 * n))⁻¹) := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ ≤ ENNReal.ofReal ((C2 ^ (3 * n)) ^ Fintype.card (W × Fin M)) *
            (ENNReal.ofReal C3 * ∏ k : W × Fin M, ∫⁻ z : EuclideanSpace ℂ (Fin n),
              ENNReal.ofReal (((1 + ‖z‖) ^ (3 * n))⁻¹ *
                ((1 + ‖Matrix.toEuclideanLin (b k.1 : Matrix (Fin n) (Fin n) ℂ).transpose z‖) ^
                  (3 * n))⁻¹)) := by
          gcongr
          exact hprod (fun k z => ENNReal.ofReal (((1 + ‖z‖) ^ (3 * n))⁻¹ *
            ((1 + ‖Matrix.toEuclideanLin (b k.1 : Matrix (Fin n) (Fin n) ℂ).transpose z‖) ^
              (3 * n))⁻¹)) hhm
      _ ≤ ENNReal.ofReal ((C2 ^ (3 * n)) ^ Fintype.card (W × Fin M)) *
            (ENNReal.ofReal C3 * ∏ k : W × Fin M,
              ENNReal.ofReal (C4 * (detW (b k.1 : Matrix (Fin n) (Fin n) ℂ))⁻¹)) := by
          gcongr with k
          exact hkv k
      _ = _ := by
          rw [← ENNReal.ofReal_prod_of_nonneg (fun k _ => hP0 k), ← ENNReal.ofReal_mul hC3,
            ← ENNReal.ofReal_mul hA0]
  have hP : ∏ k : W × Fin M, (C4 * (detW (b k.1 : Matrix (Fin n) (Fin n) ℂ))⁻¹) =
      C4 ^ Fintype.card (W × Fin M) *
        (∏ w, detW (b w : Matrix (Fin n) (Fin n) ℂ) ^ (-(M : ℝ) / 2)) ^ 2 := by
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
      sq_prod_rpow M (fun w => detW (b w : Matrix (Fin n) (Fin n) ℂ)) hd, Fintype.prod_prod_type]
    simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have hQ : 0 ≤ ∏ w, detW (b w : Matrix (Fin n) (Fin n) ℂ) ^ (-(M : ℝ) / 2) :=
    Finset.prod_nonneg fun w _ => Real.rpow_nonneg (hd w).le _
  have hw := hweyl (fun x => phaseM J (fun w => (b w : Matrix (Fin n) (Fin n) ℂ)) (tupCoord x))
    (polarOp J (fun w => (b w : Matrix (Fin n) (Fin n) ℂ)))
    (continuous_phase J _) (phase_polar W n M J hJ _ hB)
  have hsqE := hw.trans (mul_le_mul' le_rfl hint)
  rw [← ENNReal.ofReal_mul hC1, ENNReal.ofReal_le_ofReal_iff (mul_nonneg hC1 (mul_nonneg hA0
    (mul_nonneg hC3 (Finset.prod_nonneg fun k _ => hP0 k)))), hP] at hsqE
  have hsq : ‖∫ x, g x * Complex.exp (2 * Real.pi * Complex.I *
        ((phaseM J (fun w => (b w : Matrix (Fin n) (Fin n) ℂ)) (tupCoord x) : ℝ) : ℂ))‖ ^ 2 ≤
      (C1 * (C2 ^ (3 * n)) ^ Fintype.card (W × Fin M) * C3 * C4 ^ Fintype.card (W × Fin M)) *
        (∏ w, detW (b w : Matrix (Fin n) (Fin n) ℂ) ^ (-(M : ℝ) / 2)) ^ 2 := by
    refine hsqE.trans (le_of_eq ?_)
    ring
  rw [hcore, norm_mul, Complex.norm_of_nonneg hc0, mul_assoc c]
  refine mul_le_mul_of_nonneg_left ?_ hc0
  calc _ = |‖∫ x, g x * Complex.exp (2 * Real.pi * Complex.I *
        ((phaseM J (fun w => (b w : Matrix (Fin n) (Fin n) ℂ)) (tupCoord x) : ℝ) : ℂ))‖| :=
        (abs_norm _).symm
    _ ≤ Real.sqrt ((C1 * (C2 ^ (3 * n)) ^ Fintype.card (W × Fin M) * C3 *
          C4 ^ Fintype.card (W × Fin M)) *
        (∏ w, detW (b w : Matrix (Fin n) (Fin n) ℂ) ^ (-(M : ℝ) / 2)) ^ 2) := Real.abs_le_sqrt hsq
    _ = _ := by rw [Real.sqrt_mul hK0, Real.sqrt_sq hQ]

end GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.Bound
