import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMemBand
import GroundTheory.AutomorphicForms.CuspidalDiscreteness.ExistsNormRconvLeSiegel
import GroundTheory.AutomorphicForms.ReductionSiegel
open NumberField MeasureTheory GlobalTheory.CuspRep GlobalTheory.HCF Topology
open scoped ContDiff

noncomputable section

namespace GlobalTheory.AltConv

open GroundTheory.Automorphic

variable {E : Type} [Field E] [NumberField E] {a : ℕ}

abbrev Mat (E : Type) [Field E] [NumberField E] (a : ℕ) : Type := Matrix (Fin a) (Fin a) (Cinf E)

def toLA : Mat E a ≃+ Lie E a := Matrix.ofAddEquiv.symm

theorem toLA_apply (M : Mat E a) : toLA M = toL M := rfl

theorem isAddHaar_row : (volume : Measure (Fin a → Cinf E)).IsAddHaarMeasure :=
  Measure.pi.isAddHaarMeasure (fun _ : Fin a => (volume : Measure (Cinf E)))

theorem isAddHaar_lie : (volume : Measure (Lie E a)).IsAddHaarMeasure := by
  haveI := isAddHaar_row (E := E) (a := a)
  exact Measure.pi.isAddHaarMeasure (fun _ : Fin a => (volume : Measure (Fin a → Cinf E)))

theorem det_eq_one_of_sq {W : Type} [AddCommGroup W] [Module ℝ W] [Module.Finite ℝ W]
    {L : W →ₗ[ℝ] W} (hK : (L - 1) * (L - 1) = 0) : LinearMap.det L = 1 := by
  have hN : IsNilpotent (L - 1) := ⟨2, by rw [pow_two, hK]⟩
  have h := (hN.neg).charpoly_eq_X_pow_finrank
  have h2 := LinearMap.eval_charpoly (-(L - 1)) 1
  rw [h] at h2
  simpa using h2.symm

def mulL (P : Mat E a) : Lie E a →ₗ[ℝ] Lie E a where
  toFun w := toL (P * Matrix.of w)
  map_add' x y := by
    show toL (P * (Matrix.of x + Matrix.of y)) = _
    rw [Matrix.mul_add]; rfl
  map_smul' c x := by
    show toL (P * (c • Matrix.of x)) = _
    rw [Matrix.mul_smul]; rfl

theorem mulL_mul (P P' : Mat E a) : mulL P * mulL P' = mulL (P * P') := by
  refine LinearMap.ext fun w => ?_
  show toL (P * (P' * Matrix.of w)) = toL (P * P' * Matrix.of w)
  rw [Matrix.mul_assoc]

theorem mulL_zero : mulL (0 : Mat E a) = 0 := by
  refine LinearMap.ext fun w => ?_
  show toL ((0 : Mat E a) * Matrix.of w) = 0
  rw [Matrix.zero_mul]; rfl

theorem one_add_mulL_apply (P : Mat E a) (w : Lie E a) :
    (1 + mulL P) w = toL ((1 + P) * Matrix.of w) := by
  show w + toL (P * Matrix.of w) = _
  rw [Matrix.add_mul, Matrix.one_mul]; rfl

theorem one_sub_mulL_apply (P : Mat E a) (w : Lie E a) :
    (1 - mulL P) w = toL ((1 - P) * Matrix.of w) := by
  show w - toL (P * Matrix.of w) = _
  rw [Matrix.sub_mul, Matrix.one_mul]; rfl

def shear (P : Mat E a) (hP : P * P = 0) : Lie E a ≃ₗ[ℝ] Lie E a :=
  LinearEquiv.ofLinear (1 + mulL P) (1 - mulL P)
    (by
      show (1 + mulL P) * (1 - mulL P) = 1
      calc (1 + mulL P) * (1 - mulL P) = 1 - mulL P * mulL P := by noncomm_ring
        _ = 1 := by rw [mulL_mul, hP, mulL_zero, sub_zero])
    (by
      show (1 - mulL P) * (1 + mulL P) = 1
      calc (1 - mulL P) * (1 + mulL P) = 1 - mulL P * mulL P := by noncomm_ring
        _ = 1 := by rw [mulL_mul, hP, mulL_zero, sub_zero])

theorem shear_apply (P : Mat E a) (hP : P * P = 0) (w : Lie E a) :
    shear P hP w = toL ((1 + P) * Matrix.of w) := one_add_mulL_apply P w

theorem shear_symm_apply (P : Mat E a) (hP : P * P = 0) (w : Lie E a) :
    (shear P hP).symm w = toL ((1 - P) * Matrix.of w) := one_sub_mulL_apply P w

theorem measurePreserving_shear (P : Mat E a) (hP : P * P = 0) :
    MeasurePreserving (shear P hP).toContinuousLinearEquiv.toHomeomorph.toMeasurableEquiv volume volume := by
  haveI := isAddHaar_lie (E := E) (a := a)
  refine ⟨(shear P hP).toContinuousLinearEquiv.continuous.measurable, ?_⟩
  have hdet : LinearMap.det (1 + mulL P : Lie E a →ₗ[ℝ] Lie E a) = 1 :=
    det_eq_one_of_sq (by rw [add_sub_cancel_left, mulL_mul, hP, mulL_zero])
  have h := Measure.map_linearMap_addHaar_eq_smul_addHaar (μ := (volume : Measure (Lie E a)))
    (f := 1 + mulL P) (by rw [hdet]; norm_num)
  rw [hdet] at h
  simp only [inv_one, abs_one, ENNReal.ofReal_one, one_smul] at h
  exact h

theorem altPoint_sq {m : ℕ} {Y : Fin m → Mat E a} (hY : ∀ i j, Y i * Y j = 0) (ε : Fin m → Bool) :
    altPoint Y ε * altPoint Y ε = 0 := by
  unfold altPoint
  rw [Finset.sum_mul_sum]
  refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => ?_
  split_ifs <;> simp [hY]

theorem toL_altPoint {m : ℕ} (Y : Fin m → Mat E a) (ε : Fin m → Bool) :
    toL (altPoint Y ε) = altPoint (fun i => toL (Y i)) ε := by
  unfold altPoint
  rw [← toLA_apply, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  split_ifs <;> simp [toLA_apply]

theorem norm_toL_altPoint_le {m : ℕ} {Y : Fin m → Mat E a} {R : ℝ} (hR : ∀ i, ‖toL (Y i)‖ ≤ R)
    (ε : Fin m → Bool) : ‖toL (altPoint Y ε)‖ ≤ m * R := by
  rw [toL_altPoint]
  unfold altPoint
  calc ‖∑ i, if ε i then toL (Y i) else 0‖ ≤ ∑ i : Fin m, ‖if ε i then toL (Y i) else 0‖ :=
        norm_sum_le _ _
    _ ≤ ∑ _i : Fin m, R := by
        refine Finset.sum_le_sum fun i _ => ?_
        split_ifs
        · exact hR i
        · rw [norm_zero]; exact (norm_nonneg _).trans (hR i)
    _ = m * R := by simp

theorem add_altPoint_eq {m : ℕ} (Y : Fin m → Mat E a) (ε : Fin m → Bool) (v : Lie E a) :
    v + altPoint (fun i => toL (-(Y i * Matrix.of v))) ε = toL ((1 - altPoint Y ε) * Matrix.of v) := by
  have h1 : altPoint (fun i => -(Y i * Matrix.of v)) ε = -(altPoint Y ε * Matrix.of v) := by
    unfold altPoint
    rw [Finset.sum_mul, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    split_ifs <;> simp
  rw [← toL_altPoint (fun i => -(Y i * Matrix.of v)), h1, Matrix.sub_mul, Matrix.one_mul, sub_eq_add_neg,
    ← toLA_apply, ← toLA_apply, map_add]
  rfl

theorem norm_toL_mul_le (Y X : Mat E a) : ‖toL (Y * X)‖ ≤ a * ‖toL Y‖ * ‖toL X‖ := by
  have h0 : 0 ≤ (a : ℝ) * ‖toL Y‖ * ‖toL X‖ := by positivity
  refine (pi_norm_le_iff_of_nonneg h0).2 fun i => (pi_norm_le_iff_of_nonneg h0).2 fun j => ?_
  have hY : ∀ l, ‖Y i l‖ ≤ ‖toL Y‖ := fun l => (norm_le_pi_norm (toL Y i) l).trans (norm_le_pi_norm (toL Y) i)
  have hX : ∀ l, ‖X l j‖ ≤ ‖toL X‖ := fun l => (norm_le_pi_norm (toL X l) j).trans (norm_le_pi_norm (toL X) l)
  show ‖(Y * X) i j‖ ≤ _
  rw [Matrix.mul_apply]
  calc ‖∑ l, Y i l * X l j‖ ≤ ∑ l : Fin a, ‖Y i l‖ * ‖X l j‖ :=
        (norm_sum_le _ _).trans (Finset.sum_le_sum fun l _ => norm_mul_le _ _)
    _ ≤ ∑ _l : Fin a, ‖toL Y‖ * ‖toL X‖ :=
        Finset.sum_le_sum fun l _ => mul_le_mul (hY l) (hX l) (norm_nonneg _) (norm_nonneg _)
    _ = a * ‖toL Y‖ * ‖toL X‖ := by simp [mul_assoc]

theorem continuous_of_lie : Continuous (fun y : Lie E a => (Matrix.of y : Mat E a)) := continuous_id

theorem continuous_toL : Continuous (fun M : Mat E a => toL M) := continuous_id

def sqBall (r : ℝ) : Set (Lie E a) := {y | ‖y‖ ≤ r ∧ Matrix.of y * Matrix.of y = 0}

theorem isCompact_sqBall (r : ℝ) : IsCompact (sqBall (E := E) (a := a) r) := by
  refine (isCompact_closedBall (0 : Lie E a) r).of_isClosed_subset ?_ fun y hy => ?_
  · exact (isClosed_le continuous_norm continuous_const).inter
      (isClosed_eq (continuous_of_lie.matrix_mul continuous_of_lie) continuous_const)
  · rw [mem_closedBall_zero_iff]; exact hy.1

def act (p : Lie E a × Lie E a) : Lie E a := toL ((1 + Matrix.of p.1) * Matrix.of p.2)

theorem continuous_act : Continuous (act (E := E) (a := a)) :=
  continuous_toL.comp ((continuous_const.add (continuous_of_lie.comp continuous_fst)).matrix_mul
    (continuous_of_lie.comp continuous_snd))

theorem isUnit_one_add_of_sq {P : Mat E a} (hP : P * P = 0) : IsUnit (1 + P) := by
  refine ⟨⟨1 + P, 1 - P, ?_, ?_⟩, rfl⟩
  · calc (1 + P) * (1 - P) = 1 - P * P := by noncomm_ring
      _ = 1 := by rw [hP, sub_zero]
  · calc (1 - P) * (1 + P) = 1 - P * P := by noncomm_ring
      _ = 1 := by rw [hP, sub_zero]

theorem norm_sum_altSign_integral_le : ∀ (E : Type) [Field E] [NumberField E] (a : ℕ) (β : Lie E a → ℂ), ContDiff ℝ ∞ β →
    HasCompactSupport β → tsupport β ⊆ invSet E a → ∀ (m : ℕ) (R : ℝ), ∃ (c : ℝ) (Q : Set (Lie E a)),
    0 ≤ c ∧ IsCompact Q ∧ Q ⊆ invSet E a ∧ ∀ f : Lie E a → ℂ, ContinuousOn f (invSet E a) →
    ∀ F : ℝ, 0 ≤ F → (∀ w ∈ Q, ‖f w‖ ≤ F) →
    ∀ Y : Fin m → Matrix (Fin a) (Fin a) (Cinf E), (∀ i j, Y i * Y j = 0) → (∀ i, ‖toL (Y i)‖ ≤ R) →
    ‖∑ ε : Fin m → Bool, (GroundTheory.Automorphic.altSign ε : ℂ) *
        ∫ w, f (toL ((1 + GroundTheory.Automorphic.altPoint Y ε) * Matrix.of w)) * β w‖ ≤ c * F * ∏ i, ‖toL (Y i)‖ := by
  intro E _ _ a β hβ hβc hβu m R
  haveI := isAddHaar_lie (E := E) (a := a)
  obtain ⟨Bm, hBm⟩ := exists_norm_altSum_le (E := Lie E a) (F := ℂ) hβ hβc m
  set Q : Set (Lie E a) := act '' (sqBall (m * R) ×ˢ tsupport β) with hQdef
  have hQc : IsCompact Q := ((isCompact_sqBall _).prod hβc).image continuous_act
  have hQu : Q ⊆ invSet E a := by
    rintro _ ⟨⟨y, w⟩, ⟨hy, hw⟩, rfl⟩
    show IsUnit ((1 + Matrix.of y) * Matrix.of w)
    exact (isUnit_one_add_of_sq hy.2).mul (hβu hw)
  obtain ⟨Rq, hRq⟩ := hQc.exists_bound_of_continuousOn continuous_id.continuousOn
  set Bm' := max Bm 0 with hBm'
  set Rq' := max Rq 0 with hRq'
  have hBm0 : 0 ≤ Bm' := le_max_right _ _
  have hRq0 : 0 ≤ Rq' := le_max_right _ _
  refine ⟨Bm' * ((a : ℝ) * Rq') ^ m * volume.real Q, Q, by positivity, hQc, hQu, ?_⟩
  intro f hf F hF hFQ Y hY hR
  have hP : ∀ ε, altPoint Y ε * altPoint Y ε = 0 := altPoint_sq hY
  have hmemQ : ∀ ε v, toL ((1 - altPoint Y ε) * Matrix.of v) ∈ tsupport β → v ∈ Q := by
    intro ε v hv
    refine ⟨(toL (altPoint Y ε), toL ((1 - altPoint Y ε) * Matrix.of v)),
      ⟨⟨norm_toL_altPoint_le hR ε, hP ε⟩, hv⟩, ?_⟩
    show toL ((1 + altPoint Y ε) * ((1 - altPoint Y ε) * Matrix.of v)) = v
    have h1 : (1 + altPoint Y ε) * (1 - altPoint Y ε) = 1 := by
      calc (1 + altPoint Y ε) * (1 - altPoint Y ε) = 1 - altPoint Y ε * altPoint Y ε := by noncomm_ring
        _ = 1 := by rw [hP ε, sub_zero]
    rw [← Matrix.mul_assoc, h1, Matrix.one_mul]
    rfl
  have hstep : ∀ ε, ∫ w, f (toL ((1 + altPoint Y ε) * Matrix.of w)) * β w =
      ∫ v, f v * β (toL ((1 - altPoint Y ε) * Matrix.of v)) := by
    intro ε
    have hmp := measurePreserving_shear (altPoint Y ε) (hP ε)
    rw [← hmp.integral_comp' (g := fun v => f v * β (toL ((1 - altPoint Y ε) * Matrix.of v)))]
    refine integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
    have e1 : (shear _ (hP ε)).toContinuousLinearEquiv.toHomeomorph.toMeasurableEquiv w =
        shear _ (hP ε) w := rfl
    simp only [e1]
    rw [← shear_symm_apply _ (hP ε), LinearEquiv.symm_apply_apply, shear_apply]
  have hint : ∀ ε, Integrable (fun v => f v * β (toL ((1 - altPoint Y ε) * Matrix.of v))) := by
    intro ε
    have hg : Continuous fun v : Lie E a => toL ((1 - altPoint Y ε) * Matrix.of v) :=
      continuous_toL.comp (continuous_const.matrix_mul continuous_of_lie)
    have hsub : tsupport (fun v => f v * β (toL ((1 - altPoint Y ε) * Matrix.of v))) ⊆ Q :=
      (tsupport_mul_subset_right).trans
        ((tsupport_comp_subset_preimage β hg).trans fun v hv => hmemQ ε v hv)
    exact Continuous.integrable_of_hasCompactSupport
      ((hf.mul (hβ.continuous.comp hg).continuousOn).continuous_of_tsupport_subset isOpen_invSet
        (hsub.trans hQu))
      (hQc.of_isClosed_subset (isClosed_tsupport _) hsub)
  have hA : ∀ v, ∑ ε : Fin m → Bool, (altSign ε : ℂ) * (f v * β (toL ((1 - altPoint Y ε) * Matrix.of v))) =
      f v * altSum m β (fun i => toL (-(Y i * Matrix.of v))) v := by
    intro v
    rw [altSum_eq_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun ε _ => ?_
    rw [add_altPoint_eq, zsmul_eq_mul]
    ring
  simp_rw [hstep, ← integral_const_mul]
  rw [← integral_finsetSum _ (fun ε _ => (hint ε).const_mul _)]
  simp_rw [hA]
  have hpt : ∀ v, ‖f v * altSum m β (fun i => toL (-(Y i * Matrix.of v))) v‖ ≤
      Q.indicator (fun _ => F * (Bm' * (((a : ℝ) * Rq') ^ m * ∏ i, ‖toL (Y i)‖))) v := by
    intro v
    by_cases hv : v ∈ Q
    · rw [Set.indicator_of_mem hv, norm_mul]
      refine mul_le_mul (hFQ v hv) ?_ (norm_nonneg _) hF
      refine (hBm _ _).trans ?_
      have hv' : ‖v‖ ≤ Rq' := (hRq v hv).trans (le_max_left _ _)
      have hprod : ∏ i, ‖toL (-(Y i * Matrix.of v))‖ ≤ ((a : ℝ) * Rq') ^ m * ∏ i, ‖toL (Y i)‖ := by
        rw [← Fin.prod_const, ← Finset.prod_mul_distrib]
        refine Finset.prod_le_prod (fun i _ => norm_nonneg _) fun i _ => ?_
        have hn : ‖toL (-(Y i * Matrix.of v))‖ = ‖toL (Y i * Matrix.of v)‖ := by
          show ‖-(toL (Y i * Matrix.of v))‖ = _
          exact norm_neg _
        rw [hn]
        have hnv : ‖toL (Matrix.of v : Mat E a)‖ = ‖v‖ := rfl
        calc ‖toL (Y i * Matrix.of v)‖ ≤ a * ‖toL (Y i)‖ * ‖toL (Matrix.of v : Mat E a)‖ := norm_toL_mul_le _ _
          _ = a * ‖toL (Y i)‖ * ‖v‖ := by rw [hnv]
          _ ≤ a * ‖toL (Y i)‖ * Rq' :=
              mul_le_mul_of_nonneg_left hv' (mul_nonneg (Nat.cast_nonneg _) (norm_nonneg _))
          _ = a * Rq' * ‖toL (Y i)‖ := by ring
      calc Bm * ∏ i, ‖toL (-(Y i * Matrix.of v))‖ ≤ Bm' * ∏ i, ‖toL (-(Y i * Matrix.of v))‖ :=
            mul_le_mul_of_nonneg_right (le_max_left _ _) (Finset.prod_nonneg fun i _ => norm_nonneg _)
        _ ≤ Bm' * (((a : ℝ) * Rq') ^ m * ∏ i, ‖toL (Y i)‖) := mul_le_mul_of_nonneg_left hprod hBm0
    · rw [Set.indicator_of_notMem hv]
      have hz : altSum m β (fun i => toL (-(Y i * Matrix.of v))) v = 0 := by
        rw [altSum_eq_sum]
        refine Finset.sum_eq_zero fun ε _ => ?_
        rw [add_altPoint_eq]
        by_cases hs : toL ((1 - altPoint Y ε) * Matrix.of v) ∈ tsupport β
        · exact absurd (hmemQ ε v hs) hv
        · rw [image_eq_zero_of_notMem_tsupport hs, smul_zero]
      rw [hz, mul_zero, norm_zero]
  calc ‖∫ v, f v * altSum m β (fun i => toL (-(Y i * Matrix.of v))) v‖
      ≤ ∫ v, Q.indicator (fun _ => F * (Bm' * (((a : ℝ) * Rq') ^ m * ∏ i, ‖toL (Y i)‖))) v :=
        norm_integral_le_of_norm_le ((integrableOn_const hQc.measure_lt_top.ne).integrable_indicator
          hQc.measurableSet) (Filter.Eventually.of_forall hpt)
    _ = F * (Bm' * (((a : ℝ) * Rq') ^ m * ∏ i, ‖toL (Y i)‖)) * volume.real Q := by
        rw [integral_indicator hQc.measurableSet, setIntegral_const, smul_eq_mul, mul_comm]
    _ = Bm' * ((a : ℝ) * Rq') ^ m * volume.real Q * F * ∏ i, ‖toL (Y i)‖ := by ring

end GlobalTheory.AltConv
