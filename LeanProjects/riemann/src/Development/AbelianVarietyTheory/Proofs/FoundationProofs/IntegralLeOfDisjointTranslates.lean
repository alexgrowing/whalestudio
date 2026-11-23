import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Formalism.PairingDivisors.StatementH
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.EnormPowLeInvMeasureMulLintegralBall
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

namespace GlobalTheory.ThetaSupBall

open MeasureTheory Filter Set
open scoped Pointwise

theorem integral_le_of_disjoint_translates {ι : Type} [Fintype ι]
    (A : AddSubgroup (EuclideanSpace ℂ ι)) [Countable A]
    (D t : Set (EuclideanSpace ℂ ι)) (hD : IsAddFundamentalDomain A D volume)
    (ht : MeasurableSet t)
    (hd : ∀ y₁ y₂ : A, y₁ ≠ y₂ → Disjoint (y₁ +ᵥ t) (y₂ +ᵥ t))
    (f : EuclideanSpace ℂ ι → ℝ) (hf0 : ∀ u, 0 ≤ f u) (hfc : Continuous f)
    (hf : ∀ (y : A) u, f (y +ᵥ u) = f u) (hi : IntegrableOn f D) :
    ∫ u in t, f u ≤ ∫ u in D, f u := by
  haveI : VAddInvariantMeasure A (EuclideanSpace ℂ ι) volume :=
    ⟨fun g s _ => measure_preimage_add volume (g : EuclideanSpace ℂ ι) s⟩
  rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall hf0) hfc.aestronglyMeasurable,
    integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall hf0) hfc.aestronglyMeasurable]
  refine ENNReal.toReal_mono (Integrable.lintegral_lt_top hi).ne ?_
  calc ∫⁻ u in t, ENNReal.ofReal (f u)
      = ∑' y : A, ∫⁻ u in (y +ᵥ t) ∩ D, ENNReal.ofReal (f (-y +ᵥ u)) :=
        hD.setLIntegral_eq_tsum' (fun u => ENNReal.ofReal (f u)) t
    _ = ∑' y : A, ∫⁻ u in (y +ᵥ t) ∩ D, ENNReal.ofReal (f u) := by simp_rw [hf]
    _ = ∫⁻ u in ⋃ y : A, (y +ᵥ t) ∩ D, ENNReal.ofReal (f u) := by
        refine (lintegral_iUnion₀ (fun y => ?_) ?_ _).symm
        · exact (ht.const_vadd y).nullMeasurableSet.inter hD.nullMeasurableSet
        · intro y₁ y₂ h
          exact (((hd y₁ y₂ h).inf_left _).inf_right _).aedisjoint
    _ ≤ ∫⁻ u in D, ENNReal.ofReal (f u) :=
        lintegral_mono_set (iUnion_subset fun _ => inter_subset_right)

theorem factorial_div_le (g : ℕ) {v r : ℝ} (hv : 1 ≤ v) (hr : r ^ 2 = 1 / (4 * v)) :
    (g.factorial : ℝ) / (Real.pi ^ g * r ^ (2 * g)) ≤ (2 * (g : ℝ) * v + 1) ^ g := by
  have hv0 : 0 < v := by linarith
  have hpi := Real.pi_gt_three
  rw [pow_mul, hr, ← mul_pow]
  have h1 : (g.factorial : ℝ) ≤ (g : ℝ) ^ g := by exact_mod_cast Nat.factorial_le_pow g
  calc (g.factorial : ℝ) / (Real.pi * (1 / (4 * v))) ^ g
      ≤ (g : ℝ) ^ g / (Real.pi * (1 / (4 * v))) ^ g := by gcongr
    _ = ((g : ℝ) / (Real.pi * (1 / (4 * v)))) ^ g := by rw [div_pow]
    _ ≤ _ := by
        refine pow_le_pow_left₀ (by positivity) ?_ g
        rw [div_le_iff₀ (by positivity)]
        have h2 : (2 * (g : ℝ) * v + 1) * (Real.pi * (1 / (4 * v)))
            = Real.pi / 2 * g + Real.pi / (4 * v) := by field_simp; ring
        rw [h2]
        have h3 : 0 ≤ Real.pi / (4 * v) := by positivity
        have h4 : (0 : ℝ) ≤ g := Nat.cast_nonneg g
        nlinarith

theorem sup_le_mean_square : ∀ (ι : Type) [Fintype ι] (A : AddSubgroup (EuclideanSpace ℂ ι)) (v : ℝ) (Fd : Set (EuclideanSpace ℂ ι)) (G : EuclideanSpace ℂ ι → ℂ), 1 ≤ v → (∀ x ∈ A, x ≠ 0 → 1 / v ≤ ‖x‖ ^ 2) → MeasureTheory.IsAddFundamentalDomain A Fd MeasureTheory.volume → MeasureTheory.volume Fd = 1 → Differentiable ℂ G → (∀ x ∈ A, ∀ z, ‖G (z + x)‖ ^ 2 * Real.exp (-Real.pi * ‖z + x‖ ^ 2) = ‖G z‖ ^ 2 * Real.exp (-Real.pi * ‖z‖ ^ 2)) → MeasureTheory.IntegrableOn (fun z => ‖G z‖ ^ 2 * Real.exp (-Real.pi * ‖z‖ ^ 2)) Fd → ∀ z, ‖G z‖ ^ 2 * Real.exp (-Real.pi * ‖z‖ ^ 2) ≤ 3 * (2 * (Fintype.card ι : ℝ) * v + 1) ^ Fintype.card ι * ∫ w in Fd, ‖G w‖ ^ 2 * Real.exp (-Real.pi * ‖w‖ ^ 2) := by
  intro ι _ A v Fd G hv hA hD _ hG hinv hint z
  have hv0 : 0 < v := by linarith
  set r : ℝ := Real.sqrt (1 / (4 * v)) with hrdef
  have hr0 : 0 < r := Real.sqrt_pos.2 (by positivity)
  have hr2 : r ^ 2 = 1 / (4 * v) := Real.sq_sqrt (by positivity)
  set N : EuclideanSpace ℂ ι → ℝ := fun u => ‖G u‖ ^ 2 * Real.exp (-Real.pi * ‖u‖ ^ 2) with hN
  have hN0 : ∀ u, 0 ≤ N u := fun u => by positivity
  have hGc := hG.continuous
  have hNc : Continuous N := by simp only [hN]; fun_prop
  have hdisj : ∀ y₁ y₂ : A, y₁ ≠ y₂ →
      Disjoint (y₁ +ᵥ Metric.ball z r) (y₂ +ᵥ Metric.ball z r) := by
    intro y₁ y₂ hne
    rw [Set.disjoint_left]
    rintro _ ⟨p, hp, rfl⟩ ⟨q, hq, hpq⟩
    have hpq' : (y₂ : EuclideanSpace ℂ ι) + q = (y₁ : EuclideanSpace ℂ ι) + p := hpq
    have hy : ((y₁ - y₂ : A) : EuclideanSpace ℂ ι) = q - p := by
      rw [AddSubgroup.coe_sub, sub_eq_sub_iff_add_eq_add, ← hpq', add_comm]
    have hne' : ((y₁ - y₂ : A) : EuclideanSpace ℂ ι) ≠ 0 := fun h0 =>
      hne (sub_eq_zero.mp (Subtype.ext h0))
    have h1 := hA _ (y₁ - y₂ : A).2 hne'
    rw [hy] at h1
    have h2 : ‖q - p‖ < 2 * r := by
      have hp' : dist p z < r := hp
      have hq' : dist q z < r := hq
      rw [← dist_eq_norm]
      calc dist q p ≤ dist q z + dist z p := dist_triangle _ _ _
        _ < 2 * r := by rw [dist_comm z p]; linarith
    have h3 : ‖q - p‖ ^ 2 < (2 * r) ^ 2 := by gcongr
    have h4 : (2 * r) ^ 2 = 1 / v := by rw [mul_pow, hr2]; field_simp; norm_num
    linarith
  haveI : Countable A := by
    rw [← Set.countable_univ_iff]
    refine Set.PairwiseDisjoint.countable_of_isOpen
      (s := fun y : A => y +ᵥ Metric.ball z r) (fun a _ b _ h => hdisj a b h) ?_ ?_
    · intro y _
      exact Metric.isOpen_ball.vadd (y : EuclideanSpace ℂ ι)
    · intro y _
      exact ⟨y +ᵥ z, z, Metric.mem_ball_self hr0, rfl⟩
  have hpk : ∫ u in Metric.ball z r, N u ≤ ∫ u in Fd, N u := by
    refine integral_le_of_disjoint_translates A Fd _ hD measurableSet_ball hdisj N hN0 hNc ?_ hint
    intro y u
    have e : y +ᵥ u = u + (y : EuclideanSpace ℂ ι) := by
      rw [AddSubgroup.vadd_def, vadd_eq_add, add_comm]
    rw [e]
    exact hinv y y.2 u
  set φ : EuclideanSpace ℂ ι → ℂ :=
    fun u => G u * Complex.exp (-(Real.pi : ℂ) * innerSL ℂ z (u - z)) with hφ
  have hφd : Differentiable ℂ φ := by
    refine hG.mul (Differentiable.cexp (Differentiable.const_mul ?_ _))
    exact (innerSL ℂ z).differentiable.comp (differentiable_id.sub_const z)
  have hφi : IntegrableOn (fun u => ‖φ u‖ ^ 2) (Metric.ball z r) :=
    GlobalTheory.integrableOn_norm_pow_ball volume hφd.continuous.continuousOn 2
  have hsub := GlobalTheory.norm_pow_le_factorial_div_mul_integral_ball hr0 hφd.differentiableOn 2 hφi
  rw [finrank_euclideanSpace] at hsub
  have hφz : φ z = G z := by simp [hφ]
  rw [hφz] at hsub
  have hpt : ∀ u ∈ Metric.ball z r,
      ‖φ u‖ ^ 2 * Real.exp (-Real.pi * ‖z‖ ^ 2) ≤ 3 * N u := by
    intro u hu
    have hu' : ‖u - z‖ < r := by rwa [Metric.mem_ball, dist_eq_norm] at hu
    have h1 : ‖u - z‖ ^ 2 ≤ 1 / 4 := by
      have : ‖u - z‖ ^ 2 ≤ r ^ 2 := by gcongr
      refine this.trans ?_
      rw [hr2]
      exact one_div_le_one_div_of_le (by norm_num) (by linarith)
    have h2 : ‖u‖ ^ 2 = ‖z‖ ^ 2 + 2 * (inner ℂ z (u - z)).re + ‖u - z‖ ^ 2 := by
      have := norm_add_sq (𝕜 := ℂ) z (u - z)
      rwa [add_sub_cancel] at this
    have h3 : Real.exp (Real.pi * ‖u - z‖ ^ 2) ≤ 3 := by
      have hpi := Real.pi_le_four
      have hpi0 := Real.pi_pos
      calc Real.exp (Real.pi * ‖u - z‖ ^ 2) ≤ Real.exp 1 := Real.exp_le_exp.mpr (by nlinarith [sq_nonneg ‖u - z‖])
        _ ≤ 3 := by have := Real.exp_one_lt_d9; linarith
    have h4 : ‖φ u‖ ^ 2 * Real.exp (-Real.pi * ‖z‖ ^ 2)
        = Real.exp (Real.pi * ‖u - z‖ ^ 2) * N u := by
      simp only [hφ, hN]
      rw [norm_mul, Complex.norm_exp, mul_pow, ← Real.exp_nat_mul, mul_assoc, ← Real.exp_add,
        mul_left_comm, ← Real.exp_add, h2]
      congr 2
      simp only [innerSL_apply_apply, neg_mul, Complex.neg_re, Complex.re_ofReal_mul]
      push_cast
      ring
    rw [h4]
    exact mul_le_mul_of_nonneg_right h3 (hN0 u)
  have hNi : IntegrableOn N (Metric.ball z r) :=
    (hNc.continuousOn.integrableOn_compact (isCompact_closedBall z r)).mono_set
      Metric.ball_subset_closedBall
  have hb : (∫ u in Metric.ball z r, ‖φ u‖ ^ 2) * Real.exp (-Real.pi * ‖z‖ ^ 2)
      ≤ 3 * ∫ u in Metric.ball z r, N u := by
    rw [← integral_mul_const, ← integral_const_mul]
    exact setIntegral_mono_on (hφi.mul_const _) (hNi.const_mul _) measurableSet_ball hpt
  have hnum := factorial_div_le (Fintype.card ι) hv hr2
  have hI0 : 0 ≤ ∫ u in Fd, N u := integral_nonneg hN0
  set c : ℝ := ((Fintype.card ι).factorial : ℝ) /
    (Real.pi ^ Fintype.card ι * r ^ (2 * Fintype.card ι)) with hc
  have hc0 : 0 ≤ c := by positivity
  calc ‖G z‖ ^ 2 * Real.exp (-Real.pi * ‖z‖ ^ 2)
      ≤ (c * ∫ u in Metric.ball z r, ‖φ u‖ ^ 2) * Real.exp (-Real.pi * ‖z‖ ^ 2) :=
        mul_le_mul_of_nonneg_right hsub (Real.exp_pos _).le
    _ ≤ c * (3 * ∫ u in Metric.ball z r, N u) := by
        rw [mul_assoc]; exact mul_le_mul_of_nonneg_left hb hc0
    _ ≤ c * (3 * ∫ u in Fd, N u) := by gcongr
    _ ≤ (2 * (Fintype.card ι : ℝ) * v + 1) ^ Fintype.card ι * (3 * ∫ u in Fd, N u) := by gcongr
    _ = _ := by ring

end GlobalTheory.ThetaSupBall
