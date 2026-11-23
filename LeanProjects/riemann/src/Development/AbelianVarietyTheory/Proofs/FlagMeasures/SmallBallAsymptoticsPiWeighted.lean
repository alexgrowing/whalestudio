import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsGaugeAll
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TendstoProdSmallBallAsymptoticsStatement

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas

namespace GlobalTheory

theorem smallBall_pi_fin (n : ℕ) : ∀ (X : Fin n → Type) [∀ i, MeasurableSpace (X i)]
    (ν : ∀ i, Measure (X i)) [∀ i, IsFiniteMeasure (ν i)] (ρ : ∀ i, X i → ℝ) (d : Fin n → ℕ)
    (C : Fin n → ℝ), (∀ i, Measurable (ρ i)) → (∀ i x, 0 ≤ ρ i x) → (∀ i, 0 < C i) →
    (∀ i, Filter.Tendsto (fun r : ℝ => ν i {x | Real.sqrt (ρ i x) ≤ r} / ENNReal.ofReal (r ^ d i))
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (ENNReal.ofReal (C i) * volume (Metric.ball (0 : EuclideanSpace ℝ (Fin (d i))) 1)))) →
    Filter.Tendsto (fun r : ℝ => Measure.pi ν {x | Real.sqrt (∑ i, ρ i (x i)) ≤ r} /
        ENNReal.ofReal (r ^ ∑ i, d i)) (nhdsWithin 0 (Set.Ioi 0))
      (nhds (ENNReal.ofReal (∏ i, C i) *
        volume (Metric.ball (0 : EuclideanSpace ℝ (Fin (∑ i, d i))) 1))) := by
  induction n with
  | zero =>
    intro X _ ν _ ρ d C _ _ _ _
    have hball : ∀ m : ℕ, m = 0 →
        volume (Metric.ball (0 : EuclideanSpace ℝ (Fin m)) 1) = 1 := by
      rintro m rfl
      rw [volume_euclideanSpace_eq_dirac]
      exact Measure.dirac_apply_of_mem (Metric.mem_ball_self one_pos)
    rw [hball _ (Fin.sum_univ_zero d), Fin.prod_univ_zero, ENNReal.ofReal_one, mul_one]
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with r hr
    have hr' : (0 : ℝ) ≤ r := le_of_lt hr
    have hset : {x : ∀ i : Fin 0, X i | Real.sqrt (∑ i, ρ i (x i)) ≤ r} = Set.univ := by
      ext x
      simp [hr']
    rw [hset, Measure.pi_univ]
    simp
  | succ n ih =>
    intro X _ ν _ ρ d C hρm hρ0 hC h
    have hmp := measurePreserving_piFinSuccAbove ν 0
    have h2 := ih (fun j => X (Fin.succAbove 0 j)) (fun j => ν (Fin.succAbove 0 j))
      (fun j => ρ (Fin.succAbove 0 j)) (fun j => d (Fin.succAbove 0 j))
      (fun j => C (Fin.succAbove 0 j)) (fun j => hρm _) (fun j => hρ0 _) (fun j => hC _)
      (fun j => h _)
    have hmeas2 : Measurable fun y : (∀ j : Fin n, X (Fin.succAbove 0 j)) =>
        ∑ j, ρ (Fin.succAbove 0 j) (y j) :=
      Finset.measurable_sum _ fun j _ => (hρm _).comp (measurable_pi_apply j)
    have key := GlobalTheory.T.tendsto_prod_smallBall_asymptotics (X 0) (∀ j : Fin n, X (Fin.succAbove 0 j)) (ν 0)
      (Measure.pi fun j => ν (Fin.succAbove 0 j)) (ρ 0)
      (fun y => ∑ j, ρ (Fin.succAbove 0 j) (y j)) (d 0) (∑ j, d (Fin.succAbove 0 j))
      (C 0) (∏ j, C (Fin.succAbove 0 j)) (hρm 0) hmeas2 (hρ0 0)
      (fun y => Finset.sum_nonneg fun j _ => hρ0 _ _) (hC 0)
      (Finset.prod_pos fun j _ => hC _) (h 0) h2
    have hsumd : d 0 + ∑ j, d (Fin.succAbove 0 j) = ∑ i, d i :=
      (Fin.sum_univ_succAbove d 0).symm
    have hprodC : C 0 * ∏ j, C (Fin.succAbove 0 j) = ∏ i, C i :=
      (Fin.prod_univ_succAbove C 0).symm
    rw [hsumd, hprodC] at key
    refine key.congr' (Filter.Eventually.of_forall fun r => ?_)
    congr 1
    rw [← hmp.measure_preimage_equiv]
    congr 1
    ext x
    change Real.sqrt (ρ 0 (x 0) + ∑ j, ρ (Fin.succAbove 0 j) (x (Fin.succAbove 0 j))) ≤ r ↔
      Real.sqrt (∑ i, ρ i (x i)) ≤ r
    rw [Fin.sum_univ_succAbove (fun i => ρ i (x i)) 0]

theorem smallBall_weight {X : Type} [MeasurableSpace X] (ν : Measure X) (ρ : X → ℝ) (d : ℕ)
    (w : ℝ) (hw : 0 < w) (V : ENNReal)
    (h : Filter.Tendsto (fun r : ℝ => ν {x | Real.sqrt (ρ x) ≤ r} / ENNReal.ofReal (r ^ d))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds V)) :
    Filter.Tendsto (fun r : ℝ => ν {x | Real.sqrt (w * ρ x) ≤ r} / ENNReal.ofReal (r ^ d))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (ENNReal.ofReal (w ^ (-((d : ℝ) / 2))) * V)) := by
  have hs : 0 < Real.sqrt w := Real.sqrt_pos.2 hw
  have hmap : Filter.Tendsto (fun r : ℝ => r / Real.sqrt w) (nhdsWithin 0 (Set.Ioi 0))
      (nhdsWithin 0 (Set.Ioi 0)) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
    · have h0 : Filter.Tendsto (fun r : ℝ => r / Real.sqrt w) (nhds 0)
          (nhds (0 / Real.sqrt w)) := (continuous_id.div_const _).tendsto 0
      rw [zero_div] at h0
      exact h0.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with r hr
      exact div_pos hr hs
  have key := ENNReal.Tendsto.mul_const (h.comp hmap)
    (b := ENNReal.ofReal (w ^ (-((d : ℝ) / 2)))) (Or.inr ENNReal.ofReal_ne_top)
  rw [mul_comm]
  refine key.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with r hr
  have hr' : (0 : ℝ) < r := hr
  have hrs : 0 < r / Real.sqrt w := div_pos hr' hs
  have hset : {x | Real.sqrt (w * ρ x) ≤ r} = {x | Real.sqrt (ρ x) ≤ r / Real.sqrt w} := by
    ext x
    simp only [Set.mem_ofPred_eq, Real.sqrt_mul hw.le, le_div_iff₀' hs]
  have hc : w ^ (-((d : ℝ) / 2)) = (Real.sqrt w ^ d)⁻¹ := by
    rw [Real.rpow_neg hw.le, Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hw.le]
    congr 2
    ring
  have hrd : r ^ d = (r / Real.sqrt w) ^ d * Real.sqrt w ^ d := by
    rw [div_pow, div_mul_cancel₀]
    exact pow_ne_zero _ hs.ne'
  have ha0 : ENNReal.ofReal ((r / Real.sqrt w) ^ d) ≠ 0 := by
    rw [Ne, ENNReal.ofReal_eq_zero, not_le]
    exact pow_pos hrs d
  simp only [Function.comp_apply]
  rw [hset, hc, hrd, ENNReal.ofReal_mul (pow_nonneg hrs.le d),
    ENNReal.ofReal_inv_of_pos (pow_pos hs d)]
  simp only [ENNReal.div_eq_inv_mul]
  rw [ENNReal.mul_inv (Or.inl ha0) (Or.inl ENNReal.ofReal_ne_top)]
  ring

theorem smallBall_pi_weight : ∀ (ι : Type) [Fintype ι] (X : ι → Type) [∀ i, MeasurableSpace (X i)] (ν : ∀ i, Measure (X i)) [∀ i, IsFiniteMeasure (ν i)] (ρ : ∀ i, X i → ℝ) (d : ι → ℕ) (w : ι → ℝ), (∀ i, Measurable (ρ i)) → (∀ i x, 0 ≤ ρ i x) → (∀ i, 0 < w i) → (∀ i, Filter.Tendsto (fun r : ℝ => ν i {x | Real.sqrt (ρ i x) ≤ r} / ENNReal.ofReal (r ^ d i)) (nhdsWithin 0 (Set.Ioi 0)) (nhds (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin (d i))) 1)))) → Filter.Tendsto (fun r : ℝ => Measure.pi ν {x | Real.sqrt (∑ i, w i * ρ i (x i)) ≤ r} / ENNReal.ofReal (r ^ ∑ i, d i)) (nhdsWithin 0 (Set.Ioi 0)) (nhds (ENNReal.ofReal (∏ i, w i ^ (-((d i : ℝ) / 2))) * volume (Metric.ball (0 : EuclideanSpace ℝ (Fin (∑ i, d i))) 1))) := by
  intro ι _ X _ ν _ ρ d w hρm hρ0 hw h
  have hw' : ∀ i, Filter.Tendsto
      (fun r : ℝ => ν i {x | Real.sqrt (w i * ρ i x) ≤ r} / ENNReal.ofReal (r ^ d i))
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (ENNReal.ofReal (w i ^ (-((d i : ℝ) / 2))) *
        volume (Metric.ball (0 : EuclideanSpace ℝ (Fin (d i))) 1))) :=
    fun i => smallBall_weight (ν i) (ρ i) (d i) (w i) (hw i) _ (h i)
  let f : Fin (Fintype.card ι) ≃ ι := (Fintype.equivFin ι).symm
  have key := smallBall_pi_fin (Fintype.card ι) (fun j => X (f j)) (fun j => ν (f j))
    (fun j x => w (f j) * ρ (f j) x) (fun j => d (f j))
    (fun j => w (f j) ^ (-((d (f j) : ℝ) / 2))) (fun j => (hρm _).const_mul _)
    (fun j x => mul_nonneg (hw _).le (hρ0 _ x)) (fun j => Real.rpow_pos_of_pos (hw _) _)
    (fun j => hw' _)
  have hS : ∑ j, d (f j) = ∑ i, d i := Equiv.sum_comp f d
  have hP : ∏ j, w (f j) ^ (-((d (f j) : ℝ) / 2)) = ∏ i, w i ^ (-((d i : ℝ) / 2)) :=
    Equiv.prod_comp f (fun i => w i ^ (-((d i : ℝ) / 2)))
  rw [hS, hP] at key
  have hmp := measurePreserving_piCongrLeft ν f
  refine key.congr' (Filter.Eventually.of_forall fun r => ?_)
  congr 1
  rw [← hmp.measure_preimage_equiv]
  congr 1
  ext g
  simp only [Set.mem_preimage, Set.mem_ofPred_eq]
  have hsum : ∑ i, w i * ρ i (MeasurableEquiv.piCongrLeft X f g i) =
      ∑ j, w (f j) * ρ (f j) (g j) := by
    rw [← Equiv.sum_comp f (fun i => w i * ρ i (MeasurableEquiv.piCongrLeft X f g i))]
    simp only [MeasurableEquiv.piCongrLeft_apply_apply]
  rw [hsum]

end GlobalTheory
