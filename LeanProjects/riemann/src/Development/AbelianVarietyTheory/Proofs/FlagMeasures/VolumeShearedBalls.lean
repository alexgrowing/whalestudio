import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MeasurableSetHsBall
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.IwConst

noncomputable section

namespace GlobalTheory.IwConst.Shear

theorem vol_ball_type (κ : Type) [Fintype κ] (d : ℕ) (h : Fintype.card κ = d) :
    volume {x : κ → ℝ | ∑ i, x i ^ 2 ≤ 1} = ballVol d := by
  classical
  let e : κ ≃ Fin d := Fintype.equivFinOfCardEq h
  have h1 := (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ e).measurePreserving
  have h2 := PiLp.volume_preserving_toLp κ
  have h3 := (h1.comp h2).measure_preimage
    (s := Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) 1) measurableSet_closedBall.nullMeasurableSet
  unfold ballVol
  rw [← Measure.addHaar_unitClosedBall_eq_addHaar_unitBall, ← h3]
  congr 1
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_preimage, Function.comp_apply, mem_closedBall_zero_iff,
    LinearIsometryEquiv.norm_map, EuclideanSpace.norm_eq, Real.norm_eq_abs, sq_abs, Real.sqrt_le_one]

theorem vol_ball_three (a b : ℕ) :
    volume {p : ((Fin a → ℝ) × (Fin b → ℝ)) × (Fin a → ℝ) |
      ∑ i, p.1.1 i ^ 2 + ∑ i, p.1.2 i ^ 2 + ∑ i, p.2 i ^ 2 ≤ 1} = ballVol (2 * a + b) := by
  rw [← vol_ball_type ((Fin a ⊕ Fin b) ⊕ Fin a) (2 * a + b) (by simp; ring)]
  have h1 := volume_measurePreserving_sumPiEquivProdPi (fun _ : (Fin a ⊕ Fin b) ⊕ Fin a => ℝ)
  have h2 := volume_measurePreserving_sumPiEquivProdPi (fun _ : Fin a ⊕ Fin b => ℝ)
  have h3 := (h2.prod (MeasurePreserving.id (volume : Measure (Fin a → ℝ)))).comp h1
  have hm : MeasurableSet {p : ((Fin a → ℝ) × (Fin b → ℝ)) × (Fin a → ℝ) |
      ∑ i, p.1.1 i ^ 2 + ∑ i, p.1.2 i ^ 2 + ∑ i, p.2 i ^ 2 ≤ 1} :=
    measurableSet_le (by fun_prop) measurable_const
  have h4 := h3.measure_preimage hm.nullMeasurableSet
  rw [Measure.volume_eq_prod, ← h4]
  congr 1
  ext x
  simp [Fintype.sum_sum_type, MeasurableEquiv.sumPiEquivProdPi]

theorem vol_scale (a : ℕ) (q : ℝ) :
    volume {w : Fin a → ℝ | q + ∑ i, w i ^ 2 / 2 ≤ 1} =
      ENNReal.ofReal ((2 : ℝ) ^ ((a : ℝ) / 2)) * volume {w : Fin a → ℝ | q + ∑ i, w i ^ 2 ≤ 1} := by
  have h2 : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.2 two_pos
  have h := Measure.addHaar_preimage_smul (volume : Measure (Fin a → ℝ)) (r := (Real.sqrt 2)⁻¹)
    (inv_ne_zero h2.ne') {w : Fin a → ℝ | q + ∑ i, w i ^ 2 ≤ 1}
  have e1 : |(((Real.sqrt 2)⁻¹) ^ Module.finrank ℝ (Fin a → ℝ))⁻¹| = (2 : ℝ) ^ ((a : ℝ) / 2) := by
    rw [Module.finrank_fin_fun, inv_pow, inv_inv, abs_of_pos (pow_pos h2 _), Real.sqrt_eq_rpow,
      ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    congr 1; ring
  rw [e1] at h
  rw [← h]
  congr 1
  ext w
  simp only [Set.mem_setOf_eq, Set.mem_preimage, Pi.smul_apply, smul_eq_mul, mul_pow, inv_pow,
    Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  simp only [div_eq_inv_mul]

theorem vol_ell_three (a b : ℕ) :
    volume {p : ((Fin a → ℝ) × (Fin b → ℝ)) × (Fin a → ℝ) |
      ∑ i, p.1.1 i ^ 2 + ∑ i, p.1.2 i ^ 2 + ∑ i, p.2 i ^ 2 / 2 ≤ 1} =
      ENNReal.ofReal ((2 : ℝ) ^ ((a : ℝ) / 2)) * ballVol (2 * a + b) := by
  rw [← vol_ball_three]
  have hm : MeasurableSet {p : ((Fin a → ℝ) × (Fin b → ℝ)) × (Fin a → ℝ) |
      ∑ i, p.1.1 i ^ 2 + ∑ i, p.1.2 i ^ 2 + ∑ i, p.2 i ^ 2 ≤ 1} :=
    measurableSet_le (by fun_prop) measurable_const
  have hm' : MeasurableSet {p : ((Fin a → ℝ) × (Fin b → ℝ)) × (Fin a → ℝ) |
      ∑ i, p.1.1 i ^ 2 + ∑ i, p.1.2 i ^ 2 + ∑ i, p.2 i ^ 2 / 2 ≤ 1} :=
    measurableSet_le (by fun_prop) measurable_const
  rw [Measure.volume_eq_prod, Measure.prod_apply hm, Measure.prod_apply hm',
    ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_congr fun x => ?_
  exact vol_scale a (∑ i, x.1 i ^ 2 + ∑ i, x.2 i ^ 2)

theorem vol_shear {G Z : Type} [MeasurableSpace G] [AddCommGroup G] [MeasurableAdd₂ G] [MeasurableSpace Z]
    (μ : Measure G) [μ.IsAddRightInvariant] [SFinite μ] (ν : Measure Z) [SFinite ν] (f : Z → G)
    (hf : Measurable f) (s : Set (G × Z)) (hs : MeasurableSet s) :
    (μ.prod ν) {p | (p.1 + f p.2, p.2) ∈ s} = (μ.prod ν) s := by
  have hm : MeasurableSet {p : G × Z | (p.1 + f p.2, p.2) ∈ s} :=
    (show Measurable fun p : G × Z => (p.1 + f p.2, p.2) by fun_prop) hs
  rw [Measure.prod_apply_symm hm, Measure.prod_apply_symm hs]
  refine lintegral_congr fun z => ?_
  exact measure_preimage_add_right μ (f z) ((fun x => (x, z)) ⁻¹' s)

theorem volume_sheared_balls (a b c : ℕ) (ι : (Fin c → ℝ) →ₗ[ℝ] (Fin b → ℝ)) :
    volume {v : (Fin a → ℝ) × (Fin b → ℝ) × ((Fin a → ℝ) × (Fin c → ℝ)) |
      ∑ i, (v.1 i + v.2.2.1 i / Real.sqrt 2) ^ 2 + ∑ i, (v.2.1 i + ι v.2.2.2 i) ^ 2 +
        ∑ i, v.2.2.1 i ^ 2 / 2 ≤ 1 ∧ ∑ i, v.2.2.2 i ^ 2 ≤ 1} =
      ENNReal.ofReal ((2 : ℝ) ^ ((a : ℝ) / 2)) * ballVol (2 * a + b) * ballVol c := by
  have hι : Continuous ι := ι.continuous_of_finiteDimensional
  have hS : MeasurableSet {v : (Fin a → ℝ) × (Fin b → ℝ) × ((Fin a → ℝ) × (Fin c → ℝ)) |
      ∑ i, (v.1 i + v.2.2.1 i / Real.sqrt 2) ^ 2 + ∑ i, (v.2.1 i + ι v.2.2.2 i) ^ 2 +
        ∑ i, v.2.2.1 i ^ 2 / 2 ≤ 1 ∧ ∑ i, v.2.2.2 i ^ 2 ≤ 1} := by
    rw [Set.setOf_and]
    exact ((isClosed_le (by fun_prop) continuous_const).inter
      (isClosed_le (by fun_prop) continuous_const)).measurableSet
  have hs : MeasurableSet {v : ((Fin a → ℝ) × (Fin b → ℝ)) × ((Fin a → ℝ) × (Fin c → ℝ)) |
      ∑ i, v.1.1 i ^ 2 + ∑ i, v.1.2 i ^ 2 + ∑ i, v.2.1 i ^ 2 / 2 ≤ 1 ∧ ∑ i, v.2.2 i ^ 2 ≤ 1} := by
    rw [Set.setOf_and]
    exact ((isClosed_le (by fun_prop) continuous_const).inter
      (isClosed_le (by fun_prop) continuous_const)).measurableSet
  have h1 := (volume_preserving_prodAssoc (α₁ := Fin a → ℝ) (β₁ := Fin b → ℝ)
    (γ₁ := (Fin a → ℝ) × (Fin c → ℝ))).measure_preimage hS.nullMeasurableSet
  have h2 := vol_shear ((volume : Measure (Fin a → ℝ)).prod (volume : Measure (Fin b → ℝ)))
    (volume : Measure ((Fin a → ℝ) × (Fin c → ℝ)))
    (fun z => ((fun i => z.1 i / Real.sqrt 2), ι z.2)) (Continuous.measurable (by fun_prop)) _ hs
  have h3 := (volume_preserving_prodAssoc (α₁ := (Fin a → ℝ) × (Fin b → ℝ)) (β₁ := Fin a → ℝ)
    (γ₁ := Fin c → ℝ)).measure_preimage hs.nullMeasurableSet
  rw [← h1]
  refine (h2.trans h3.symm).trans ?_
  rw [← vol_ell_three, ← vol_ball_type (Fin c) c (Fintype.card_fin c), ← Measure.prod_prod]
  rfl

end GlobalTheory.IwConst.Shear
