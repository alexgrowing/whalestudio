import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.Entire

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2
open scoped Classical
open UpperTheory.ConvolutionTheory.R2.G (FS2 Rw nE row)
open scoped ComplexOrder

namespace UpperTheory.ConvolutionTheory.RankTwoDescent

private def wr (k r : ℕ) (y : ℝ) : ℝ := y ^ k * ((1 + y) ^ r)⁻¹

private theorem wr_pos (k r : ℕ) {y : ℝ} (hy : 0 < y) : 0 < wr k r y := by
  unfold wr; positivity

private theorem wr_top (k r : ℕ) (a : ℝ) (h : a + k ≤ r) : wr k r =O[atTop] (fun y : ℝ => y ^ (-a)) := by
  refine Asymptotics.IsBigO.of_bound 1 ?_
  filter_upwards [eventually_ge_atTop 1] with y hy
  have y0 : 0 < y := by linarith
  rw [Real.norm_of_nonneg (wr_pos k r y0).le, Real.norm_of_nonneg (Real.rpow_nonneg y0.le _), one_mul]
  have h1 : ((1 + y) ^ r)⁻¹ ≤ (y ^ r)⁻¹ :=
    inv_anti₀ (by positivity) (pow_le_pow_left₀ y0.le (by linarith) r)
  calc wr k r y ≤ y ^ k * (y ^ r)⁻¹ := mul_le_mul_of_nonneg_left h1 (by positivity)
    _ = y ^ ((k : ℝ) - r) := by rw [Real.rpow_sub y0, Real.rpow_natCast, Real.rpow_natCast, div_eq_mul_inv]
    _ ≤ y ^ (-a) := Real.rpow_le_rpow_of_exponent_le hy (by linarith)

private theorem wr_bot (k r : ℕ) : wr k r =O[𝓝[>] 0] (fun y : ℝ => y ^ (-(-(k : ℝ)))) := by
  refine Asymptotics.IsBigO.of_bound 1 ?_
  filter_upwards [self_mem_nhdsWithin] with y hy
  have y0 : 0 < y := hy
  rw [Real.norm_of_nonneg (wr_pos k r y0).le, neg_neg, Real.rpow_natCast, Real.norm_of_nonneg (by positivity), one_mul]
  exact mul_le_of_le_one_right (by positivity) (inv_le_one_of_one_le₀ (one_le_pow₀ (by linarith)))

private theorem wr_cont (k r : ℕ) : ContinuousOn (wr k r) (Set.Ioi 0) := by
  unfold wr
  refine ContinuousOn.mul (by fun_prop) (ContinuousOn.inv₀ (by fun_prop) fun y hy => ?_)
  have : (0 : ℝ) < y := hy
  positivity

private theorem one_side {T : ℝ} (hT : 0 ≤ T) (k : ℕ) {K : ℝ → ℝ → ℂ}
    (hc : ContinuousOn (Function.uncurry K) (Set.univ ×ˢ Set.Ioi 0))
    (hb : ∀ r : ℕ, ∃ B : ℝ, ∀ t ∈ Set.Icc 0 T, ∀ y, 0 < y → ‖K t y‖ ≤ B * wr k r y)
    {s : ℂ} (hs : 1 - (k : ℝ) < s.re) :
    (∀ t ∈ Set.Icc 0 T, IntegrableOn (fun y : ℝ => K t y * (y : ℂ) ^ (s - 2)) (Set.Ioi 0)) ∧
    IntervalIntegrable (fun t => ∫ y in Set.Ioi (0 : ℝ), K t y * (y : ℂ) ^ (s - 2)) volume 0 T ∧
    (∫ t in (0 : ℝ)..T, ∫ y in Set.Ioi (0 : ℝ), K t y * (y : ℂ) ^ (s - 2)) = mellin (fun y => ∫ t in (0 : ℝ)..T, K t y) (s - 1) ∧
    DifferentiableAt ℂ (mellin (fun y => ∫ t in (0 : ℝ)..T, K t y)) (s - 1) := by
  obtain ⟨r, hr⟩ := exists_nat_ge ((s - 1).re + 1 + k)
  obtain ⟨B, hB⟩ := hb r
  set c : ℂ := s - 2 with hcdef
  have hsre : (s - 1).re = s.re - 1 := by simp
  have hbot : -(k : ℝ) < (s - 1).re := by rw [hsre]; linarith

  have hwC : ContinuousOn (fun y => ((wr k r y : ℝ) : ℂ)) (Set.Ioi 0) :=
    Complex.continuous_ofReal.comp_continuousOn (wr_cont k r)
  have hM : MellinConvergent (fun y => ((wr k r y : ℝ) : ℂ)) (s - 1) :=
    mellinConvergent_of_isBigO_rpow (a := (s - 1).re + 1) (b := -(k : ℝ))
      (hwC.locallyIntegrableOn measurableSet_Ioi)
      ((Complex.isBigO_ofReal_left).2 (wr_top k r _ (by linarith))) (by linarith)
      ((Complex.isBigO_ofReal_left).2 (wr_bot k r)) hbot
  have hW : IntegrableOn (fun y : ℝ => ‖(y : ℂ) ^ c‖ * wr k r y) (Set.Ioi 0) := by
    have h : IntegrableOn _ (Set.Ioi (0 : ℝ)) := Integrable.norm hM
    refine IntegrableOn.congr_fun h (fun y hy => ?_) measurableSet_Ioi
    have y0 : (0 : ℝ) < y := hy
    have e : s - 1 - 1 = c := by rw [hcdef]; ring
    simp only [norm_smul, e, Complex.norm_real, Real.norm_of_nonneg (wr_pos k r y0).le]
  have hpw : ContinuousOn (fun y : ℝ => (y : ℂ) ^ c) (Set.Ioi 0) := fun y hy =>
    (Complex.continuousAt_ofReal_cpow_const y c (Or.inr (ne_of_gt hy))).continuousWithinAt
  have hbd : ∀ t ∈ Set.Icc 0 T, ∀ y : ℝ, 0 < y → ‖K t y * (y : ℂ) ^ c‖ ≤ B * (‖(y : ℂ) ^ c‖ * wr k r y) := by
    intro t ht y y0
    rw [norm_mul]
    calc ‖K t y‖ * ‖(y : ℂ) ^ c‖ ≤ (B * wr k r y) * ‖(y : ℂ) ^ c‖ :=
          mul_le_mul_of_nonneg_right (hB t ht y y0) (norm_nonneg _)
      _ = _ := by ring
  have hS : MeasurableSet (Set.Ioc (0 : ℝ) T ×ˢ Set.Ioi (0 : ℝ)) := measurableSet_Ioc.prod measurableSet_Ioi
  have hP : Integrable (fun p : ℝ × ℝ => K p.1 p.2 * (p.2 : ℂ) ^ c)
      ((volume.restrict (Set.Ioc 0 T)).prod (volume.restrict (Set.Ioi 0))) := by
    refine Integrable.mono' (g := fun p : ℝ × ℝ => B * (‖(p.2 : ℂ) ^ c‖ * wr k r p.2)) ?_ ?_ ?_
    · exact (Integrable.const_mul hW B).comp_snd _
    · rw [Measure.prod_restrict]
      refine ContinuousOn.aestronglyMeasurable ?_ hS
      refine ContinuousOn.mul ?_ ?_
      · exact hc.mono fun p hp => ⟨Set.mem_univ _, hp.2⟩
      · exact hpw.comp continuousOn_snd fun p hp => hp.2
    · rw [Measure.prod_restrict, ae_restrict_iff' hS]
      exact Eventually.of_forall fun p hp => hbd p.1 ⟨hp.1.1.le, hp.1.2⟩ p.2 hp.2
  have hf : ContinuousOn (fun y => ∫ t in (0 : ℝ)..T, K t y) (Set.Ioi 0) := by
    rw [continuousOn_iff_continuous_restrict]
    have h2 : Continuous (Function.uncurry fun (y : Set.Ioi (0 : ℝ)) (t : ℝ) => K t y) := by
      refine hc.comp_continuous (f := fun p : Set.Ioi (0 : ℝ) × ℝ => (p.2, (p.1 : ℝ))) (by fun_prop) fun p => ⟨Set.mem_univ _, p.1.2⟩
    exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' h2 0 T
  have hfb : ∀ y : ℝ, 0 < y → ‖∫ t in (0 : ℝ)..T, K t y‖ ≤ (B * T) * wr k r y := by
    intro y y0
    have := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := T) (f := fun t => K t y) (C := B * wr k r y)
      fun t ht => hB t (by rw [Set.uIoc_of_le hT] at ht; exact ⟨ht.1.le, ht.2⟩) y y0
    rw [sub_zero, abs_of_nonneg hT] at this
    linarith
  have hfO : ∀ l : Filter ℝ, (∀ᶠ y in l, 0 < y) → (fun y => ∫ t in (0 : ℝ)..T, K t y) =O[l] wr k r := fun l hl =>
    Asymptotics.IsBigO.of_bound (B * T) (hl.mono fun y y0 => by
      rw [Real.norm_of_nonneg (wr_pos k r y0).le]; exact hfb y y0)
  refine ⟨fun t ht => ?_, ?_, ?_, ?_⟩
  · refine Integrable.mono' (Integrable.const_mul hW B) ?_ ?_
    · refine ContinuousOn.aestronglyMeasurable (ContinuousOn.mul ?_ hpw) measurableSet_Ioi
      exact hc.comp (f := fun y : ℝ => (t, y)) (by fun_prop) fun y hy => ⟨Set.mem_univ _, hy⟩
    · rw [ae_restrict_iff' measurableSet_Ioi]
      exact Eventually.of_forall fun y hy => hbd t ht y hy
  · rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hT]
    exact hP.integral_prod_left
  · rw [intervalIntegral.integral_of_le hT, mellin]
    have sw := integral_integral_swap (f := fun (t y : ℝ) => K t y * (y : ℂ) ^ c) hP
    rw [sw]
    refine setIntegral_congr_fun measurableSet_Ioi fun y _ => ?_
    have e : s - 1 - 1 = c := by rw [hcdef]; ring
    simp only [e, smul_eq_mul, intervalIntegral.integral_of_le hT]
    rw [integral_mul_const, mul_comm]
  · exact mellin_differentiableAt_of_isBigO_rpow (a := (s - 1).re + 1) (b := -(k : ℝ))
      (hf.locallyIntegrableOn measurableSet_Ioi)
      ((hfO _ (eventually_gt_atTop 0)).trans (wr_top k r _ (by linarith))) (by linarith)
      ((hfO _ self_mem_nhdsWithin).trans (wr_bot k r)) hbot

private theorem split_int {Φ : ℝ → ℂ} (h1 : IntegrableOn Φ (Set.Ioi 0)) (h2 : IntegrableOn (fun y => Φ (-y)) (Set.Ioi 0)) :
    ∫ y, Φ y = (∫ y in Set.Ioi (0 : ℝ), Φ y) + ∫ y in Set.Ioi (0 : ℝ), Φ (-y) := by
  have hL : IntegrableOn Φ (Set.Iic 0) := by
    rw [integrableOn_Iic_iff_integrableOn_Iio]
    have h3 := (Measure.measurePreserving_neg (volume : Measure ℝ)).integrableOn_comp_preimage
      (MeasurableEquiv.neg ℝ).measurableEmbedding (f := Φ) (s := Set.Iio 0)
    refine h3.1 ?_
    have e : (Neg.neg : ℝ → ℝ) ⁻¹' Set.Iio 0 = Set.Ioi 0 := by ext y; simp
    rw [e]
    exact h2
  have e := integral_comp_neg_Ioi (0 : ℝ) Φ
  rw [e, neg_zero, add_comm, intervalIntegral.integral_Iic_add_Ioi hL h1]

private theorem two_side {T : ℝ} (hT : 0 ≤ T) (k : ℕ) {q : ℝ → ℂ} (hq : Continuous q) {H : ℝ → ℝ → ℂ}
    (hc : ContinuousOn (Function.uncurry H) (Set.univ ×ˢ {0}ᶜ))
    (hb : ∀ r : ℕ, ∃ B : ℝ, ∀ t ∈ Set.Icc 0 T, ∀ y : ℝ, y ≠ 0 → ‖H t y‖ ≤ B * ((1 + |y|) ^ r)⁻¹) :
    DifferentiableOn ℂ (fun s : ℂ => ∫ t in (0 : ℝ)..T, q t * ∫ y : ℝ, H t y * (y : ℂ) ^ k * ((|y| : ℝ) : ℂ) ^ (s - 2))
      {s | 1 - (k : ℝ) < s.re} := by
  obtain ⟨Q, hQ⟩ := isCompact_Icc.exists_bound_of_continuousOn (s := Set.Icc 0 T) hq.continuousOn
  have hQ0 : 0 ≤ Q := (norm_nonneg _).trans (hQ 0 ⟨le_rfl, hT⟩)
  set Kp : ℝ → ℝ → ℂ := fun t y => q t * H t y * (y : ℂ) ^ k with hKp
  set Km : ℝ → ℝ → ℂ := fun t y => q t * H t (-y) * ((-y : ℝ) : ℂ) ^ k with hKm
  have hcp : ContinuousOn (Function.uncurry Kp) (Set.univ ×ˢ Set.Ioi 0) := by
    refine ContinuousOn.mul (ContinuousOn.mul ?_ ?_) ?_
    · exact (hq.comp continuous_fst).continuousOn
    · exact hc.mono fun p hp => ⟨Set.mem_univ _, ne_of_gt hp.2⟩
    · exact (Continuous.pow (Complex.continuous_ofReal.comp continuous_snd) k).continuousOn
  have hcm : ContinuousOn (Function.uncurry Km) (Set.univ ×ˢ Set.Ioi 0) := by
    refine ContinuousOn.mul (ContinuousOn.mul ?_ ?_) ?_
    · exact (hq.comp continuous_fst).continuousOn
    · refine hc.comp (f := fun p : ℝ × ℝ => (p.1, -p.2)) (by fun_prop) fun p hp => ⟨Set.mem_univ _, ?_⟩
      have : (0 : ℝ) < p.2 := hp.2
      simpa using this.ne'
    · exact (Continuous.pow (Complex.continuous_ofReal.comp continuous_snd.neg) k).continuousOn
  have hbound : ∀ (r : ℕ) (B : ℝ), (∀ t ∈ Set.Icc 0 T, ∀ y : ℝ, y ≠ 0 → ‖H t y‖ ≤ B * ((1 + |y|) ^ r)⁻¹) →
      ∀ t ∈ Set.Icc 0 T, ∀ y y' : ℝ, 0 < y → |y'| = y → ‖q t * H t y' * (y' : ℂ) ^ k‖ ≤ Q * B * wr k r y := by
    intro r B hB t ht y y' y0 hy
    have hy' : y' ≠ 0 := by rintro rfl; simp at hy; exact y0.ne hy
    have h1 := hB t ht y' hy'
    rw [hy] at h1
    rw [norm_mul, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, hy]
    calc ‖q t‖ * ‖H t y'‖ * y ^ k ≤ Q * (B * ((1 + y) ^ r)⁻¹) * y ^ k :=
          mul_le_mul_of_nonneg_right (mul_le_mul (hQ t ht) h1 (norm_nonneg _) hQ0) (by positivity)
      _ = _ := by unfold wr; ring
  have hbp : ∀ r : ℕ, ∃ B : ℝ, ∀ t ∈ Set.Icc 0 T, ∀ y, 0 < y → ‖Kp t y‖ ≤ B * wr k r y := fun r => by
    obtain ⟨B, hB⟩ := hb r
    exact ⟨Q * B, fun t ht y y0 => hbound r B hB t ht y y y0 (abs_of_pos y0)⟩
  have hbm : ∀ r : ℕ, ∃ B : ℝ, ∀ t ∈ Set.Icc 0 T, ∀ y, 0 < y → ‖Km t y‖ ≤ B * wr k r y := fun r => by
    obtain ⟨B, hB⟩ := hb r
    exact ⟨Q * B, fun t ht y y0 => hbound r B hB t ht y (-y) y0 (by rw [abs_neg, abs_of_pos y0])⟩
  have op := fun {s : ℂ} (hs : 1 - (k : ℝ) < s.re) => one_side hT k hcp hbp hs
  have om := fun {s : ℂ} (hs : 1 - (k : ℝ) < s.re) => one_side hT k hcm hbm hs
  have hd : DifferentiableOn ℂ (fun s : ℂ => mellin (fun y => ∫ t in (0 : ℝ)..T, Kp t y) (s - 1) +
      mellin (fun y => ∫ t in (0 : ℝ)..T, Km t y) (s - 1)) {s | 1 - (k : ℝ) < s.re} := fun s hs => by
    have h1 : DifferentiableAt ℂ (fun s : ℂ => s - 1) s := differentiableAt_id.sub_const 1
    exact (DifferentiableAt.add (DifferentiableAt.comp s (op hs).2.2.2 h1)
      (DifferentiableAt.comp s (om hs).2.2.2 h1)).differentiableWithinAt
  refine hd.congr fun s hs => ?_
  obtain ⟨ip, iip, ep, -⟩ := op hs
  obtain ⟨im, iim, em', -⟩ := om hs
  rw [← ep, ← em', ← intervalIntegral.integral_add iip iim]
  refine intervalIntegral.integral_congr fun t ht => ?_
  rw [Set.uIcc_of_le hT] at ht
  have e1 : ∀ y : ℝ, y ∈ Set.Ioi (0 : ℝ) → Kp t y * (y : ℂ) ^ (s - 2) =
      q t * (H t y * (y : ℂ) ^ k * ((|y| : ℝ) : ℂ) ^ (s - 2)) := fun y hy => by
    have y0 : (0 : ℝ) < y := hy
    rw [abs_of_pos y0, hKp]; ring
  have e2 : ∀ y : ℝ, y ∈ Set.Ioi (0 : ℝ) → Km t y * (y : ℂ) ^ (s - 2) =
      q t * (H t (-y) * ((-y : ℝ) : ℂ) ^ k * ((|-y| : ℝ) : ℂ) ^ (s - 2)) := fun y hy => by
    have y0 : (0 : ℝ) < y := hy
    rw [abs_neg, abs_of_pos y0, hKm]; ring
  have i1 := IntegrableOn.congr_fun (ip t ht) e1 measurableSet_Ioi
  have i2 := IntegrableOn.congr_fun (im t ht) e2 measurableSet_Ioi
  show q t * _ = _
  rw [← integral_const_mul, split_int (Φ := fun y : ℝ => q t * (H t y * (y : ℂ) ^ k * ((|y| : ℝ) : ℂ) ^ (s - 2))) i1 i2,
    setIntegral_congr_fun measurableSet_Ioi e1, setIntegral_congr_fun measurableSet_Ioi e2]

variable {E : Type} [Field E] [NumberField E]

private theorem cont_em : Continuous (em E) :=
  Continuous.units_map _ (continuous_id.matrix_map AdeleBaseChange.continuous_adeleMap)

private theorem cont_infGL2 : Continuous (TR.infGL ℚ 2) :=
  Continuous.units_map _ (continuous_const.add (continuous_id.matrix_map
    ((TR.continuous_infEq ℚ).prodMk continuous_const :
    Continuous fun x : TR.Rinf ℚ => ((TR.infEq ℚ x, 0) : InfiniteAdeleRing ℚ × Af ℚ))))

private theorem cont_toGL {f : ℝ → Matrix.SpecialLinearGroup (Fin 2) (TR.Rinf ℚ)} (hf : ∀ i j, Continuous fun t => (f t).1 i j) :
    Continuous fun t => Matrix.SpecialLinearGroup.toGL (f t) := by
  have e : ∀ g : Matrix.SpecialLinearGroup (Fin 2) (TR.Rinf ℚ),
      (((Matrix.SpecialLinearGroup.toGL g)⁻¹ : GL (Fin 2) (TR.Rinf ℚ)) : Matrix (Fin 2) (Fin 2) (TR.Rinf ℚ)) = (g⁻¹).1 := fun g => by
    rw [← map_inv]; rfl
  refine Units.continuous_iff.2 ⟨continuous_matrix hf, continuous_matrix fun i j => ?_⟩
  refine (?_ : Continuous fun t => ((f t)⁻¹).1 i j).congr fun t => (congrFun (congrFun (e (f t)) i) j).symm
  simp only [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two]
  fin_cases i <;> fin_cases j <;> simp <;> first | exact hf _ _ | exact (hf _ _).neg

private theorem cont_rot : Continuous rot := by
  refine cont_infGL2.comp (cont_toGL fun i j => ?_)
  fin_cases i <;> fin_cases j <;> simp <;> fun_prop

private theorem cont_iy : ContinuousOn iy {0}ᶜ := by
  rw [continuousOn_iff_continuous_restrict]
  have h : Continuous fun y : ({0}ᶜ : Set ℝ) => (⟨fun _ => (y : ℝ), fun _ => (y : ℝ)⁻¹, funext fun _ => mul_inv_cancel₀ y.2,
      funext fun _ => inv_mul_cancel₀ y.2⟩ : (TR.Rinf ℚ)ˣ) := by
    refine Units.continuous_iff.2 ⟨continuous_pi fun _ => continuous_subtype_val, continuous_pi fun _ => ?_⟩
    exact continuous_subtype_val.inv₀ fun y => y.2
  refine ((TR.continuous_infId ℚ).comp h).congr fun y => ?_
  change _ = iy y.1
  rw [iy, dif_neg (show (y : ℝ) ≠ 0 from y.2)]
  rfl

private theorem re_iy {y : ℝ} (hy : y ≠ 0) : re (iy y : A ℚ) = y := by
  have h : ∀ x, TR.pInf ℚ (TR.sInf ℚ x) = x := fun x => (TR.infEq ℚ).symm_apply_apply x
  rw [re, iy, dif_neg hy]
  change TR.pInf ℚ (1 - TR.sInf ℚ 1 + TR.sInf ℚ _) _ = y
  simp [h]

private theorem cont_Wo (D : Dat ℚ E) {φ : GL (Fin 2) (A E) → ℂ} (hc : Continuous φ) (hb : ∃ B : ℝ, ∀ g, ‖φ g‖ ≤ B)
    {X : Type} [TopologicalSpace X] [FirstCountableTopology X] {h : X → GL (Fin 2) (A E)} (hh : Continuous h) :
    Continuous fun x => Wo D φ (h x) := by
  obtain ⟨B, hB⟩ := hb
  obtain ⟨C, hC, hEC⟩ : ∃ C, IsCompact C ∧ fundamentalSet ℚ ⊆ C :=
    ⟨closure (fundamentalSetInfinite ℚ) ×ˢ _,
      (isCompact_closure_fundamentalSetInfinite ℚ).prod (isCompact_integralFiniteAdeles ℚ),
      fun x hx => ⟨subset_closure hx.1, hx.2⟩⟩
  have hCp : IsCompact (Set.univ.pi fun _ : Fin 2 => C) := isCompact_univ_pi fun _ => hC
  have hfin : adeleMeasurePi ℚ (FS2 ℚ) < ⊤ :=
    (measure_mono (show FS2 ℚ ⊆ Set.univ.pi fun _ : Fin 2 => C from fun x hx i hi => hEC (hx i hi))).trans_lt hCp.measure_lt_top
  haveI : IsFiniteMeasure ((adeleMeasurePi ℚ).restrict (FS2 ℚ)) := ⟨by simpa using hfin⟩
  have hn : Continuous fun u : Fin 2 → A ℚ => nE D u :=
    continuous_gl.comp (continuous_nU.comp ((AdeleBaseChange.continuous_adeleMap.comp (continuous_apply 0)).add
      ((AdeleBaseChange.continuous_adeleMap.comp (continuous_apply 1)).mul continuous_const)))
  have hψ : Continuous fun u : Fin 2 → A ℚ => ψ (u 1) := continuous_ψ.comp (continuous_apply 1)
  refine continuous_of_dominated (bound := fun _ => B) (fun x => ?_) (fun x => ?_) (integrable_const _) ?_
  · exact ((hc.comp (hn.mul continuous_const)).mul hψ).aestronglyMeasurable
  · refine Eventually.of_forall fun u => ?_
    rw [norm_mul, norm_ψ, mul_one]
    exact hB _
  · refine Eventually.of_forall fun u => ?_
    exact (hc.comp (continuous_const.mul hh)).mul continuous_const

private theorem norm_chi {ω χ : HChar ℚ} (hω : Unit1 ω) (h : ∀ a, (χ.1 a * ω.1 a) ^ 2 = 1) (a : (A ℚ)ˣ) :
    ‖((χ.1 a : ℂˣ) : ℂ)‖ = 1 := by
  have h1 := congrArg (fun u : ℂˣ => ‖(u : ℂ)‖) (h a)
  simp only [Units.val_pow_eq_pow_val, Units.val_mul, norm_pow, norm_mul, Units.val_one, norm_one, hω a, mul_one] at h1
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).1 h1

end UpperTheory.ConvolutionTheory.RankTwoDescent

open UpperTheory.ConvolutionTheory.RankTwoDescent

theorem UpperTheory.ConvolutionTheory.RankTwoDescent.hol_of :
    Hol := by
  intro E _ _ _ D P ω χ hcen hω hsq k φ p hA
  have hq : Continuous fun t : ℝ => MvPolynomial.eval ![(Real.sin t : ℂ), (Real.cos t : ℂ)] p := by
    refine (MvPolynomial.continuous_eval p).comp (continuous_pi fun i => ?_)
    fin_cases i <;> simp <;> fun_prop
  refine two_side (T := 2 * Real.pi) (by positivity) k hq
    (H := fun t y => Wo D φ (em E (aE (iy y) * rot t)) * ((χ.1 (iy y) : ℂˣ) : ℂ)) ?_ ?_
  · rw [continuousOn_iff_continuous_restrict]
    have hi : Continuous fun x : ↥((Set.univ ×ˢ {0}ᶜ : Set (ℝ × ℝ))) => iy x.1.2 :=
      cont_iy.comp_continuous (continuous_snd.comp continuous_subtype_val) fun x => x.2.2
    have hr : Continuous fun x : ↥((Set.univ ×ˢ {0}ᶜ : Set (ℝ × ℝ))) => rot x.1.1 :=
      cont_rot.comp (continuous_fst.comp continuous_subtype_val)
    have hh : Continuous fun x : ↥((Set.univ ×ˢ {0}ᶜ : Set (ℝ × ℝ))) => em E (aE (iy x.1.2) * rot x.1.1) :=
      cont_em.comp ((continuous_aE.comp hi).mul hr)
    exact (cont_Wo D hA.cont hA.bdd hh).mul (Units.continuous_val.comp (χ.2.1.comp hi))
  · intro r
    have hC : IsCompact ((fun t => em E (rot t)) '' Set.Icc 0 (2 * Real.pi)) :=
      isCompact_Icc.image (cont_em.comp cont_rot)
    obtain ⟨K, -, hK⟩ := hA.wdec _ hC
    obtain ⟨B, hB⟩ := hK r
    refine ⟨B, fun t ht y hy => ?_⟩
    have h1 := (hB (iy y) (em E (rot t)) ⟨t, ht, rfl⟩).1
    rw [re_iy hy, ← map_mul] at h1
    rw [norm_mul, norm_chi hω hsq, mul_one]
    exact h1

end
