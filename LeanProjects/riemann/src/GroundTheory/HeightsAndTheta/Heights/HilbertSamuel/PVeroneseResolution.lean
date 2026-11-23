import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsSecondVeroneseParts
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.BergmanProjectiveVolume
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.AnForm.M MeasureTheory Set
  GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.CP

noncomputable section

namespace VeroneseResolution

variable {D : ℕ}

def ix (a b : Fin (D + 1)) : Ix (Veronese.Idx D) := ⟨(), ⟨(min a b, max a b), min_le_max⟩⟩

theorem map_ix (w : Fin (D + 1) → ℂ) (a b : Fin (D + 1)) : Veronese.map D w (ix a b) = w a * w b := by
  rcases le_total a b with h | h
  · simp [Veronese.map, ix, min_eq_left h, max_eq_right h]
  · simp [Veronese.map, ix, min_eq_right h, max_eq_left h, mul_comm]

theorem x_ix (a b : Fin (D + 1)) : Veronese.x D (ix a b) = Veronese.t D a * Veronese.t D b := by
  rcases le_total a b with h | h
  · simp [Veronese.x, ix, min_eq_left h, max_eq_right h]
  · simp [Veronese.x, ix, min_eq_right h, max_eq_left h, mul_comm]

theorem ix_self (q : Ix (Veronese.Idx D)) : ix q.2.1.1 q.2.1.2 = q := by
  obtain ⟨⟨⟩, ⟨⟨a, b⟩, h⟩⟩ := q
  simp [ix, min_eq_left h, max_eq_right h]

theorem map_smul (s : ℂ) (v : Fin (D + 1) → ℂ) :
    Veronese.map D (s • v) = (s ^ 2) • Veronese.map D v := by
  funext q
  simp only [Veronese.map, Pi.smul_apply, smul_eq_mul]
  ring

def subst (f : MvPolynomial (Ix (Veronese.Idx D)) ℤ) : MvPolynomial (Fin (D + 1)) ℚ :=
  eval₂ (Int.castRingHom _) (fun q => X q.2.1.1 * X q.2.1.2) f

theorem algebraMap_subst (f : MvPolynomial (Ix (Veronese.Idx D)) ℤ) :
    algebraMap (MvPolynomial (Fin (D + 1)) ℚ) (Veronese.Fld D) (subst f) =
      Polynomial.eval 1 (coneMap ℤ (Veronese.x D) f) := by
  induction f using MvPolynomial.induction_on with
  | C a =>
    rw [subst, eval₂_C]
    simp [coneMap]
  | add p q hp hq => simp only [subst, eval₂_add, map_add, Polynomial.eval_add] at hp hq ⊢; rw [hp, hq]
  | mul_X p n hp =>
    simp only [subst, eval₂_mul, eval₂_X, map_mul, Polynomial.eval_mul] at hp ⊢
    rw [hp]
    simp [coneMap, Veronese.x, Veronese.t]

theorem eval_veronese (w : Fin (D + 1) → ℂ) (f : MvPolynomial (Ix (Veronese.Idx D)) ℤ) :
    eval (Veronese.map D w) (MvPolynomial.map (Int.castRingHom ℂ) f) = eval₂ (algebraMap ℚ ℂ) w (subst f) := by
  induction f using MvPolynomial.induction_on with
  | C a =>
    rw [subst, eval₂_C, eq_intCast, ← coe_eval₂Hom, map_intCast]
    simp
  | add p q hp hq => simp only [subst, eval₂_add, map_add] at hp hq ⊢; rw [hp, hq]
  | mul_X p n hp =>
    simp only [subst, eval₂_mul, eval₂_X, map_mul, map_X, eval_X] at hp ⊢
    rw [hp]
    rfl

theorem subst_eq_zero {f : MvPolynomial (Ix (Veronese.Idx D)) ℤ} (hf : f ∈ coordIdeal ℤ (Veronese.x D)) :
    subst f = 0 := by
  have h0 : coneMap ℤ (Veronese.x D) f = 0 := hf
  apply IsFractionRing.injective (MvPolynomial (Fin (D + 1)) ℚ) (Veronese.Fld D)
  rw [algebraMap_subst, h0, map_zero, Polynomial.eval_zero]

theorem eval_veronese_eq_zero (w : Fin (D + 1) → ℂ) {f : MvPolynomial (Ix (Veronese.Idx D)) ℤ}
    (hf : f ∈ coordIdeal ℤ (Veronese.x D)) :
    eval (Veronese.map D w) (MvPolynomial.map (Int.castRingHom ℂ) f) = 0 := by
  rw [eval_veronese, subst_eq_zero hf, eval₂_zero]

theorem one_not_mem : (1 : MvPolynomial (Ix (Veronese.Idx D)) ℤ) ∉ coordIdeal ℤ (Veronese.x D) := by
  intro h
  have := eval_veronese_eq_zero 0 h
  simp at this

theorem mcPts_top_eq : mcPts (ι := GlobalTheory (Veronese.Idx D)) ⊤ = ∅ := by
  ext z
  simp only [mcPts, mem_ofPred_eq, Submodule.mem_top, mem_empty_iff_false, iff_false, not_and]
  intro _ h
  have := h 1 trivial
  simp at this

def quad (a b c d : Fin (D + 1)) : MvPolynomial (Ix (Veronese.Idx D)) ℤ :=
  X (ix a b) * X (ix c d) - X (ix a c) * X (ix b d)

theorem quad_mem (a b c d : Fin (D + 1)) : quad a b c d ∈ coordIdeal ℤ (Veronese.x D) := by
  change coneMap ℤ (Veronese.x D) (quad a b c d) = 0
  simp only [quad, coneMap, map_sub, map_mul, aeval_X, x_ix]
  ring

theorem quad_rel {z : Ix (Veronese.Idx D) → ℂ}
    (hz : ∀ f ∈ coordIdeal ℤ (Veronese.x D), eval z (MvPolynomial.map (Int.castRingHom ℂ) f) = 0)
    (a b c d : Fin (D + 1)) : z (ix a b) * z (ix c d) = z (ix a c) * z (ix b d) := by
  have := hz _ (quad_mem a b c d)
  simp only [quad, map_sub, map_mul, map_X, eval_X] at this
  exact sub_eq_zero.mp this

theorem chartVec_chartCoord_mk (i : Fin (D + 1)) (v : Fin (D + 1) → ℂ) (hv : v ≠ 0) (hvi : v i ≠ 0) :
    chartVec i (chartCoord i (Projectivization.mk ℂ v hv)) = (v i)⁻¹ • v := by
  rw [chartCoord_mk]
  funext m
  obtain rfl | ⟨k, rfl⟩ := Fin.eq_self_or_eq_succAbove i m
  · simp [hvi]
  · simp [div_eq_inv_mul]

theorem rep_apply_ne_zero {i : Fin (D + 1)} {y : CP D} (hy : y ∈ chartDomain i) : y.rep i ≠ 0 := by
  rw [← Projectivization.mk_rep y] at hy
  exact (mk_mem_chartDomain i _ _).1 hy

theorem chartVec_chartCoord_rep {i : Fin (D + 1)} {y : CP D} (hy : y ∈ chartDomain i) :
    chartVec i (chartCoord i y) = (y.rep i)⁻¹ • y.rep := by
  conv_lhs => rw [← Projectivization.mk_rep y]
  exact chartVec_chartCoord_mk i _ _ (rep_apply_ne_zero hy)

def lift (p y : CP D) : Ix (Veronese.Idx D) → ℂ :=
  Veronese.map D (chartVec (chartIndex p) (chartCoord (chartIndex p) y))

theorem lift_eq {p y : CP D} (hy : y ∈ chartDomain (chartIndex p)) :
    lift p y = ((y.rep (chartIndex p))⁻¹ ^ 2) • Veronese.map D y.rep := by
  rw [lift, chartVec_chartCoord_rep hy, map_smul]

theorem lift_ne_zero (p y : CP D) : lift p y ⟨(), ⟨(chartIndex p, chartIndex p), le_rfl⟩⟩ ≠ 0 := by
  simp [lift, Veronese.map]

theorem holo_lift (p : CP D) (q : Ix (Veronese.Idx D)) :
    (projAtlas D).HoloOn (chartDomain (chartIndex p)) (fun y => lift p y q) := by
  intro j z hz
  set i := chartIndex p
  have hzi : chartVec j z i ≠ 0 := hz.2
  have hf : AnalyticAt ℂ (fun w : Fin D → ℂ =>
      (chartVec j w i)⁻¹ * chartVec j w q.2.1.1 * ((chartVec j w i)⁻¹ * chartVec j w q.2.1.2)) z :=
    ((((ProjFS.analyticAt_chartVec_apply j i z).inv hzi).mul (ProjFS.analyticAt_chartVec_apply j _ z)).mul
      (((ProjFS.analyticAt_chartVec_apply j i z).inv hzi).mul (ProjFS.analyticAt_chartVec_apply j _ z)))
  refine hf.congr ?_
  filter_upwards [ProjFS.eventually_chartVec_ne hzi] with w hw
  change _ = Veronese.map D (chartVec i (chartCoord i (chartInv j w))) q
  rw [ProjFS.chartVec_chartCoord_chartInv hw]
  rfl

def res (D : ℕ) : AnRes (ι := GlobalTheory (Veronese.Idx D)) (coordIdeal ℤ (Veronese.x D)) ⊤ D where
  homog := ⟨{1}, fun f hf => ⟨0, by
      rw [mem_singleton_iff.mp hf]
      intro m hm k
      rw [support_one, Finset.mem_singleton] at hm
      simp [hm]⟩, Ideal.span_singleton_one.symm⟩
  nondeg h := one_not_mem (h Submodule.mem_top)
  X := CP D
  A := projAtlas D
  U p := chartDomain (chartIndex p)
  isOpen_U _ := isOpen_chartDomain _
  mem_U p := mem_chartDomain_chartIndex p
  lift := lift
  holo := holo_lift
  mem p y _ := ⟨fun _ => ⟨⟨(chartIndex p, chartIndex p), le_rfl⟩, lift_ne_zero p y⟩,
    fun _ hf => eval_veronese_eq_zero _ hf⟩
  compat p p' y hy := by
    refine ⟨fun _ => ((y.rep (chartIndex p))⁻¹ ^ 2) / ((y.rep (chartIndex p'))⁻¹ ^ 2),
      fun _ => div_ne_zero (pow_ne_zero _ (inv_ne_zero (rep_apply_ne_zero hy.1)))
        (pow_ne_zero _ (inv_ne_zero (rep_apply_ne_zero hy.2))), ?_⟩
    rw [lift_eq hy.1, lift_eq hy.2]
    funext q
    have h1 : y.rep (chartIndex p) ≠ 0 := rep_apply_ne_zero hy.1
    have h2 : y.rep (chartIndex p') ≠ 0 := rep_apply_ne_zero hy.2
    simp only [Pi.smul_apply, smul_eq_mul]
    field_simp
  surj z hz _ := by
    obtain ⟨qi, hq0⟩ := hz.1 ()
    have rel := quad_rel hz.2

    obtain ⟨a, ha⟩ : ∃ a, z (ix a a) ≠ 0 := by
      set q : Ix (Veronese.Idx D) := ⟨(), qi⟩
      have hzq : z (ix q.2.1.1 q.2.1.2) ≠ 0 := by rw [ix_self]; exact hq0
      refine ⟨q.2.1.1, fun h0 => hzq ?_⟩
      have := rel q.2.1.1 q.2.1.2 q.2.1.1 q.2.1.2
      rw [h0, zero_mul] at this
      exact mul_self_eq_zero.mp this
    set w : Fin (D + 1) → ℂ := fun j => z (ix a j) with hw
    have hw0 : w ≠ 0 := fun h => ha (congrFun h a)
    have hmap : Veronese.map D w = z (ix a a) • z := by
      funext q
      rw [← ix_self q, map_ix, Pi.smul_apply, smul_eq_mul]
      exact rel a q.2.1.1 a q.2.1.2
    set p := Projectivization.mk ℂ w hw0
    have hp : p ∈ chartDomain (chartIndex p) := mem_chartDomain_chartIndex p
    have hwi : w (chartIndex p) ≠ 0 := hp
    refine ⟨p, fun _ => (w (chartIndex p))⁻¹ ^ 2 * z (ix a a),
      fun _ => mul_ne_zero (pow_ne_zero _ (inv_ne_zero hwi)) ha, ?_⟩
    change Veronese.map D (chartVec (chartIndex p) (chartCoord (chartIndex p) p)) = _
    rw [chartVec_chartCoord_mk _ w hw0 hwi, map_smul, hmap]
    funext q
    simp only [Pi.smul_apply, smul_eq_mul]
    ring
  inj p p' _ h := by
    obtain ⟨c, hc, hcz⟩ := h
    rw [lift_eq (mem_chartDomain_chartIndex p), lift_eq (mem_chartDomain_chartIndex p')] at hcz
    set v := p.rep
    set v' := p'.rep
    have hv : v (chartIndex p) ≠ 0 := rep_apply_ne_zero (mem_chartDomain_chartIndex p)
    have hv' : v' (chartIndex p') ≠ 0 := rep_apply_ne_zero (mem_chartDomain_chartIndex p')

    set e : ℂ := (v (chartIndex p))⁻¹⁻¹ ^ 2 * c () * (v' (chartIndex p'))⁻¹ ^ 2 with he
    have he0 : e ≠ 0 := by
      simp only [he]
      exact mul_ne_zero (mul_ne_zero (pow_ne_zero _ (inv_ne_zero (inv_ne_zero hv))) (hc ()))
        (pow_ne_zero _ (inv_ne_zero hv'))
    have hab : ∀ a b, v a * v b = e * (v' a * v' b) := by
      intro a b
      have := congrFun hcz (ix a b)
      simp only [Pi.smul_apply, smul_eq_mul, map_ix] at this
      rw [he]
      field_simp at this ⊢
      linear_combination this
    set a := chartIndex p
    have hva' : v' a ≠ 0 := by
      intro h0
      have := hab a a
      rw [h0, zero_mul, mul_zero] at this
      exact hv (mul_self_eq_zero.mp this)
    rw [← Projectivization.mk_rep p, ← Projectivization.mk_rep p', Projectivization.mk_eq_mk_iff']
    refine ⟨v a / v' a, ?_⟩
    funext b
    simp only [Pi.smul_apply, smul_eq_mul]
    have h1 := hab a b
    have h2 := hab a a
    rw [div_mul_eq_mul_div, div_eq_iff hva']
    apply mul_left_cancel₀ hv
    linear_combination v' b * h2 - v' a * h1
  null j := by
    have : {x : CP D | lift x x ∈ mcPts (ι := GlobalTheory (Veronese.Idx D)) ⊤} = ∅ := by
      rw [mcPts_top_eq]; rfl
    change volume (_ ∩ chartInv j ⁻¹' {x : CP D | lift x x ∈ mcPts (ι := GlobalTheory (Veronese.Idx D)) ⊤}) = 0
    rw [this, preimage_empty, inter_empty, measure_empty]

theorem isSmoothVolume_fs (D : ℕ) : IsSmoothVolume (projAtlas D) (fsMeasure D) := by
  refine ⟨inferInstance, fun j => ⟨fsVolumeDensity j, (fsVolume D).smooth j,
    fun y _ => fsVolumeDensity_pos j y, fun S hS hsub => ?_⟩⟩
  have hsub' : S ⊆ chartDomain (N := D) j := hsub
  change fsMeasure D S = ∫⁻ y in univ ∩ chartInv j ⁻¹' S, ENNReal.ofReal (fsVolumeDensity j y)
  rw [univ_inter]
  have h := ProjFS.setLIntegral_fsMeasure_chartDomain (N := D) j (S.indicator 1) (measurable_one.indicator hS)
  rw [lintegral_indicator_one hS, Measure.restrict_apply hS, inter_eq_left.mpr hsub'] at h
  rw [h, ← lintegral_indicator ((measurable_chartInv j) hS)]
  congr 1
  funext y
  by_cases hy : chartInv j y ∈ S
  · have hy' : y ∈ chartInv j ⁻¹' S := hy
    rw [indicator_of_mem hy, indicator_of_mem hy', Pi.one_apply, one_mul]
  · have hy' : y ∉ chartInv j ⁻¹' S := hy
    rw [indicator_of_notMem hy, indicator_of_notMem hy', zero_mul]

theorem lift_self_eq (p : CP D) :
    lift p p = ((p.rep (chartIndex p))⁻¹ ^ 2) • Veronese.map D p.rep :=
  lift_eq (mem_chartDomain_chartIndex p)

end VeroneseResolution

open VeroneseResolution in

theorem VeroneseResolution.proof : VeroneseResolution.Statement := by
  intro D _
  refine ⟨⊤, res D, CP.instMeasurableSpace, CP.instBorelSpace, fsMeasure D, isSmoothVolume_fs D,
    fun g hg => ?_⟩
  have key : ∀ p : CP D, g (lift p p) = g (Veronese.map D p.rep) := fun p => by
    rw [lift_self_eq p]
    exact hg _ _ (pow_ne_zero _ (inv_ne_zero (rep_apply_ne_zero (mem_chartDomain_chartIndex p))))
  exact integral_congr_ae (Filter.Eventually.of_forall key)

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
