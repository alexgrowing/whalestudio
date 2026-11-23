import Mathlib
import GroundTheory.PAdicHodge.ExtRobbaBounded
import GroundTheory.PAdicHodge.RobbaNewton
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.PAdicHodge

namespace TeichLift

open Laurent Filter Topology UniformSpace

variable {p : ℕ} [hp : Fact p.Prime] {L : Type*} [NontriviallyNormedField L] [IsUltrametricDist L]
  [CharP L p] [PerfectRing L p] {Γ : Type*} [CommRing Γ] (T : TeichLift p L Γ)
  (ρ0 : Set.Ioo (0 : ℝ) 1)

theorem rad_pos (ρ : Set.Ioc (0 : ℝ) ρ0) : 0 < (ρ : ℝ) := ρ.2.1

theorem rad_lt_one (ρ : Set.Ioc (0 : ℝ) ρ0) : (ρ : ℝ) < 1 := lt_of_le_of_lt ρ.2.2 ρ0.2.2

theorem convergesAt_rad (b : T.Econ ρ0) (ρ : Set.Ioc (0 : ℝ) ρ0) :
    ConvergesAt (T.coeffB b) ρ :=
  convergesAt_of_le (T.coeffB_neg_exists _) b.2 ρ.2.1 ρ.2.2

def gaussSeminorm (ρ : Set.Ioc (0 : ℝ) ρ0) : RingSeminorm (T.Econ ρ0) where
  toFun b := gaussNorm (T.coeffB b) ρ
  map_zero' := by
    show gaussNorm (T.coeffB 0) ρ = 0
    rw [← map_zero (algebraMap Γ T.B), coeffB_algebraMap, (T.zcoeff_eq_zero_iff 0).2 rfl]
    simp [gaussNorm]
  add_le' b c :=
    (T.convergesAt_coeffB_add (rad_pos ρ0 ρ) (rad_lt_one ρ0 ρ) (T.convergesAt_rad ρ0 b ρ)
      (T.convergesAt_rad ρ0 c ρ)).2.trans
      (max_le_add_of_nonneg (gaussNorm_nonneg (rad_pos ρ0 ρ)) (gaussNorm_nonneg (rad_pos ρ0 ρ)))
  neg' b := (T.convergesAt_coeffB_neg (rad_pos ρ0 ρ) (rad_lt_one ρ0 ρ) (T.convergesAt_rad ρ0 b ρ)).2
  mul_le' b c := le_of_eq (T.convergesAt_coeffB_mul (rad_pos ρ0 ρ) (rad_lt_one ρ0 ρ)
    (T.convergesAt_rad ρ0 b ρ) (T.convergesAt_rad ρ0 c ρ)).2

theorem gaussSeminorm_apply (ρ : Set.Ioc (0 : ℝ) ρ0) (b : T.Econ ρ0) :
    T.gaussSeminorm ρ0 ρ b = gaussNorm (T.coeffB b) ρ := rfl

def uniformAt (ρ : Set.Ioc (0 : ℝ) ρ0) : UniformSpace (T.Econ ρ0) :=
  (T.gaussSeminorm ρ0 ρ).toSeminormedRing.toUniformSpace

instance instUniformSpaceEcon : UniformSpace (T.Econ ρ0) := ⨅ ρ, T.uniformAt ρ0 ρ

instance instIsUniformAddGroupEcon : IsUniformAddGroup (T.Econ ρ0) :=
  isUniformAddGroup_iInf fun ρ =>
    (T.gaussSeminorm ρ0 ρ).toAddGroupSeminorm.toSeminormedAddCommGroup.to_isUniformAddGroup

instance instIsTopologicalRingEcon : IsTopologicalRing (T.Econ ρ0) := by
  have hmul : ∀ ρ, @ContinuousMul (T.Econ ρ0) (T.uniformAt ρ0 ρ).toTopologicalSpace _ := fun ρ =>
    @NonUnitalSeminormedRing.toContinuousMul _
      (T.gaussSeminorm ρ0 ρ).toSeminormedRing.toNonUnitalSeminormedRing
  have h : ContinuousMul (T.Econ ρ0) := by
    have h := continuousMul_iInf (ts := fun ρ => (T.uniformAt ρ0 ρ).toTopologicalSpace) hmul
    have e : (⨅ ρ, T.uniformAt ρ0 ρ).toTopologicalSpace =
        ⨅ ρ, (T.uniformAt ρ0 ρ).toTopologicalSpace := UniformSpace.toTopologicalSpace_iInf
    exact e.symm ▸ h
  exact {}

abbrev RobbaExt := UniformSpace.Completion (T.Econ ρ0)

theorem uniformContinuous_gaussNorm (ρ : Set.Ioc (0 : ℝ) ρ0) :
    UniformContinuous (fun b : T.Econ ρ0 => gaussNorm (T.coeffB b) ρ) := by
  refine uniformContinuous_iInf_dom (i := ρ) ?_
  exact @uniformContinuous_norm _ (T.gaussSeminorm ρ0 ρ).toAddGroupSeminorm.toSeminormedAddCommGroup.toSeminormedAddGroup

def extNorm (ρ : Set.Ioc (0 : ℝ) ρ0) (x : T.RobbaExt ρ0) : ℝ :=
  Completion.extension (fun b : T.Econ ρ0 => gaussNorm (T.coeffB b) ρ) x

variable {ρ0}

theorem extNorm_coe (ρ : Set.Ioc (0 : ℝ) ρ0) (b : T.Econ ρ0) :
    T.extNorm ρ0 ρ b = gaussNorm (T.coeffB b) ρ :=
  Completion.extension_coe (T.uniformContinuous_gaussNorm ρ0 ρ) b

theorem continuous_extNorm (ρ : Set.Ioc (0 : ℝ) ρ0) : Continuous (T.extNorm ρ0 ρ) :=
  Completion.continuous_extension

theorem extNorm_nonneg (ρ : Set.Ioc (0 : ℝ) ρ0) (x : T.RobbaExt ρ0) : 0 ≤ T.extNorm ρ0 ρ x :=
  Completion.induction_on x (isClosed_le continuous_const (T.continuous_extNorm ρ))
    fun b => by rw [extNorm_coe]; exact gaussNorm_nonneg (rad_pos ρ0 ρ)

theorem extNorm_mul (ρ : Set.Ioc (0 : ℝ) ρ0) (x y : T.RobbaExt ρ0) :
    T.extNorm ρ0 ρ (x * y) = T.extNorm ρ0 ρ x * T.extNorm ρ0 ρ y :=
  Completion.induction_on₂ x y
    (isClosed_eq ((T.continuous_extNorm ρ).comp continuous_mul)
      (((T.continuous_extNorm ρ).comp continuous_fst).mul ((T.continuous_extNorm ρ).comp continuous_snd)))
    fun a b => by
      rw [← Completion.coe_mul, extNorm_coe, extNorm_coe, extNorm_coe]
      exact (T.convergesAt_coeffB_mul (rad_pos ρ0 ρ) (rad_lt_one ρ0 ρ) (T.convergesAt_rad ρ0 a ρ)
        (T.convergesAt_rad ρ0 b ρ)).2

theorem extNorm_add_le (ρ : Set.Ioc (0 : ℝ) ρ0) (x y : T.RobbaExt ρ0) :
    T.extNorm ρ0 ρ (x + y) ≤ max (T.extNorm ρ0 ρ x) (T.extNorm ρ0 ρ y) :=
  Completion.induction_on₂ x y
    (isClosed_le ((T.continuous_extNorm ρ).comp continuous_add)
      (((T.continuous_extNorm ρ).comp continuous_fst).max ((T.continuous_extNorm ρ).comp continuous_snd)))
    fun a b => by
      rw [← Completion.coe_add, extNorm_coe, extNorm_coe, extNorm_coe]
      exact (T.convergesAt_coeffB_add (rad_pos ρ0 ρ) (rad_lt_one ρ0 ρ) (T.convergesAt_rad ρ0 a ρ)
        (T.convergesAt_rad ρ0 b ρ)).2

theorem extNorm_neg (ρ : Set.Ioc (0 : ℝ) ρ0) (x : T.RobbaExt ρ0) :
    T.extNorm ρ0 ρ (-x) = T.extNorm ρ0 ρ x :=
  Completion.induction_on x
    (isClosed_eq ((T.continuous_extNorm ρ).comp continuous_neg) (T.continuous_extNorm ρ))
    fun a => by
      rw [← Completion.coe_neg, extNorm_coe, extNorm_coe]
      exact (T.convergesAt_coeffB_neg (rad_pos ρ0 ρ) (rad_lt_one ρ0 ρ) (T.convergesAt_rad ρ0 a ρ)).2

theorem extNorm_sub_comm (ρ : Set.Ioc (0 : ℝ) ρ0) (x y : T.RobbaExt ρ0) :
    T.extNorm ρ0 ρ (x - y) = T.extNorm ρ0 ρ (y - x) := by
  rw [← neg_sub, extNorm_neg]

theorem extNorm_one (ρ : Set.Ioc (0 : ℝ) ρ0) : T.extNorm ρ0 ρ 1 = 1 := by
  rw [← Completion.coe_one, extNorm_coe]
  show gaussNorm (T.coeffB 1) ρ = 1
  rw [← map_one (algebraMap Γ T.B), coeffB_algebraMap, zcoeff_one]
  refine le_antisymm (gaussNorm_single_zero_one_le (rad_pos ρ0 ρ)) ?_
  have := (convergesAt_pi_single (L := L) 0 1 ρ).le_gaussNorm 0
  simpa using this

theorem extNorm_zero (ρ : Set.Ioc (0 : ℝ) ρ0) : T.extNorm ρ0 ρ 0 = 0 := by
  rw [← Completion.coe_zero, extNorm_coe]
  exact map_zero (T.gaussSeminorm ρ0 ρ)

theorem extNorm_interp_le (ρ₁ ρ₂ ρ : Set.Ioc (0 : ℝ) ρ0) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hρ : (ρ : ℝ) = (ρ₁ : ℝ) ^ (1 - t) * (ρ₂ : ℝ) ^ t) (x : T.RobbaExt ρ0) :
    T.extNorm ρ0 ρ x ≤ T.extNorm ρ0 ρ₁ x ^ (1 - t) * T.extNorm ρ0 ρ₂ x ^ t :=
  Completion.induction_on x
    (isClosed_le (T.continuous_extNorm ρ)
      (((T.continuous_extNorm ρ₁).rpow_const fun _ => Or.inr (by linarith)).mul
        ((T.continuous_extNorm ρ₂).rpow_const fun _ => Or.inr ht0)))
    fun b => by
      rw [extNorm_coe, extNorm_coe, extNorm_coe, hρ]
      exact gaussNorm_interp_le (rad_pos ρ0 ρ₁) (rad_pos ρ0 ρ₂) (T.convergesAt_rad ρ0 b ρ₁)
        (T.convergesAt_rad ρ0 b ρ₂) ht0 ht1

theorem extNorm_le_max (ρ₁ ρ₂ ρ : Set.Ioc (0 : ℝ) ρ0) (h1 : (ρ₁ : ℝ) ≤ ρ) (h2 : (ρ : ℝ) ≤ ρ₂)
    (x : T.RobbaExt ρ0) :
    T.extNorm ρ0 ρ x ≤ max (T.extNorm ρ0 ρ₁ x) (T.extNorm ρ0 ρ₂ x) :=
  Completion.induction_on x
    (isClosed_le (T.continuous_extNorm ρ) ((T.continuous_extNorm ρ₁).max (T.continuous_extNorm ρ₂)))
    fun b => by
      rw [extNorm_coe, extNorm_coe, extNorm_coe]
      exact gaussNorm_le_max (rad_pos ρ0 ρ₁) h1 h2 (T.convergesAt_rad ρ0 b ρ₁)
        (T.convergesAt_rad ρ0 b ρ₂)

theorem exists_interp_exponent {a r b : ℝ} (ha : 0 < a) (har : a < r) (hrb : r < b) :
    ∃ t : ℝ, 0 < t ∧ t < 1 ∧ r = a ^ (1 - t) * b ^ t := by
  have hr : 0 < r := ha.trans har
  have hb : 0 < b := hr.trans hrb
  have h1 : Real.log a < Real.log r := Real.log_lt_log ha har
  have h2 : Real.log r < Real.log b := Real.log_lt_log hr hrb
  refine ⟨(Real.log r - Real.log a) / (Real.log b - Real.log a), ?_, ?_, ?_⟩
  · exact div_pos (by linarith) (by linarith)
  · rw [div_lt_one (by linarith)]; linarith
  · rw [Real.rpow_def_of_pos ha, Real.rpow_def_of_pos hb, ← Real.exp_add]
    have hne : Real.log b - Real.log a ≠ 0 := by linarith
    have : Real.log a * (1 - (Real.log r - Real.log a) / (Real.log b - Real.log a)) +
        Real.log b * ((Real.log r - Real.log a) / (Real.log b - Real.log a)) = Real.log r := by
      field_simp
      ring
    rw [this, Real.exp_log hr]

def topRad (ρ0 : Set.Ioo (0 : ℝ) 1) : Set.Ioc (0 : ℝ) ρ0 := ⟨ρ0, ρ0.2.1, le_rfl⟩

theorem gaussNorm_top_le (b : T.Econ ρ0) {δ : ℝ} (hδ : 0 < δ) :
    ∃ M : ℕ, ∀ ρ : Set.Ioc (0 : ℝ) ρ0,
      gaussNorm (T.coeffB b) ρ0 ≤ max (gaussNorm (T.coeffB b) ρ * ((ρ0 : ℝ) / ρ) ^ M) δ := by
  have hc : ConvergesAt (T.coeffB b) ρ0 := b.2
  obtain ⟨B, hB⟩ := (hc.finite_le hδ).bddAbove
  refine ⟨B.toNat, fun ρ => gaussNorm_le fun n => ?_⟩
  have hρ := rad_pos ρ0 ρ
  have hq : 1 ≤ (ρ0 : ℝ) / ρ := by rw [le_div_iff₀ hρ, one_mul]; exact ρ.2.2
  by_cases hn : n ≤ B
  · refine le_max_of_le_left ?_
    have e : ‖T.coeffB b n‖ * (ρ0 : ℝ) ^ n = (‖T.coeffB b n‖ * (ρ : ℝ) ^ n) * ((ρ0 : ℝ) / ρ) ^ n := by
      rw [div_zpow, mul_assoc, mul_div_assoc', mul_div_cancel_left₀ _ (zpow_pos hρ n).ne']
    rw [e]
    refine mul_le_mul ((T.convergesAt_rad ρ0 b ρ).le_gaussNorm n) ?_ (zpow_pos (by positivity) n).le
      (gaussNorm_nonneg hρ)
    rw [← zpow_natCast]
    exact zpow_le_zpow_right₀ hq (by omega)
  · refine le_max_of_le_right (le_of_lt (not_le.1 fun h => hn (hB h)))

theorem extNorm_top_eq_zero {x : T.RobbaExt ρ0}
    (h : ∀ ρ : Set.Ioc (0 : ℝ) ρ0, (ρ : ℝ) < ρ0 → T.extNorm ρ0 ρ x = 0) :
    T.extNorm ρ0 (topRad ρ0) x = 0 := by
  refine le_antisymm (le_of_forall_pos_le_add fun ε hε => ?_) (T.extNorm_nonneg _ x)
  rw [zero_add]
  set ρh : Set.Ioc (0 : ℝ) ρ0 := ⟨ρ0 / 2, by have := ρ0.2.1; positivity, by linarith [ρ0.2.1]⟩

  have hU : {y : T.RobbaExt ρ0 | T.extNorm ρ0 ρh (x - y) < ε / 2 ∧
      T.extNorm ρ0 (topRad ρ0) (x - y) < ε / 2} ∈ 𝓝 x := by
    refine IsOpen.mem_nhds ?_ ?_
    · exact (isOpen_lt ((T.continuous_extNorm ρh).comp (continuous_const.sub continuous_id))
        continuous_const).inter (isOpen_lt ((T.continuous_extNorm _).comp
          (continuous_const.sub continuous_id)) continuous_const)
    · simp only [Set.mem_setOf_eq, sub_self, extNorm_zero]; exact ⟨by linarith, by linarith⟩
  obtain ⟨b, hb1, hb2⟩ := Completion.denseRange_coe.mem_nhds hU
  obtain ⟨M, hM⟩ := T.gaussNorm_top_le b (δ := ε / 2) (by linarith)

  have hcont : ContinuousAt (fun r : ℝ => ((ρ0 : ℝ) / r) ^ M) (ρ0 : ℝ) :=
    (continuousAt_const.div continuousAt_id (ρ0.2.1).ne').pow M
  have hev1 : ∀ᶠ r in 𝓝 (ρ0 : ℝ), ((ρ0 : ℝ) / r) ^ M < 2 :=
    hcont.eventually (gt_mem_nhds (show ((ρ0 : ℝ) / ρ0) ^ M < 2 by
      rw [div_self (ρ0.2.1).ne', one_pow]; norm_num))
  have hev2 : ∀ᶠ r in 𝓝[<] (ρ0 : ℝ), ((ρ0 : ℝ) / r) ^ M < 2 ∧ r ∈ Set.Ioo ((ρ0 : ℝ) / 2) ρ0 :=
    (hev1.filter_mono nhdsWithin_le_nhds).and (Ioo_mem_nhdsLT (by linarith [ρ0.2.1]))
  obtain ⟨r, hr1, hr2⟩ := hev2.exists
  set ρ : Set.Ioc (0 : ℝ) ρ0 := ⟨r, by linarith [hr2.1, ρ0.2.1], hr2.2.le⟩ with hρdef
  have hρlt : (ρ : ℝ) < ρ0 := hr2.2
  have hρh : (ρh : ℝ) ≤ ρ := hr2.1.le
  have hxb : T.extNorm ρ0 ρ (x - b) < ε / 2 :=
    (T.extNorm_le_max ρh (topRad ρ0) ρ hρh ρ.2.2 (x - b)).trans_lt (max_lt hb1 hb2)
  have hbρ : gaussNorm (T.coeffB b) ρ < ε / 2 := by
    rw [← extNorm_coe]
    have := T.extNorm_add_le ρ (-(x - b)) x
    rw [h ρ hρlt, extNorm_neg, show -(x - ↑b) + x = ↑b by ring] at this
    exact this.trans_lt (max_lt hxb (by linarith))
  have hbtop : gaussNorm (T.coeffB b) ρ0 ≤ ε := by
    refine (hM ρ).trans (max_le ?_ (by linarith))
    calc gaussNorm (T.coeffB b) ρ * ((ρ0 : ℝ) / ρ) ^ M ≤ (ε / 2) * 2 :=
          mul_le_mul hbρ.le hr1.le (pow_nonneg (div_nonneg ρ0.2.1.le (rad_pos ρ0 ρ).le) M)
            (by linarith)
      _ = ε := by ring
  have := T.extNorm_add_le (topRad ρ0) (x - b) b
  rw [sub_add_cancel, extNorm_coe] at this
  exact this.trans (max_le (by linarith) (by exact hbtop))

theorem dist_uniformAt (ρ : Set.Ioc (0 : ℝ) ρ0) (a b : T.Econ ρ0) :
    @dist _ (T.gaussSeminorm ρ0 ρ).toSeminormedRing.toPseudoMetricSpace.toDist a b =
      T.extNorm ρ0 ρ ((a : T.RobbaExt ρ0) - b) := by
  change T.gaussSeminorm ρ0 ρ (-a + b) = _
  rw [neg_add_eq_sub, ← neg_sub, map_neg_eq_map, gaussSeminorm_apply, ← Completion.coe_sub,
    extNorm_coe]

theorem eq_zero_of_forall_extNorm_eq_zero {x : T.RobbaExt ρ0}
    (h : ∀ ρ, T.extNorm ρ0 ρ x = 0) : x = 0 := by
  refine Inseparable.eq (inseparable_iff_ker_uniformity.2 (Filter.mem_ker.2 fun V hV => ?_))
  obtain ⟨W, ⟨hWu, hWc⟩, hWV⟩ := (uniformity_hasBasis_closed.mem_iff).1 hV
  refine hWV ?_
  have hU := Filter.mem_map.1 ((Completion.uniformContinuous_coe (α := T.Econ ρ0)) hWu)
  have hiInf : uniformity (T.Econ ρ0) = ⨅ ρ, @uniformity _ (T.uniformAt ρ0 ρ) := iInf_uniformity
  rw [hiInf] at hU
  obtain ⟨I, hIfin, V', hV', hUeq⟩ := Filter.mem_iInf.1 hU
  have hε : ∀ i : I, ∃ ε > 0, ∀ {a b : T.Econ ρ0},
      @dist _ (T.gaussSeminorm ρ0 i).toSeminormedRing.toPseudoMetricSpace.toDist a b < ε →
        (a, b) ∈ V' i := fun i =>
    (@Metric.mem_uniformity_dist _ (T.gaussSeminorm ρ0 i).toSeminormedRing.toPseudoMetricSpace
      (V' i)).1 (hV' i)
  choose ε hεpos hεV using hε
  haveI : Finite I := hIfin.to_subtype
  have hS : IsClosed {y : T.RobbaExt ρ0 | (y, 0) ∈ W} :=
    hWc.preimage (continuous_id.prodMk continuous_const)
  suffices hx : x ∈ closure {y : T.RobbaExt ρ0 | (y, 0) ∈ W} by
    rw [hS.closure_eq] at hx; exact hx
  rw [mem_closure_iff_nhds]
  intro t ht
  have hO : t ∩ ⋂ i : I, {y : T.RobbaExt ρ0 | T.extNorm ρ0 i (y - x) < ε i} ∈ 𝓝 x := by
    refine Filter.inter_mem ht (Filter.iInter_mem.2 fun i => IsOpen.mem_nhds ?_ ?_)
    · exact isOpen_lt ((T.continuous_extNorm _).comp (continuous_id.sub continuous_const))
        continuous_const
    · simp only [Set.mem_setOf_eq, sub_self, extNorm_zero]; exact hεpos i
  obtain ⟨b, hb⟩ := Completion.denseRange_coe.mem_nhds hO
  refine ⟨b, hb.1, ?_⟩
  have hmem : (b, (0 : T.Econ ρ0)) ∈ (fun q : T.Econ ρ0 × T.Econ ρ0 =>
      ((q.1 : T.RobbaExt ρ0), (q.2 : T.RobbaExt ρ0))) ⁻¹' W := by
    rw [hUeq, Set.mem_iInter]
    intro i
    refine hεV i ?_
    rw [dist_uniformAt, Completion.coe_zero, sub_zero]
    have h1 := Set.mem_iInter.1 hb.2 i
    simp only [Set.mem_setOf_eq] at h1
    have := T.extNorm_add_le i ((b : T.RobbaExt ρ0) - x) x
    rw [sub_add_cancel, h i] at this
    exact this.trans_lt (max_lt h1 (hεpos i))
  rw [Set.mem_preimage, Completion.coe_zero] at hmem
  exact hmem

theorem extNorm_eq_zero_of_eq_zero {x : T.RobbaExt ρ0} {ρ₂ : Set.Ioc (0 : ℝ) ρ0}
    (h : T.extNorm ρ0 ρ₂ x = 0) (ρ : Set.Ioc (0 : ℝ) ρ0) (hρ : (ρ : ℝ) < ρ0) :
    T.extNorm ρ0 ρ x = 0 := by
  refine le_antisymm ?_ (T.extNorm_nonneg ρ x)
  rcases lt_trichotomy (ρ : ℝ) ρ₂ with hlt | heq | hgt
  · set ρ₁ : Set.Ioc (0 : ℝ) ρ0 := ⟨(ρ : ℝ) / 2, by have := rad_pos ρ0 ρ; positivity,
      by have := ρ.2.2; have := rad_pos ρ0 ρ; linarith⟩
    obtain ⟨t, ht0, ht1, hρt⟩ := exists_interp_exponent (a := (ρ₁ : ℝ)) (r := ρ) (b := ρ₂)
      (by have := rad_pos ρ0 ρ; show (0 : ℝ) < (ρ : ℝ) / 2; positivity)
      (by show (ρ : ℝ) / 2 < ρ; have := rad_pos ρ0 ρ; linarith) hlt
    have := T.extNorm_interp_le ρ₁ ρ₂ ρ ht0.le ht1.le hρt x
    rwa [h, Real.zero_rpow ht0.ne', mul_zero] at this
  · have : ρ = ρ₂ := Subtype.ext heq
    rw [this, h]
  · obtain ⟨t, ht0, ht1, hρt⟩ := exists_interp_exponent (a := (ρ₂ : ℝ)) (r := ρ) (b := ρ0)
      (rad_pos ρ0 ρ₂) hgt hρ
    have := T.extNorm_interp_le ρ₂ (topRad ρ0) ρ ht0.le ht1.le hρt x
    rwa [h, Real.zero_rpow (by linarith), zero_mul] at this

theorem extNorm_pos {x : T.RobbaExt ρ0} (hx : x ≠ 0) (ρ : Set.Ioc (0 : ℝ) ρ0) :
    0 < T.extNorm ρ0 ρ x := by
  refine lt_of_le_of_ne (T.extNorm_nonneg ρ x) fun h => hx ?_
  have hbelow : ∀ ρ' : Set.Ioc (0 : ℝ) ρ0, (ρ' : ℝ) < ρ0 → T.extNorm ρ0 ρ' x = 0 :=
    fun ρ' hρ' => T.extNorm_eq_zero_of_eq_zero h.symm ρ' hρ'
  have htop := T.extNorm_top_eq_zero hbelow
  refine T.eq_zero_of_forall_extNorm_eq_zero fun ρ' => ?_
  rcases ρ'.2.2.lt_or_eq with hlt | heq
  · exact hbelow ρ' hlt
  · have : ρ' = topRad ρ0 := Subtype.ext heq
    rw [this, htop]

theorem extNorm_eq_zero_iff {x : T.RobbaExt ρ0} (ρ : Set.Ioc (0 : ℝ) ρ0) :
    T.extNorm ρ0 ρ x = 0 ↔ x = 0 :=
  ⟨fun h => by_contra fun hx => (T.extNorm_pos hx ρ).ne' h, fun h => by rw [h, extNorm_zero]⟩

instance instIsDomainRobbaExt : IsDomain (T.RobbaExt ρ0) := by
  have hnt : Nontrivial (T.RobbaExt ρ0) := ⟨⟨0, 1, fun h => by
    have := congrArg (T.extNorm ρ0 (topRad ρ0)) h
    rw [extNorm_zero, extNorm_one] at this
    exact zero_ne_one this⟩⟩
  have : NoZeroDivisors (T.RobbaExt ρ0) := ⟨fun {x y} hxy => by
    have := congrArg (T.extNorm ρ0 (topRad ρ0)) hxy
    rw [extNorm_mul, extNorm_zero, mul_eq_zero, T.extNorm_eq_zero_iff, T.extNorm_eq_zero_iff] at this
    exact this⟩
  exact NoZeroDivisors.to_isDomain _

theorem dist_uniformAt' (ρ : Set.Ioc (0 : ℝ) ρ0) (a b : T.Econ ρ0) :
    @dist _ (T.gaussSeminorm ρ0 ρ).toSeminormedRing.toPseudoMetricSpace.toDist a b =
      gaussNorm (T.coeffB ((a : T.B) - b)) ρ := by
  change T.gaussSeminorm ρ0 ρ (-a + b) = _
  rw [neg_add_eq_sub, ← neg_sub, map_neg_eq_map, gaussSeminorm_apply]
  rfl

variable {ρ1 : Set.Ioo (0 : ℝ) 1}

def incl (h : (ρ1 : ℝ) ≤ ρ0) : T.Econ ρ0 →+* T.Econ ρ1 := Subring.inclusion (T.Econ_anti h)

theorem coe_incl (h : (ρ1 : ℝ) ≤ ρ0) (b : T.Econ ρ0) : ((T.incl h b : T.Econ ρ1) : T.B) = b := rfl

theorem uniformContinuous_incl (h : (ρ1 : ℝ) ≤ ρ0) : UniformContinuous (T.incl h) := by
  refine uniformContinuous_iInf_rng.2 fun ρ => ?_
  refine uniformContinuous_iInf_dom (i := (⟨ρ, ρ.2.1, ρ.2.2.trans h⟩ : Set.Ioc (0 : ℝ) ρ0)) ?_
  refine (@Metric.uniformContinuous_iff _ _
    (T.gaussSeminorm ρ0 ⟨ρ, ρ.2.1, ρ.2.2.trans h⟩).toSeminormedRing.toPseudoMetricSpace
    (T.gaussSeminorm ρ1 ρ).toSeminormedRing.toPseudoMetricSpace _).2 fun ε hε => ⟨ε, hε, ?_⟩
  intro a b hab
  rw [dist_uniformAt'] at hab ⊢
  exact hab

def res (h : (ρ1 : ℝ) ≤ ρ0) : T.RobbaExt ρ0 →+* T.RobbaExt ρ1 :=
  Completion.mapRingHom (T.incl h) (T.uniformContinuous_incl h).continuous

theorem res_coe (h : (ρ1 : ℝ) ≤ ρ0) (b : T.Econ ρ0) :
    T.res h (b : T.RobbaExt ρ0) = ((T.incl h b : T.Econ ρ1) : T.RobbaExt ρ1) :=
  Completion.mapRingHom_coe _ b

theorem continuous_res (h : (ρ1 : ℝ) ≤ ρ0) : Continuous (T.res h) :=
  Completion.continuous_map

theorem extNorm_res (h : (ρ1 : ℝ) ≤ ρ0) (ρ : Set.Ioc (0 : ℝ) ρ1) (x : T.RobbaExt ρ0) :
    T.extNorm ρ1 ρ (T.res h x) = T.extNorm ρ0 ⟨ρ, ρ.2.1, ρ.2.2.trans h⟩ x :=
  Completion.induction_on x
    (isClosed_eq ((T.continuous_extNorm ρ).comp (T.continuous_res h)) (T.continuous_extNorm _))
    fun b => by rw [res_coe, extNorm_coe, extNorm_coe, coe_incl]

theorem res_injective (h : (ρ1 : ℝ) ≤ ρ0) : Function.Injective (T.res h) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  have := T.extNorm_res h (topRad ρ1) x
  rw [hx, extNorm_zero, eq_comm, T.extNorm_eq_zero_iff] at this
  exact this

theorem res_self (x : T.RobbaExt ρ0) : T.res (le_refl (ρ0 : ℝ)) x = x :=
  Completion.induction_on x (isClosed_eq (T.continuous_res _) continuous_id)
    fun b => by rw [res_coe]; rfl

theorem res_res {ρ2 : Set.Ioo (0 : ℝ) 1} (h12 : (ρ1 : ℝ) ≤ ρ0) (h23 : (ρ2 : ℝ) ≤ ρ1)
    (x : T.RobbaExt ρ0) : T.res h23 (T.res h12 x) = T.res (h23.trans h12) x :=
  Completion.induction_on x
    (isClosed_eq ((T.continuous_res _).comp (T.continuous_res _)) (T.continuous_res _))
    fun b => by rw [res_coe, res_coe, res_coe]; rfl

theorem coe_eq_zero_Econ {b : T.Econ ρ0} (hb : (b : T.RobbaExt ρ0) = 0) : b = 0 := by
  have h1 : T.extNorm ρ0 (topRad ρ0) (b : T.RobbaExt ρ0) = 0 := by rw [hb, extNorm_zero]
  rw [extNorm_coe] at h1
  change gaussNorm (T.coeffB b) (ρ0 : ℝ) = 0 at h1

  by_contra hb0
  have hb0' : (b : T.B) ≠ 0 := fun h => hb0 (Subtype.ext h)
  obtain ⟨n, x, hx⟩ := IsLocalization.Away.surj T.π (b : T.B)
  have hx0 : x ≠ 0 := by
    rintro rfl; exact hb0' (T.eq_zero_of_mul_pow (by rw [hx, map_zero]))
  have hc := b.2
  rw [mem_Econ, T.coeffB_eq hx] at hc
  rw [T.coeffB_eq hx, gaussNorm_shift ρ0.2.1] at h1
  have hx0' : T.zcoeff x ≠ 0 := fun h => hx0 ((T.zcoeff_eq_zero_iff x).1 h)
  have := gaussNorm_pos ρ0.2.1 ((convergesAt_shift_iff ρ0.2.1 _).1 hc) hx0'
  have hz := zpow_pos ρ0.2.1 (-(n : ℤ))
  nlinarith [mul_pos this hz]

theorem coe_injective_Econ : Function.Injective ((↑) : T.Econ ρ0 → T.RobbaExt ρ0) := fun a b hab =>
  sub_eq_zero.1 (T.coe_eq_zero_Econ (by rw [Completion.coe_sub, hab, sub_self]))

end TeichLift

end GroundTheory.PAdicHodge
