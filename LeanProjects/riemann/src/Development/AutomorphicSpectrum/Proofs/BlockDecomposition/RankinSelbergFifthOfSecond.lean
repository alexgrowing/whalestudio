import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.VerticalStrips.UnramifiedEulerProductIntegral
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralCompSymm

noncomputable section

open MeasureTheory Matrix Filter Topology
open GroundTheory.LocalField GroundTheory.Automorphic
open GroundTheory.Automorphic.GLnLocal (integralGL)
open ValuativeRel
open scoped ValuativeRel ENNReal NNReal

namespace GlobalTheory.CompanionTheory.RSPlane

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [MeasurableSpace F] [BorelSpace F]

def ball (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    (n : ℤ) : Set (Fin 2 → F) := {r | ∀ i, r i ∈ valBall F n}

def shell (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    (n : ℤ) : Set (Fin 2 → F) := ball F n \ ball F (n + 1)

def uu (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    (n : ℤ) : ℝ≥0 := (residueCard F : ℝ≥0) ^ (-n)

omit [MeasurableSpace F] [BorelSpace F] in
theorem ball_eq (n : ℤ) : ball F n = Set.pi Set.univ fun _ => (valBall F n : Set F) := by
  ext r; simp [ball]

omit [MeasurableSpace F] [BorelSpace F] in
theorem ball_anti {n m : ℤ} (h : n ≤ m) : ball F m ⊆ ball F n :=
  fun _ hr i => valBall_antitone h (hr i)

theorem measurableSet_ball (n : ℤ) : MeasurableSet (ball F n) := by
  rw [ball_eq]
  exact MeasurableSet.univ_pi fun _ => measurableSet_valBall n

theorem measurableSet_shell (n : ℤ) : MeasurableSet (shell F n) :=
  (measurableSet_ball n).diff (measurableSet_ball (n + 1))

theorem plane_measure_isAddHaar (ψ : AddChar F Circle) : (Ad3.R.m2 ψ).IsAddHaarMeasure := by
  unfold Ad3.R.m2; infer_instance

theorem plane_measure_ball {ψ : AddChar F Circle} (hψ : Ad3.IsStd ψ) (n : ℤ) :
    Ad3.R.m2 ψ (ball F n) = ((uu F n ^ 2 : ℝ≥0) : ℝ≥0∞) := by
  have h1 : selfDualMeasure ψ (valBall F n : Set F) = (uu F n : ℝ≥0∞) := by
    rw [measure_valBall, coe_valBall_zero, selfDualMeasure_integers, hψ.2.2]
    simp [uu]
  rw [Ad3.R.m2, ball_eq, Measure.pi_pi]
  simp [h1, Fin.prod_univ_two, sq]

omit [MeasurableSpace F] [BorelSpace F] in
theorem uu_succ (n : ℤ) : uu F (n + 1) = uu F n * ((residueCard F : ℝ≥0))⁻¹ := by
  rw [uu, uu, neg_add, zpow_add₀ residueCard_nnreal_ne_zero, _root_.zpow_neg_one]

def cc (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] : ℝ≥0 :=
  1 - ((residueCard F : ℝ≥0)⁻¹) ^ 2

omit [MeasurableSpace F] [BorelSpace F] in
theorem cc_ne_zero : cc F ≠ 0 := by
  have h : ((residueCard F : ℝ≥0)⁻¹) ^ 2 < 1 :=
    pow_lt_one₀ zero_le' (inv_lt_one_of_one_lt₀ one_lt_residueCard_nnreal) two_ne_zero
  exact (tsub_pos_of_lt h).ne'

theorem plane_measure_shell {ψ : AddChar F Circle} (hψ : Ad3.IsStd ψ) (n : ℤ) :
    Ad3.R.m2 ψ (shell F n) = ((cc F * uu F n ^ 2 : ℝ≥0) : ℝ≥0∞) := by
  have := plane_measure_isAddHaar ψ
  rw [shell, measure_diff (ball_anti (by omega)) (measurableSet_ball _).nullMeasurableSet
    (by rw [plane_measure_ball hψ]; exact ENNReal.coe_ne_top), plane_measure_ball hψ, plane_measure_ball hψ, uu_succ, ← ENNReal.coe_sub]
  congr 1
  rw [cc, tsub_mul, one_mul, mul_pow, mul_comm]

theorem plane_measure_zero {ψ : AddChar F Circle} (hψ : Ad3.IsStd ψ) : Ad3.R.m2 ψ {0} = 0 := by
  have ht : Tendsto (fun n : ℕ => uu F (n : ℤ)) atTop (𝓝 0) := by
    have h := tendsto_pow_atTop_nhds_zero_of_lt_one (r := ((residueCard F : ℝ≥0))⁻¹) zero_le'
      (inv_lt_one_of_one_lt₀ one_lt_residueCard_nnreal)
    refine h.congr fun n => ?_
    rw [uu, _root_.zpow_neg, zpow_natCast, inv_pow]
  have ht2 : Tendsto (fun n : ℕ => ((uu F (n : ℤ) ^ 2 : ℝ≥0) : ℝ≥0∞)) atTop (𝓝 0) := by
    have := (ht.pow 2)
    simpa using ENNReal.tendsto_coe.mpr this
  refine le_antisymm (ge_of_tendsto' ht2 fun n => ?_) zero_le'
  rw [← plane_measure_ball hψ]
  exact measure_mono fun r hr i => by rw [Set.mem_singleton_iff.mp hr]; exact zero_mem _

omit [MeasurableSpace F] [BorelSpace F] in
theorem iUnion_shell : ⋃ n, shell F n = ({0} : Set (Fin 2 → F))ᶜ := by
  ext r
  simp only [Set.mem_iUnion, Set.mem_compl_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨n, hn, hn'⟩ rfl
    exact hn' fun i => zero_mem _
  · intro hr
    obtain ⟨i, hi⟩ : ∃ i, r i ≠ 0 := by
      by_contra h
      push_neg at h
      exact hr (funext h)
    have hex : ∃ n : ℤ, r ∈ ball F n := by
      obtain ⟨a, ha⟩ := exists_mem_valBall_neg_nat (r 0)
      obtain ⟨b, hb⟩ := exists_mem_valBall_neg_nat (r 1)
      refine ⟨-((max a b : ℕ) : ℤ), fun j => ?_⟩
      fin_cases j
      · exact valBall_antitone (by push_cast; omega) ha
      · exact valBall_antitone (by push_cast; omega) hb
    have hbd : ∀ n : ℤ, r ∈ ball F n → n ≤ ord (r i) := fun n hn =>
      (mem_valBall_iff_le_ord hi).mp (hn i)
    obtain ⟨n, hn, hmax⟩ := Int.exists_greatest_of_bdd ⟨_, hbd⟩ hex
    exact ⟨n, hn, fun h => by have := hmax _ h; omega⟩

omit [MeasurableSpace F] [BorelSpace F] in
theorem disjoint_shell : Pairwise (Function.onFun Disjoint (shell F)) := by
  have key : ∀ n m : ℤ, n < m → Disjoint (shell F n) (shell F m) := fun n m h =>
    Set.disjoint_left.mpr fun r hr hr' => hr.2 (ball_anti (by omega) hr'.1)
  intro n m hnm
  rcases lt_or_gt_of_ne hnm with h | h
  · exact key n m h
  · exact (key m n h).symm

theorem lintegral_shells (μ : Measure (Fin 2 → F)) (h0 : μ {0} = 0) (H : (Fin 2 → F) → ℝ≥0∞)
    (h : ℤ → ℝ≥0∞) (hH : ∀ n, ∀ r ∈ shell F n, H r = h n) :
    ∫⁻ r, H r ∂μ = ∑' n, h n * μ (shell F n) := by
  have hae : ∀ᵐ r ∂μ, r ∈ ⋃ n, shell F n := by
    rw [iUnion_shell]
    exact measure_eq_zero_iff_ae_notMem.mp h0
  rw [← Measure.restrict_eq_self_of_ae_mem hae, lintegral_iUnion measurableSet_shell disjoint_shell]
  refine tsum_congr fun n => ?_
  rw [Measure.restrict_eq_self_of_ae_mem hae,
    setLIntegral_congr_fun (measurableSet_shell n) (hH n), setLIntegral_const]

omit [MeasurableSpace F] [BorelSpace F] in
theorem exists_unit_ord (n : ℤ) : ∃ t : Fˣ, ord (t : F) = n := by
  obtain ⟨c, hc, hcn⟩ := exists_ord_eq F n
  exact ⟨Units.mk0 c hc, hcn⟩

def tt (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    (n : ℤ) : Fˣ := (exists_unit_ord n).choose

omit [MeasurableSpace F] [BorelSpace F] in
theorem ord_tt (n : ℤ) : ord (tt F n : F) = n := (exists_unit_ord n).choose_spec

omit [MeasurableSpace F] [BorelSpace F] in
theorem mem_integer_iff_ord {x : F} (hx : x ≠ 0) : x ∈ 𝒪[F] ↔ 0 ≤ ord x := by
  rw [← mem_valBall_zero_iff, mem_valBall_iff_le_ord hx]

omit [MeasurableSpace F] [BorelSpace F] in
theorem integral_div {x : F} {n : ℤ} (hx : x ∈ valBall F n) (t : Fˣ) (ht : ord (t : F) = n) :
    (t : F)⁻¹ * x ∈ 𝒪[F] := by
  by_cases h0 : x = 0
  · simp [h0]
  have ht0 : (t : F) ≠ 0 := t.ne_zero
  rw [mem_integer_iff_ord (mul_ne_zero (inv_ne_zero ht0) h0), ord_mul (inv_ne_zero ht0) h0,
    ord_inv ht0, ht]
  have := (mem_valBall_iff_le_ord h0).mp hx
  omega

omit [MeasurableSpace F] [BorelSpace F] in
theorem exists_K_row {a b : F} (ha : a ∈ 𝒪[F]) (hb : b ∈ 𝒪[F])
    (hu : (a ≠ 0 ∧ a⁻¹ ∈ 𝒪[F]) ∨ (b ≠ 0 ∧ b⁻¹ ∈ 𝒪[F])) :
    ∃ κ ∈ integralGL F 2, ![0, 1] ᵥ* (κ : Matrix (Fin 2) (Fin 2) F) = ![a, b] := by
  rcases hu with ⟨h0, hi⟩ | ⟨h0, hi⟩
  · refine ⟨⟨!![0, -a⁻¹; a, b], !![b, a⁻¹; -a, 0], ?_, ?_⟩, ?_, ?_⟩
    · ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, h0, mul_comm]
    · ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, h0, mul_comm]
    · rw [GLnLocal.mem_integralGL_iff]
      refine ⟨fun i j => ?_, fun i j => ?_⟩
      · fin_cases i <;> fin_cases j <;> simp [ha, hb, hi]
      · fin_cases i <;> fin_cases j <;> simp [ha, hb, hi]
    · ext j; fin_cases j <;> simp [Matrix.vecMul, dotProduct, Fin.sum_univ_two]
  · refine ⟨⟨!![b⁻¹, 0; a, b], !![b, 0; -a, b⁻¹], ?_, ?_⟩, ?_, ?_⟩
    · ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, h0, mul_comm]
    · ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, h0, mul_comm]
    · rw [GLnLocal.mem_integralGL_iff]
      refine ⟨fun i j => ?_, fun i j => ?_⟩
      · fin_cases i <;> fin_cases j <;> simp [ha, hb, hi]
      · fin_cases i <;> fin_cases j <;> simp [ha, hb, hi]
    · ext j; fin_cases j <;> simp [Matrix.vecMul, dotProduct, Fin.sum_univ_two]

omit [MeasurableSpace F] [BorelSpace F] in

theorem exists_K_shell {n : ℤ} {r : Fin 2 → F} (hr : r ∈ shell F n) :
    ∃ κ ∈ integralGL F 2, r = ![0, (tt F n : F)] ᵥ* (κ : Matrix (Fin 2) (Fin 2) F) := by
  have ht0 : (tt F n : F) ≠ 0 := (tt F n).ne_zero
  have hint := fun i => integral_div (hr.1 i) (tt F n) (ord_tt n)
  have hunit : ∃ i, (tt F n : F)⁻¹ * r i ≠ 0 ∧ ((tt F n : F)⁻¹ * r i)⁻¹ ∈ 𝒪[F] := by
    have := hr.2
    simp only [ball, Set.mem_setOf_eq, not_forall] at this
    obtain ⟨i, hi⟩ := this
    have h0 : r i ≠ 0 := fun h => hi (h ▸ zero_mem _)
    have h1 := (mem_valBall_iff_le_ord h0).mp (hr.1 i)
    have h2 := mt (mem_valBall_iff_le_ord h0).mpr hi
    have hn : (tt F n : F)⁻¹ * r i ≠ 0 := mul_ne_zero (inv_ne_zero ht0) h0
    refine ⟨i, hn, ?_⟩
    rw [mem_integer_iff_ord (inv_ne_zero hn), ord_inv hn, ord_mul (inv_ne_zero ht0) h0,
      ord_inv ht0, ord_tt]
    omega
  have hu : ((tt F n : F)⁻¹ * r 0 ≠ 0 ∧ ((tt F n : F)⁻¹ * r 0)⁻¹ ∈ 𝒪[F]) ∨
      ((tt F n : F)⁻¹ * r 1 ≠ 0 ∧ ((tt F n : F)⁻¹ * r 1)⁻¹ ∈ 𝒪[F]) := by
    obtain ⟨i, hi⟩ := hunit
    fin_cases i
    · exact Or.inl hi
    · exact Or.inr hi
  obtain ⟨κ, hκ, he⟩ := exists_K_row (hint 0) (hint 1) hu
  refine ⟨κ, hκ, ?_⟩
  have hs : ![0, (tt F n : F)] = (tt F n : F) • ![0, 1] := by
    ext j; fin_cases j <;> simp
  rw [hs, Matrix.smul_vecMul, he]
  ext j; fin_cases j <;> simp [ht0]

section Act

variable [MeasurableSpace (GL (Fin 2) F)] [BorelSpace (GL (Fin 2) F)]

def act (r : Fin 2 → F) (κ : integralGL F 2) : Fin 2 → F := r ᵥ* (κ.1 : Matrix (Fin 2) (Fin 2) F)

omit [MeasurableSpace F] [BorelSpace F] [MeasurableSpace (GL (Fin 2) F)] [BorelSpace (GL (Fin 2) F)] in
theorem act_act (r : Fin 2 → F) (κ κ' : integralGL F 2) : act (act r κ) κ' = act r (κ * κ') := by
  simp [act, Matrix.vecMul_vecMul]

theorem measurable_entry (i j : Fin 2) :
    Measurable fun κ : integralGL F 2 => (κ.1 : Matrix (Fin 2) (Fin 2) F) i j :=
  ((GLnLocal.continuous_entry F 2 i j).comp continuous_subtype_val).measurable

theorem measurable_act : Measurable fun p : (Fin 2 → F) × integralGL F 2 => act p.1 p.2 := by
  refine measurable_pi_lambda _ fun j => ?_
  have h : (fun p : (Fin 2 → F) × integralGL F 2 => act p.1 p.2 j) = fun p =>
      p.1 0 * (p.2.1 : Matrix (Fin 2) (Fin 2) F) 0 j + p.1 1 * (p.2.1 : Matrix (Fin 2) (Fin 2) F) 1 j := by
    funext p
    simp [act, Matrix.vecMul, dotProduct, Fin.sum_univ_two]
  rw [h]
  exact (((measurable_pi_apply 0).comp measurable_fst).mul ((measurable_entry 0 j).comp measurable_snd)).add
    (((measurable_pi_apply 1).comp measurable_fst).mul ((measurable_entry 1 j).comp measurable_snd))

omit [MeasurableSpace F] [BorelSpace F] [MeasurableSpace (GL (Fin 2) F)] [BorelSpace (GL (Fin 2) F)] in
theorem act_mem_ball {r : Fin 2 → F} (hr : r ∈ ball F 0) (κ : integralGL F 2) : act r κ ∈ ball F 0 := by
  intro j
  have he := ((GLnLocal.mem_integralGL_iff F 2).mp κ.2).1
  have h : act r κ j = r 0 * (κ.1 : Matrix (Fin 2) (Fin 2) F) 0 j +
      r 1 * (κ.1 : Matrix (Fin 2) (Fin 2) F) 1 j := by
    simp [act, Matrix.vecMul, dotProduct, Fin.sum_univ_two]
  rw [h, mem_valBall_zero_iff]
  exact Subring.add_mem _ (Subring.mul_mem _ (mem_valBall_zero_iff.mp (hr 0)) (he 0 j))
    (Subring.mul_mem _ (mem_valBall_zero_iff.mp (hr 1)) (he 1 j))

theorem measurePreserving_act {ψ : AddChar F Circle} (hψ : Ad3.IsStd ψ) (κ : integralGL F 2) :
    MeasurePreserving (fun r => act r κ) (Ad3.R.m2 ψ) (Ad3.R.m2 ψ) := by
  have := plane_measure_isAddHaar ψ
  let M : (Fin 2 → F) ≃ₗ[F] (Fin 2 → F) :=
    { toFun := fun r => act r κ⁻¹
      invFun := fun r => act r κ
      map_add' := fun x y => by simp [act, Matrix.add_vecMul]
      map_smul' := fun c x => by simp [act, Matrix.smul_vecMul]
      left_inv := fun r => by simp [act_act, act]
      right_inv := fun r => by simp [act_act, act] }
  have hmeas : Measurable fun r : Fin 2 → F => act r κ :=
    measurable_act.comp (measurable_id.prodMk measurable_const)
  have h := GlobalTheory.ChangeVarPi.map_symm_eq_smul F (Fin 2) (Ad3.R.m2 ψ) M
  have hfun : (M.symm : (Fin 2 → F) → (Fin 2 → F)) = fun r => act r κ := rfl
  rw [hfun] at h
  have hpre : (fun r => act r κ) ⁻¹' ball F 0 = ball F 0 := by
    ext r
    refine ⟨fun hr => ?_, fun hr => act_mem_ball hr κ⟩
    have := act_mem_ball hr κ⁻¹
    simpa [act_act, act] using this
  have hb := congrArg (fun μ : Measure (Fin 2 → F) => μ (ball F 0)) h
  simp only [Measure.map_apply hmeas (measurableSet_ball 0), hpre, Measure.smul_apply, plane_measure_ball hψ] at hb
  have hu : uu F 0 = 1 := by simp [uu]
  rw [hu] at hb
  have hc : distribHaarChar F (LinearEquiv.det M) = 1 := by
    simpa [ENNReal.smul_def] using hb.symm
  rw [hc, one_smul] at h
  exact ⟨hmeas, h⟩

end Act

section Main

variable [MeasurableSpace (GL (Fin 2) F)] [BorelSpace (GL (Fin 2) F)]

def avg (m : Measure (integralGL F 2)) (f : (Fin 2 → F) → ℝ≥0∞) (r : Fin 2 → F) : ℝ≥0∞ :=
  ∫⁻ κ, f (act r κ) ∂m

omit [MeasurableSpace F] [BorelSpace F] in
theorem avg_act (m : Measure (integralGL F 2)) [m.IsHaarMeasure] (f : (Fin 2 → F) → ℝ≥0∞)
    (r : Fin 2 → F) (κ₀ : integralGL F 2) : avg m f (act r κ₀) = avg m f r := by
  simp only [avg, act_act]
  exact lintegral_mul_left_eq_self (fun κ => f (act r κ)) κ₀

omit [MeasurableSpace F] [BorelSpace F] in
theorem avg_shell (m : Measure (integralGL F 2)) [m.IsHaarMeasure] (f : (Fin 2 → F) → ℝ≥0∞)
    {n : ℤ} {r : Fin 2 → F} (hr : r ∈ shell F n) : avg m f r = avg m f ![0, (tt F n : F)] := by
  obtain ⟨κ, hκ, rfl⟩ := exists_K_shell hr
  exact avg_act m f _ ⟨κ, hκ⟩

theorem measurable_avg (m : Measure (integralGL F 2)) [IsProbabilityMeasure m]
    {f : (Fin 2 → F) → ℝ≥0∞} (hf : Measurable f) : Measurable (avg m f) :=
  Measurable.lintegral_prod_right' (f := fun p : (Fin 2 → F) × integralGL F 2 => f (act p.1 p.2))
    (hf.comp measurable_act)

theorem lintegral_avg {ψ : AddChar F Circle} (hψ : Ad3.IsStd ψ) (m : Measure (integralGL F 2))
    [IsProbabilityMeasure m] {f : (Fin 2 → F) → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ r, avg m f r ∂Ad3.R.m2 ψ = ∫⁻ r, f r ∂Ad3.R.m2 ψ := by
  have := plane_measure_isAddHaar ψ
  simp only [avg]
  have hae : AEMeasurable (Function.uncurry fun (r : Fin 2 → F) (κ : integralGL F 2) => f (act r κ))
      ((Ad3.R.m2 ψ).prod m) := (hf.comp measurable_act).aemeasurable
  rw [lintegral_lintegral_swap hae]
  have h : ∀ κ : integralGL F 2, ∫⁻ r, f (act r κ) ∂Ad3.R.m2 ψ = ∫⁻ r, f r ∂Ad3.R.m2 ψ :=
    fun κ => (measurePreserving_act hψ κ).lintegral_comp hf
  simp [h]

theorem lintegral_plane_measure_shells {ψ : AddChar F Circle} (hψ : Ad3.IsStd ψ) (m : Measure (integralGL F 2))
    [m.IsHaarMeasure] [IsProbabilityMeasure m] {f : (Fin 2 → F) → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ r, f r ∂Ad3.R.m2 ψ =
      ∑' n, avg m f ![0, (tt F n : F)] * ((cc F * uu F n ^ 2 : ℝ≥0) : ℝ≥0∞) := by
  rw [← lintegral_avg hψ m hf, lintegral_shells _ (plane_measure_zero hψ) _ (fun n => avg m f ![0, (tt F n : F)])
    (fun n r hr => avg_shell m f hr)]
  simp_rw [plane_measure_shell hψ]

end Main

def ushell (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    (n : ℤ) : Set Fˣ := {z | ord (z : F) = n}

theorem measurableSet_ushell (n : ℤ) : MeasurableSet (ushell F n) := by
  have h : ushell F n = Units.val ⁻¹' ((valBall F n : Set F) \ valBall F (n + 1)) := by
    ext z
    simp only [ushell, Set.mem_setOf_eq, Set.mem_preimage, Set.mem_diff, SetLike.mem_coe,
      mem_valBall_iff_le_ord z.ne_zero]
    omega
  rw [h]
  exact measurableEmbedding_units_val.measurable
    ((measurableSet_valBall n).diff (measurableSet_valBall (n + 1)))

omit [MeasurableSpace F] [BorelSpace F] in
theorem valuation_eq_one_iff {x : F} (hx : x ≠ 0) : valuation F x = 1 ↔ ord x = 0 := by
  constructor
  · intro h
    have h0 : x ∈ valBall F 0 := mem_valBall_zero_iff.mpr (le_of_eq h)
    have h1 : x ∉ valBall F 1 := fun h' => (mem_valBall_one_iff.mp h').ne h
    have a := (mem_valBall_iff_le_ord hx).mp h0
    have b := mt (mem_valBall_iff_le_ord hx).mpr h1
    omega
  · intro h
    have h0 : x ∈ valBall F 0 := (mem_valBall_iff_le_ord hx).mpr h.ge
    have h1 : x ∉ valBall F 1 := fun h' => by
      have := (mem_valBall_iff_le_ord hx).mp h'
      omega
    have hle : valuation F x ≤ 1 := mem_valBall_zero_iff.mp h0
    have hnlt : ¬ valuation F x < 1 := fun h' => h1 (mem_valBall_one_iff.mpr h')
    exact le_antisymm hle (not_lt.mp hnlt)

theorem multHaar_ushell (n : ℤ) : multHaar F (ushell F n) = 1 := by
  have h : ushell F n = (fun z => (tt F n)⁻¹ * z) ⁻¹' (unitFiltrationUnits F 0 : Set Fˣ) := by
    ext z
    have ht0 : (tt F n : F) ≠ 0 := (tt F n).ne_zero
    simp only [ushell, Set.mem_setOf_eq, Set.mem_preimage, SetLike.mem_coe,
      mem_unitFiltrationUnits_zero_iff, Units.val_mul, Units.val_inv_eq_inv_val]
    rw [valuation_eq_one_iff (mul_ne_zero (inv_ne_zero ht0) z.ne_zero),
      ord_mul (inv_ne_zero ht0) z.ne_zero, ord_inv ht0, ord_tt]
    omega
  rw [h, measure_preimage_mul, multHaar_unitFiltrationUnits_zero]

theorem lintegral_ushells (H : Fˣ → ℝ≥0∞) (h : ℤ → ℝ≥0∞) (hH : ∀ n, ∀ z ∈ ushell F n, H z = h n) :
    ∫⁻ z, H z ∂multHaar F = ∑' n, h n := by
  have hU : ⋃ n, ushell F n = Set.univ :=
    Set.eq_univ_of_forall fun z => Set.mem_iUnion.mpr ⟨_, rfl⟩
  have hd : Pairwise (Function.onFun Disjoint (ushell F)) := fun n m hnm =>
    Set.disjoint_left.mpr fun z hz hz' => hnm (hz.symm.trans hz')
  rw [← setLIntegral_univ, ← hU, lintegral_iUnion measurableSet_ushell hd]
  refine tsum_congr fun n => ?_
  rw [setLIntegral_congr_fun (measurableSet_ushell n) (hH n), setLIntegral_const, multHaar_ushell,
    mul_one]

omit [MeasurableSpace F] [BorelSpace F] in
theorem row_mem_shell {n : ℤ} {z : Fˣ} (hz : ord (z : F) = n) : ![0, (z : F)] ∈ shell F n := by
  refine ⟨fun i => ?_, fun h => ?_⟩
  · fin_cases i
    · exact zero_mem _
    · exact (mem_valBall_iff_le_ord z.ne_zero).mpr hz.ge
  · have := (mem_valBall_iff_le_ord z.ne_zero).mp (h 1)
    omega

def dens (z : Fˣ) : ℝ≥0∞ := ENNReal.ofReal ((modulus (z : F) : ℝ) ^ 2)

theorem measurable_dens : Measurable (dens : Fˣ → ℝ≥0∞) := by
  unfold dens
  exact ENNReal.measurable_ofReal.comp
    (((measurable_modulus.comp measurableEmbedding_units_val.measurable).coe_nnreal_real).pow_const 2)

omit [MeasurableSpace F] [BorelSpace F] in
theorem dens_of_ord {n : ℤ} {z : Fˣ} (hz : ord (z : F) = n) :
    dens z = ((uu F n ^ 2 : ℝ≥0) : ℝ≥0∞) := by
  rw [dens, modulus_of_ne_zero z.ne_zero, hz, uu, ← ENNReal.ofReal_coe_nnreal]
  push_cast
  rfl

theorem sFinite_multHaar : SFinite (multHaar F) := by
  have h1 : SecondCountableTopology Fˣ :=
    (isOpenEmbedding_units_val (K := F)).isEmbedding.secondCountableTopology
  have h2 : LocallyCompactSpace Fˣ := (isOpenEmbedding_units_val (K := F)).locallyCompactSpace
  infer_instance

theorem measurable_row : Measurable fun z : Fˣ => (![0, (z : F)] : Fin 2 → F) := by
  refine measurable_pi_lambda _ fun j => ?_
  fin_cases j
  · exact measurable_const
  · exact measurableEmbedding_units_val.measurable

section Push

variable [MeasurableSpace (GL (Fin 2) F)] [BorelSpace (GL (Fin 2) F)]

theorem measurable_push : Measurable fun p : integralGL F 2 × Fˣ =>
    (![0, (p.2 : F)] ᵥ* (p.1.1 : Matrix (Fin 2) (Fin 2) F) : Fin 2 → F) :=
  measurable_act.comp ((measurable_row.comp measurable_snd).prodMk measurable_fst)

theorem lintegral_push (m : Measure (integralGL F 2)) [m.IsHaarMeasure] [IsProbabilityMeasure m]
    {f : (Fin 2 → F) → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ r, f r ∂(Measure.map (fun p : integralGL F 2 × Fˣ =>
        (![0, (p.2 : F)] ᵥ* (p.1.1 : Matrix (Fin 2) (Fin 2) F) : Fin 2 → F))
      (m.prod ((multHaar F).withDensity dens))) =
      ∑' n, avg m f ![0, (tt F n : F)] * ((uu F n ^ 2 : ℝ≥0) : ℝ≥0∞) := by
  have := sFinite_multHaar (F := F)
  rw [lintegral_map hf measurable_push, lintegral_prod_symm (fun p : integralGL F 2 × Fˣ =>
    f (![0, (p.2 : F)] ᵥ* (p.1.1 : Matrix (Fin 2) (Fin 2) F))) (hf.comp measurable_push).aemeasurable]
  have hA : Measurable fun z : Fˣ => avg m f ![0, (z : F)] := (measurable_avg m hf).comp measurable_row
  have e : ∫⁻ z, ∫⁻ κ : integralGL F 2, f (![0, (z : F)] ᵥ* (κ.1 : Matrix (Fin 2) (Fin 2) F)) ∂m
      ∂((multHaar F).withDensity dens) =
      ∫⁻ z, avg m f ![0, (z : F)] ∂((multHaar F).withDensity dens) := rfl
  rw [e, lintegral_withDensity_eq_lintegral_mul _ measurable_dens hA]
  refine lintegral_ushells _ _ fun n z hz => ?_
  simp only [Pi.mul_apply]
  rw [dens_of_ord hz, avg_shell m f (row_mem_shell hz), mul_comm]

end Push

theorem measure_plane_eq_rows : Ad3.R.A2 → Ad3.R.A5 := by
  intro _ F _ _ _ _ _ _ ψ hψ _ _ m _ _
  refine ⟨cc F, cc_ne_zero, Measure.ext fun s hs => ?_⟩
  have hf : Measurable (s.indicator (1 : (Fin 2 → F) → ℝ≥0∞)) := measurable_one.indicator hs
  have h1 := lintegral_plane_measure_shells hψ m hf
  have h2 := lintegral_push m hf
  rw [lintegral_indicator_one hs] at h1 h2
  have e : (fun z : Fˣ => ENNReal.ofReal ((modulus (z : F) : ℝ) ^ 2)) = dens := rfl
  rw [Measure.smul_apply, e, h1, h2, ENNReal.smul_def, smul_eq_mul, ← ENNReal.tsum_mul_left]
  refine tsum_congr fun n => ?_
  rw [ENNReal.coe_mul]
  ring

end GlobalTheory.CompanionTheory.RSPlane

end
