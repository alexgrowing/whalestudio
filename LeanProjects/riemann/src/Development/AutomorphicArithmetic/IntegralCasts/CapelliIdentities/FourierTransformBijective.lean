import Mathlib

open MeasureTheory Metric

section
variable {K : Type} [NontriviallyNormedField K] [IsUltrametricDist K] [ProperSpace K]

private lemma cond_one (ψ : AddChar K ℂ) (hψ : IsLocallyConstant ψ) (hne : ∃ t, ψ t ≠ 1) :
    ∃ d : K, d ≠ 0 ∧ ∀ t : K, (∀ x : K, ‖x‖ ≤ 1 → ψ (x * t) = 1) ↔ ‖t‖ ≤ ‖d‖ := by
  obtain ⟨t0, ht0⟩ := hne
  set D : Set K := {t | ∀ x : K, ‖x‖ ≤ 1 → ψ (x * t) = 1} with hD
  have hdown : ∀ s ∈ D, s ≠ 0 → ∀ t : K, ‖t‖ ≤ ‖s‖ → ψ t = 1 := by
    intro s hs hs0 t ht
    have := hs (t / s) (by rw [norm_div]; exact div_le_one_of_le₀ ht (norm_nonneg _))
    rwa [div_mul_cancel₀ _ hs0] at this
  have hcl : IsClosed D := by
    have : D = ⋂ x : K, ⋂ _ : ‖x‖ ≤ 1, (fun t => ψ (x * t)) ⁻¹' {1} := by
      ext t; simp [hD]
    rw [this]
    refine isClosed_iInter fun x => isClosed_iInter fun _ => ?_
    exact isClosed_singleton.preimage (hψ.continuous.comp (continuous_const.mul continuous_id))
  have hbd : D ⊆ closedBall 0 ‖t0‖ := by
    intro s hs
    rw [mem_closedBall_zero_iff]
    by_contra h
    push Not at h
    have hs0 : s ≠ 0 := by
      rintro rfl
      simp at h
      exact absurd h (not_lt.2 (norm_nonneg _))
    exact ht0 (hdown s hs hs0 t0 h.le)
  have hc : IsCompact D := (isCompact_closedBall 0 ‖t0‖).of_isClosed_subset hcl hbd
  have hop : IsOpen (ψ ⁻¹' {1}) := hψ _
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hop 0 (by simp)
  obtain ⟨e, he0, heε⟩ := NormedField.exists_norm_lt K hε
  have heD : e ∈ D := by
    intro x hx
    apply hball
    rw [mem_ball_zero_iff, norm_mul]
    exact lt_of_le_of_lt (mul_le_of_le_one_left (norm_nonneg _) hx) heε
  obtain ⟨d, hdD, hd⟩ := hc.exists_isMaxOn ⟨e, heD⟩ continuous_norm.continuousOn
  have hd0 : d ≠ 0 := by
    have : ‖e‖ ≤ ‖d‖ := hd heD
    exact norm_pos_iff.1 (lt_of_lt_of_le he0 this)
  refine ⟨d, hd0, fun t => ⟨fun ht => hd ht, fun ht x hx => hdown d hdD hd0 _ ?_⟩⟩
  rw [norm_mul]
  exact (mul_le_of_le_one_left (norm_nonneg _) hx).trans ht

omit [IsUltrametricDist K] [ProperSpace K] in
private lemma cond_pi (ψ : AddChar K ℂ) {d : K}
    (hd : ∀ t : K, (∀ x : K, ‖x‖ ≤ 1 → ψ (x * t) = 1) ↔ ‖t‖ ≤ ‖d‖)
    {κ : Type} [Fintype κ] {c : K} (hc : c ≠ 0) (y : κ → K) :
    (∀ x : κ → K, ‖x‖ ≤ ‖c‖ → ψ (dotProduct x y) = 1) ↔ ‖y‖ ≤ ‖d / c‖ := by
  classical
  have hc' : 0 < ‖c‖ := norm_pos_iff.2 hc
  constructor
  · intro h
    rw [pi_norm_le_iff_of_nonneg (norm_nonneg _)]
    intro i
    rw [norm_div, le_div_iff₀ hc', ← norm_mul, ← hd]
    intro x hx
    have := h (Pi.single i (x * c)) (by
      rw [Pi.norm_single, norm_mul]; exact mul_le_of_le_one_left (norm_nonneg _) hx)
    rw [single_dotProduct] at this
    rw [← this]; congr 1; ring
  · intro h x hx
    have key : ∀ s : Finset κ, ψ (∑ i ∈ s, x i * y i) = 1 := by
      intro s
      induction s using Finset.induction_on with
      | empty => simp
      | insert i s hi ih =>
        rw [Finset.sum_insert hi, AddChar.map_add_eq_mul, ih, mul_one]
        have h1 : ‖y i * c‖ ≤ ‖d‖ := by
          rw [norm_mul, ← le_div_iff₀ hc', ← norm_div]
          exact (norm_le_pi_norm y i).trans h
        have h2 := (hd _).2 h1 (x i / c) (by
          rw [norm_div]
          exact div_le_one_of_le₀ ((norm_le_pi_norm x i).trans hx) (norm_nonneg _))
        rw [← h2]; congr 1; field_simp
    exact key _

omit [IsUltrametricDist K] [ProperSpace K] in
private lemma unif {κ : Type} [Fintype κ] {f : (κ → K) → ℂ} (h1 : IsLocallyConstant f)
    (h2 : HasCompactSupport f) :
    ∃ e : K, e ≠ 0 ∧ ∀ u : κ → K, ‖u‖ ≤ ‖e‖ → ∀ x, f (x + u) = f x := by
  obtain ⟨δ, hδ, h⟩ := lebesgue_number_lemma_of_metric (c := fun z : ℂ => f ⁻¹' {z}) h2
    (fun z => h1 _) (fun x _ => by simp)
  obtain ⟨e, he0, heδ⟩ := NormedField.exists_norm_lt K hδ
  refine ⟨e, norm_pos_iff.1 he0, fun u hu x => ?_⟩
  have hlt : ‖u‖ < δ := lt_of_le_of_lt hu heδ
  by_cases hx : x ∈ tsupport f
  · obtain ⟨z, hz⟩ := h x hx
    have a1 : f x = z := hz (mem_ball_self hδ)
    have a2 : f (x + u) = z := hz (by simpa [mem_ball, dist_eq_norm] using hlt)
    rw [a1, a2]
  · by_cases hx' : x + u ∈ tsupport f
    · obtain ⟨z, hz⟩ := h _ hx'
      have a1 : f (x + u) = z := hz (mem_ball_self hδ)
      have a2 : f x = z := hz (by simpa [mem_ball, dist_eq_norm] using hlt)
      rw [a1, a2]
    · rw [image_eq_zero_of_notMem_tsupport hx, image_eq_zero_of_notMem_tsupport hx']

omit [IsUltrametricDist K] [ProperSpace K] in
private lemma bdd {κ : Type} [Fintype κ] {f : (κ → K) → ℂ}
    (h2 : HasCompactSupport f) :
    ∃ c : K, c ≠ 0 ∧ ∀ x : κ → K, ¬ ‖x‖ ≤ ‖c‖ → f x = 0 := by
  obtain ⟨R, hR⟩ := h2.isCompact.isBounded.subset_closedBall 0
  obtain ⟨c, hc⟩ := NormedField.exists_lt_norm K (max R 0)
  refine ⟨c, norm_pos_iff.1 (lt_of_le_of_lt (le_max_right _ _) hc), fun x hx => ?_⟩
  apply image_eq_zero_of_notMem_tsupport
  intro h
  have := mem_closedBall_zero_iff.1 (hR h)
  exact hx (this.trans ((le_max_left _ _).trans hc.le))

omit [IsUltrametricDist K] in
private lemma sb_of {κ : Type} [Fintype κ] {f : (κ → K) → ℂ} {e c : K} (he : e ≠ 0)
    (h1 : ∀ u : κ → K, ‖u‖ ≤ ‖e‖ → ∀ x, f (x + u) = f x)
    (h2 : ∀ x : κ → K, ¬ ‖x‖ ≤ ‖c‖ → f x = 0) :
    IsLocallyConstant f ∧ HasCompactSupport f := by
  constructor
  · rw [IsLocallyConstant.iff_eventually_eq]
    intro x
    filter_upwards [closedBall_mem_nhds x (norm_pos_iff.2 he)] with y hy
    rw [mem_closedBall, dist_eq_norm] at hy
    simpa using h1 (y - x) hy x
  · exact HasCompactSupport.intro (isCompact_closedBall 0 ‖c‖)
      (fun x hx => h2 x (by simpa using hx))

end

section
variable {K : Type} [NontriviallyNormedField K] [IsUltrametricDist K] [ProperSpace K]
  {κ : Type} [Fintype κ] [MeasurableSpace (κ → K)] [BorelSpace (κ → K)]
  (μ : Measure (κ → K)) [μ.IsAddHaarMeasure] (ψ : AddChar K ℂ)

private noncomputable def four (f : (κ → K) → ℂ) (y : κ → K) : ℂ :=
  ∫ x, ψ (dotProduct x y) * f x ∂μ

omit [IsUltrametricDist K] [ProperSpace K] in
private lemma four_transl (f : (κ → K) → ℂ) (a y : κ → K) :
    four μ ψ (fun x => f (x + a)) y = ψ (-(dotProduct a y)) * four μ ψ f y := by
  unfold four
  rw [← integral_add_right_eq_self (fun x => ψ (dotProduct x y) * f x) a, ← integral_const_mul]
  congr 1
  ext x
  rw [← mul_assoc, ← AddChar.map_add_eq_mul, add_dotProduct]
  congr 2
  ring

omit [IsUltrametricDist K] [ProperSpace K] [BorelSpace (κ → K)] [μ.IsAddHaarMeasure] in
private lemma four_mod (f : (κ → K) → ℂ) (b y : κ → K) :
    four μ ψ (fun x => ψ (dotProduct x b) * f x) y = four μ ψ f (y + b) := by
  unfold four
  congr 1
  ext x
  rw [← mul_assoc, ← AddChar.map_add_eq_mul, dotProduct_add]

variable {d : K} (hd : ∀ t : K, (∀ x : K, ‖x‖ ≤ 1 → ψ (x * t) = 1) ↔ ‖t‖ ≤ ‖d‖)
include hd

omit [IsUltrametricDist K] [ProperSpace K] in
private lemma four_supp {f : (κ → K) → ℂ} {e : K} (he : e ≠ 0)
    (h1 : ∀ u : κ → K, ‖u‖ ≤ ‖e‖ → ∀ x, f (x + u) = f x) (y : κ → K) (hy : ¬ ‖y‖ ≤ ‖d / e‖) :
    four μ ψ f y = 0 := by
  rw [← cond_pi ψ hd he] at hy
  push Not at hy
  obtain ⟨u, hu, hne⟩ := hy
  have := four_transl μ ψ f (-u) y
  rw [show (fun x => f (x + -u)) = f from funext (h1 _ (by simpa using hu)), neg_dotProduct,
    neg_neg] at this
  by_contra h
  apply hne
  exact (mul_right_cancel₀ h (this.symm.trans (one_mul _).symm))

omit [IsUltrametricDist K] [ProperSpace K] [BorelSpace (κ → K)] [μ.IsAddHaarMeasure] in
private lemma four_inv {f : (κ → K) → ℂ} {c : K} (hc : c ≠ 0)
    (h2 : ∀ x : κ → K, ¬ ‖x‖ ≤ ‖c‖ → f x = 0) (u : κ → K) (hu : ‖u‖ ≤ ‖d / c‖) (y : κ → K) :
    four μ ψ f (y + u) = four μ ψ f y := by
  rw [← four_mod]
  congr 1
  ext x
  by_cases hx : ‖x‖ ≤ ‖c‖
  · rw [(cond_pi ψ hd hc u).2 hu x hx, one_mul]
  · rw [h2 x hx, mul_zero]

omit [IsUltrametricDist K] in
private lemma four_sb (hd0 : d ≠ 0) {f : (κ → K) → ℂ} (h1 : IsLocallyConstant f)
    (h2 : HasCompactSupport f) :
    IsLocallyConstant (four μ ψ f) ∧ HasCompactSupport (four μ ψ f) := by
  obtain ⟨e, he, h1⟩ := unif h1 h2
  obtain ⟨c, hc, h2⟩ := bdd h2
  exact sb_of (div_ne_zero hd0 hc) (four_inv μ ψ hd hc h2) (four_supp μ ψ hd he h1)

omit hd [ProperSpace K] [MeasurableSpace (κ → K)] [BorelSpace (κ → K)] in
private lemma ind_inv (r : ℝ) (u : κ → K) (hu : ‖u‖ ≤ r) (x : κ → K) :
    (closedBall (0 : κ → K) r).indicator (fun _ => (1 : ℂ)) (x + u) =
      (closedBall (0 : κ → K) r).indicator (fun _ => (1 : ℂ)) x := by
  have : x + u ∈ closedBall (0 : κ → K) r ↔ x ∈ closedBall (0 : κ → K) r := by
    simp only [mem_closedBall_zero_iff]
    constructor
    · intro h
      have := IsUltrametricDist.norm_add_le_max (x + u) (-u)
      rw [add_neg_cancel_right, norm_neg] at this
      exact this.trans (max_le h hu)
    · intro h
      exact (IsUltrametricDist.norm_add_le_max x u).trans (max_le h hu)
  by_cases hx : x ∈ closedBall (0 : κ → K) r
  · rw [Set.indicator_of_mem hx, Set.indicator_of_mem (this.2 hx)]
  · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem (fun h => hx (this.1 h))]

omit [ProperSpace K] in
private lemma four_ind {c : K} (hc : c ≠ 0) (y : κ → K) :
    four μ ψ ((closedBall (0 : κ → K) ‖c‖).indicator (fun _ => (1 : ℂ))) y =
      (μ.real (closedBall 0 ‖c‖) : ℂ) *
        (closedBall (0 : κ → K) ‖d / c‖).indicator (fun _ => (1 : ℂ)) y := by
  by_cases hy : ‖y‖ ≤ ‖d / c‖
  · have := four_inv μ ψ hd hc
      (f := (closedBall (0 : κ → K) ‖c‖).indicator (fun _ => (1 : ℂ)))
      (fun x hx => Set.indicator_of_notMem (by simpa using hx) _) y hy 0
    rw [zero_add] at this
    rw [this, Set.indicator_of_mem (by simpa using hy), mul_one]
    unfold four
    simp only [dotProduct_zero, AddChar.map_zero_eq_one, one_mul]
    rw [integral_indicator_const _ measurableSet_closedBall]
    simp
  · rw [four_supp μ ψ hd hc (ind_inv _) y hy, Set.indicator_of_notMem (by simpa using hy),
      mul_zero]

private lemma four_four (hψ : IsLocallyConstant ψ) (hd0 : d ≠ 0) {f : (κ → K) → ℂ}
    (h1 : IsLocallyConstant f) (h2 : HasCompactSupport f) :
    ∃ C : ℂ, C ≠ 0 ∧ ∀ z, four μ ψ (four μ ψ f) z = C * f (-z) := by
  obtain ⟨e, he, hinv⟩ := unif h1 h2
  have hde : d / e ≠ 0 := div_ne_zero hd0 he
  have hpos : ∀ c : K, c ≠ 0 → (μ.real (closedBall (0 : κ → K) ‖c‖) : ℂ) ≠ 0 := by
    intro c hc
    have h3 := measure_closedBall_pos μ (0 : κ → K) (norm_pos_iff.2 hc)
    have h4 : μ (closedBall (0 : κ → K) ‖c‖) < ⊤ := measure_closedBall_lt_top
    exact_mod_cast (ENNReal.toReal_pos h3.ne' h4.ne).ne'
  refine ⟨(μ.real (closedBall (0 : κ → K) ‖d / e‖) : ℂ) * (μ.real (closedBall (0 : κ → K) ‖e‖) : ℂ),
    mul_ne_zero (hpos _ hde) (hpos _ he), fun z => ?_⟩
  set χ : (κ → K) → ℂ := (closedBall (0 : κ → K) ‖d / e‖).indicator (fun _ => (1 : ℂ)) with hχ
  have hχsb : IsLocallyConstant χ ∧ HasCompactSupport χ :=
    sb_of (c := d / e) hde (ind_inv _) (fun x hx => Set.indicator_of_notMem (by simpa using hx) _)
  have hcψ := hψ.continuous
  have hcχ := hχsb.1.continuous
  have hcf := h1.continuous
  have step1 : four μ ψ (four μ ψ f) z =
      ∫ y, ∫ x, ψ (dotProduct y (x + z)) * χ y * f x ∂μ ∂μ := by
    change ∫ y, ψ (dotProduct y z) * four μ ψ f y ∂μ = _
    congr 1
    ext y
    have : four μ ψ f y = χ y * four μ ψ f y := by
      by_cases hy : ‖y‖ ≤ ‖d / e‖
      · rw [hχ, Set.indicator_of_mem (by simpa using hy), one_mul]
      · rw [four_supp μ ψ hd he hinv y hy, mul_zero]
    rw [this]
    unfold four
    rw [← integral_const_mul, ← integral_const_mul]
    congr 1
    ext x
    rw [dotProduct_add, AddChar.map_add_eq_mul, dotProduct_comm y x]
    ring
  rw [step1, integral_integral_swap_of_hasCompactSupport]
  · have : ∀ x, ∫ y, ψ (dotProduct y (x + z)) * χ y * f x ∂μ =
        ((μ.real (closedBall (0 : κ → K) ‖d / e‖) : ℂ) * f (-z)) *
          (closedBall (0 : κ → K) ‖e‖).indicator (fun _ => (1 : ℂ)) (x + z) := by
      intro x
      rw [integral_mul_const]
      have h5 := four_ind μ ψ hd hde (x + z)
      rw [show d / (d / e) = e by field_simp] at h5
      change four μ ψ χ (x + z) * f x = _
      rw [h5]
      by_cases hx : ‖x + z‖ ≤ ‖e‖
      · have := hinv _ hx (-z)
        rw [show -z + (x + z) = x by abel] at this
        rw [this]; ring
      · rw [Set.indicator_of_notMem (by simpa using hx)]; ring
    simp_rw [this]
    rw [integral_const_mul, integral_add_right_eq_self
      ((closedBall (0 : κ → K) ‖e‖).indicator (fun _ => (1 : ℂ))) z,
      integral_indicator_const _ measurableSet_closedBall]
    simp only [Complex.real_smul]
    ring
  · have hdot : Continuous fun p : (κ → K) × (κ → K) => dotProduct p.1 (p.2 + z) := by
      unfold dotProduct
      fun_prop
    exact ((hcψ.comp hdot).mul (hcχ.comp continuous_fst)).mul (hcf.comp continuous_snd)
  · refine HasCompactSupport.intro (hχsb.2.isCompact.prod h2.isCompact) ?_
    rintro ⟨y, x⟩ h
    simp only [Set.mem_prod, not_and_or] at h
    rcases h with h | h
    · simp [Function.uncurry, image_eq_zero_of_notMem_tsupport h]
    · simp [Function.uncurry, image_eq_zero_of_notMem_tsupport h]

end

theorem UpperTheory.fourier_transform_bijective :
    ∀ (K : Type) [NontriviallyNormedField K] [IsUltrametricDist K] [ProperSpace K] (ψ : AddChar K ℂ),
        IsLocallyConstant ψ → (∃ t, ψ t ≠ 1) → ∀ (κ : Type) [Fintype κ],
        ∃ T : ((κ → K) → ℂ) →ₗ[ℂ] ((κ → K) → ℂ),
          Set.BijOn T {f | IsLocallyConstant f ∧ HasCompactSupport f} {f | IsLocallyConstant f ∧ HasCompactSupport f} ∧
          (∀ f : (κ → K) → ℂ, IsLocallyConstant f → HasCompactSupport f → ∀ a y : κ → K,
            T (fun x => f (x + a)) y = ψ (-(dotProduct a y)) * T f y) ∧
          (∀ f : (κ → K) → ℂ, IsLocallyConstant f → HasCompactSupport f → ∀ b y : κ → K,
            T (fun x => ψ (dotProduct x b) * f x) y = T f (y + b)) := by
  intro K _ _ _ ψ hψ hne κ _
  obtain ⟨d, hd0, hd⟩ := cond_one ψ hψ hne
  letI : MeasurableSpace (κ → K) := borel _
  haveI : BorelSpace (κ → K) := ⟨rfl⟩
  let μ : Measure (κ → K) := Measure.addHaar
  let S : Submodule ℂ ((κ → K) → ℂ) :=
    { carrier := {f | IsLocallyConstant f ∧ HasCompactSupport f}
      add_mem' := fun ha hb => ⟨ha.1.add hb.1, ha.2.add hb.2⟩
      zero_mem' := ⟨IsLocallyConstant.const 0, HasCompactSupport.zero⟩
      smul_mem' := fun c f hf => ⟨hf.1.comp (fun t => c • t), hf.2.comp_left (g := fun t => c • t) (by simp)⟩ }
  have hlc : ∀ y : κ → K, IsLocallyConstant (fun x : κ → K => ψ (dotProduct x y)) := by
    intro y
    have hdot : Continuous fun x : κ → K => dotProduct x y := by
      unfold dotProduct
      fun_prop
    exact hψ.comp_continuous hdot
  have hint : ∀ f ∈ S, ∀ y, Integrable (fun x => ψ (dotProduct x y) * f x) μ := by
    intro f hf y
    exact ((hlc y).continuous.mul hf.1.continuous).integrable_of_hasCompactSupport hf.2.mul_left
  let T0 : S →ₗ[ℂ] ((κ → K) → ℂ) :=
    { toFun := fun f => four μ ψ f
      map_add' := fun f g => by
        ext y
        simp only [four, Submodule.coe_add, Pi.add_apply, mul_add]
        exact integral_add (hint f f.2 y) (hint g g.2 y)
      map_smul' := fun c f => by
        ext y
        simp only [four, Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
        rw [← integral_const_mul]
        congr 1
        ext x
        ring }
  obtain ⟨T, hT⟩ := LinearMap.exists_extend T0
  have hT' : ∀ f ∈ S, T f = four μ ψ f := fun f hf => LinearMap.congr_fun hT ⟨f, hf⟩
  have hmap : ∀ f ∈ S, T f ∈ S := fun f hf => by
    rw [hT' f hf]; exact four_sb μ ψ hd hd0 hf.1 hf.2
  have hTT : ∀ f ∈ S, ∃ C : ℂ, C ≠ 0 ∧ ∀ z, T (T f) z = C * f (-z) := fun f hf => by
    rw [hT' _ (hmap f hf), hT' f hf]; exact four_four μ ψ hd hψ hd0 hf.1 hf.2
  refine ⟨T, ⟨hmap, ?_, ?_⟩, ?_, ?_⟩
  · intro f hf g hg h
    obtain ⟨C, hC, h1⟩ := hTT (f - g) (S.sub_mem hf hg)
    ext z
    have := h1 (-z)
    rw [map_sub, h, sub_self, map_zero, neg_neg] at this
    have := (mul_eq_zero.1 this.symm).resolve_left hC
    exact sub_eq_zero.1 this
  · intro g hg
    have hg' : (fun x => g (-x)) ∈ S :=
      ⟨hg.1.comp_continuous continuous_neg, hg.2.comp_homeomorph (Homeomorph.neg _)⟩
    obtain ⟨C, hC, h1⟩ := hTT _ hg'
    refine ⟨C⁻¹ • T (fun x => g (-x)), S.smul_mem _ (hmap _ hg'), ?_⟩
    ext z
    rw [map_smul, Pi.smul_apply, h1, neg_neg, smul_eq_mul, inv_mul_cancel_left₀ hC]
  · intro f h1 h2 a y
    have : (fun x => f (x + a)) ∈ S :=
      ⟨h1.comp_continuous (continuous_add_const a), h2.comp_homeomorph (Homeomorph.addRight a)⟩
    rw [hT' _ this, hT' f ⟨h1, h2⟩, four_transl]
  · intro f h1 h2 b y
    have : (fun x => ψ (dotProduct x b) * f x) ∈ S := ⟨(hlc b).mul h1, h2.mul_left⟩
    rw [hT' _ this, hT' f ⟨h1, h2⟩, four_mod]
