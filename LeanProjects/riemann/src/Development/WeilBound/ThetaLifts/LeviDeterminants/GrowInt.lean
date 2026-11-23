import Development.WeilBound.ThetaLifts.LeviDeterminants.ContinuousOfMem
import Development.AutomorphicSpectrum.Proofs.MembershipProofs.ThetaDistributionNonzeroAdmissible
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardTraceAdelicAddCharLocalComponentNeOne

noncomputable section

namespace PositivityTheory.ThKF0.Grow

open scoped Matrix NNReal ENNReal Classical SchwartzMap LineDeriv
open NumberField IsDedekindDomain MeasureTheory Filter Topology GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] {ψ : AddChar (AF F) ℂ}

omit [Fintype κ] in
theorem exists_major {μ : @Measure (κ → AF F) (borel _)} {G₁ G₂ : (κ → AF F) → ℂ} (h₁ : Continuous G₁) (h₂ : Continuous G₂)
    (f₁ : nsq μ G₁ < ⊤) (f₂ : nsq μ G₂ < ⊤) :
    ∃ G : (κ → AF F) → ℂ, Continuous G ∧ nsq μ G < ⊤ ∧ ∀ x, ‖G₁ x‖ + ‖G₂ x‖ ≤ ‖G x‖ := by
  have c₁ : Continuous fun x => ((‖G₁ x‖ : ℝ) : ℂ) := Complex.continuous_ofReal.comp h₁.norm
  have c₂ : Continuous fun x => ((‖G₂ x‖ : ℝ) : ℂ) := Complex.continuous_ofReal.comp h₂.norm
  have e : ∀ G : (κ → AF F) → ℂ, nsq μ (fun x => ((‖G x‖ : ℝ) : ℂ)) = nsq μ G := fun G => by
    unfold nsq
    simp only [← ofReal_norm_eq_enorm, Complex.norm_real, norm_norm]
  refine ⟨(fun x => ((‖G₁ x‖ : ℝ) : ℂ)) + fun x => ((‖G₂ x‖ : ℝ) : ℂ), c₁.add c₂, (nsq_add_le μ c₁ _).trans_lt ?_, fun x => ?_⟩
  · rw [e, e]
    exact ENNReal.add_lt_top.2 ⟨ENNReal.mul_lt_top (by simp) f₁, ENNReal.mul_lt_top (by simp) f₂⟩
  · rw [Pi.add_apply, ← Complex.ofReal_add, Complex.norm_real]
    exact le_abs_self _

omit [Fintype κ] in
theorem emb_zero : emb (0 : V F κ × V F κ) = 0 := by
  have : inf (0 : mixedEmbedding.mixedSpace F) = 0 := Prod.ext (map_zero (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm) rfl
  exact Prod.ext (funext fun _ => this) (funext fun _ => this)

theorem schr_zero (Φ : (κ → AF F) → ℂ) (w : V F κ × V F κ) : schr ψ (emb ((0 : ℝ) • w)) Φ = Φ := by
  funext x; simp [emb_zero, schr]

theorem exists_dom (hψ : IsStd ψ) {μ : @Measure (κ → AF F) (borel _)} (hμ : IsHaar μ) (w : V F κ × V F κ)
    {Φ : (κ → AF F) → ℂ} (hΦ : Φ ∈ schA F κ) : ∃ G : (κ → AF F) → ℂ, Continuous G ∧ nsq μ G < ⊤ ∧
      ∀ t : ℝ, |t| ≤ 1 → ∀ x, ‖schr ψ (emb (t • w)) Φ x - Φ x‖ ≤ |t| * ‖G x‖ := by
  induction hΦ using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨f, g, hg, rfl⟩ := hx
    obtain ⟨k, hk⟩ := weight_lt_top (F := F) (κ := κ)
    obtain ⟨K, hK0, hK⟩ := lineD_bound f w.1 0 (linForm w.2) (qc w) k
    have hu : Continuous fun z : V F κ => ((K * ((1 + ‖z‖) ^ k)⁻¹ : ℝ) : ℂ) :=
      Complex.continuous_ofReal.comp (continuous_const.mul (Continuous.inv₀ (by fun_prop) fun z => by positivity))
    refine ⟨pureA F (fun z => ((K * ((1 + ‖z‖) ^ k)⁻¹ : ℝ) : ℂ)) g, ?_, nsq_pure_lt_top hμ hu (hk K) hg, fun t ht x => ?_⟩
    · have h := PositivityTheory.ThKF0.Split.continuous_splitE_symm F κ
      exact (hu.comp h.fst).mul (hg.1.continuous.comp h.snd)
    · have e := congrFun (schr_zero (ψ := ψ) (pureA F f g) w) x
      rw [← e, schr_emb hψ, schr_emb hψ, ← sub_mul, norm_mul, pureA, norm_mul, ← mul_assoc]
      refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
      have := (convex_Icc (-1 : ℝ) 1).norm_image_sub_le_of_norm_hasDerivWithin_le
        (f := lineFn f w.1 (linForm w.2) (qc w) fun i => evI F (x i))
        (fun s _ => (hasDerivAt_lineFn f w.1 (linForm w.2) (qc w) _ s).hasDerivWithinAt)
        (fun s hs => by simpa only [add_zero] using hK (fun i => evI F (x i)) s (abs_le.2 hs))
        (x := 0) (y := t) ⟨by norm_num, by norm_num⟩ (abs_le.1 ht)
      rw [sub_zero, Real.norm_eq_abs, mul_comm] at this
      refine this.trans (mul_le_mul_of_nonneg_left ?_ (abs_nonneg _))
      rw [Complex.norm_real]
      exact le_abs_self _
  | zero => exact ⟨0, continuous_const, by simp [nsq], fun t _ x => by simp [schr]⟩
  | add a b _ _ h h' =>
    obtain ⟨G₁, c₁, f₁, h⟩ := h
    obtain ⟨G₂, c₂, f₂, h'⟩ := h'
    obtain ⟨G, c, f, hG⟩ := exists_major c₁ c₂ f₁ f₂
    refine ⟨G, c, f, fun t ht x => ?_⟩
    rw [schr_add, Pi.add_apply, Pi.add_apply, add_sub_add_comm]
    refine (norm_add_le _ _).trans ((add_le_add (h t ht x) (h' t ht x)).trans ?_)
    rw [← mul_add]
    exact mul_le_mul_of_nonneg_left (hG x) (abs_nonneg _)
  | smul c a _ h =>
    obtain ⟨G, c₁, f₁, h⟩ := h
    refine ⟨c • G, c₁.const_smul c, by rw [nsq_smul]; exact ENNReal.mul_lt_top (by simp [enorm_eq_nnnorm]) f₁,
      fun t ht x => ?_⟩
    rw [schr_smul, Pi.smul_apply, Pi.smul_apply, Pi.smul_apply, ← smul_sub, norm_smul, norm_smul, mul_left_comm]
    exact mul_le_mul_of_nonneg_left (h t ht x) (norm_nonneg _)

theorem slope_tendsto {φ : ℝ → ℂ} {d : ℂ} (h : HasDerivAt φ d 0) :
    Tendsto (fun n : ℕ => ((n : ℂ) + 1) * (φ (1 / ((n : ℝ) + 1)) - φ 0)) atTop (𝓝 d) := by
  have h1 : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.2 ⟨tendsto_one_div_add_atTop_nhds_zero_nat, Eventually.of_forall fun n => Set.mem_Ioi.2 Nat.one_div_pos_of_nat⟩
  refine (h.tendsto_slope_zero_right.comp h1).congr fun n => ?_
  simp

theorem schr_mem (hψ : IsStd ψ) (w : Pt F κ) {Φ : (κ → AF F) → ℂ} (hΦ : Φ ∈ schA F κ) : schr ψ w Φ ∈ schA F κ := by
  obtain ⟨v⟩ : Nonempty (Pl F) := by
    obtain ⟨m, hm⟩ := Ideal.exists_maximal (𝓞 F)
    exact ⟨⟨m, hm.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField hm (RingOfIntegers.not_isField F)⟩⟩
  exact (GlobalTheory.CompanionTheory.AdelicHeis.schr_mem_and_thetaSum F κ ψ hψ.1
    (fun h => GlobalTheory.PsiNontriv.psiV_ne_one ψ hψ v (by rw [h]; rfl)) hψ.2.1).1 _ _ hΦ

theorem Impl.dR (hψ : IsStd ψ) {μ : @Measure (κ → AF F) (borel _)} (hμ : IsHaar μ) {T : Module.End ℂ ((κ → AF F) → ℂ)}
    {s : Pt F κ →ₗ[AF F] Pt F κ} (hT : Impl ψ T s) {w w' : V F κ × V F κ} (hw : s (emb w) = emb w')
    {Φ : (κ → AF F) → ℂ} (hΦ : Φ ∈ schA F κ) : T (dR ψ w' Φ) = dR ψ w (T Φ) := by
  letI mA : MeasurableSpace (κ → AF F) := borel _
  haveI : BorelSpace (κ → AF F) := ⟨rfl⟩
  haveI : μ.IsAddHaarMeasure := hμ
  let q : ℕ → (κ → AF F) → ℂ := fun n =>
    ((n : ℂ) + 1) • (schr ψ (emb ((1 / ((n : ℝ) + 1)) • w')) Φ - Φ) - Grow.dR ψ w' Φ
  have hq : ∀ n, q n ∈ schA F κ := fun n =>
    sub_mem (Submodule.smul_mem _ _ (sub_mem (schr_mem hψ _ hΦ) hΦ)) (dR_mem hψ w' hΦ)
  have meas : ∀ Θ ∈ schA F κ, Measurable fun x => ‖Θ x‖ₑ ^ 2 := fun Θ h =>
    (continuous_of_mem h).measurable.enorm.pow_const 2
  obtain ⟨G₁, c₁, f₁, h₁⟩ := exists_dom hψ hμ w' hΦ
  obtain ⟨G, -, f, hG⟩ := exists_major c₁ (continuous_of_mem (dR_mem hψ w' hΦ)) f₁ (nsq_lt_top hμ (dR_mem hψ w' hΦ))
  have lim : ∀ {u : ℕ → ℂ} {a : ℂ}, Tendsto u atTop (𝓝 a) → Tendsto (fun n => ‖u n‖ₑ ^ 2) atTop (𝓝 (‖a‖ₑ ^ 2)) :=
    fun h => ((ENNReal.continuous_pow 2).tendsto _).comp h.enorm
  have t0 : Tendsto (fun n => nsq μ (q n)) atTop (𝓝 0) := by
    have := tendsto_lintegral_of_dominated_convergence (μ := μ) (F := fun n x => ‖q n x‖ₑ ^ 2) (f := fun _ => 0)
      (fun x => ‖G x‖ₑ ^ 2) (fun n => meas _ (hq n)) (fun n => Eventually.of_forall fun x => ?_) f.ne
      (Eventually.of_forall fun x => ?_)
    · rw [lintegral_zero] at this
      exact this
    · refine pow_le_pow_left' (enorm_le_iff_norm_le.2 ((norm_sub_le _ _).trans (le_trans ?_ (hG x)))) 2
      have hp : (0 : ℝ) < (n : ℝ) + 1 := by positivity
      have h1 := h₁ (1 / ((n : ℝ) + 1)) (by
        rw [abs_of_pos (by positivity), div_le_one hp]; linarith [Nat.cast_nonneg (α := ℝ) n]) x
      rw [abs_of_pos (by positivity), one_div ((n : ℝ) + 1), inv_mul_eq_div, le_div_iff₀ hp, mul_comm, ← one_div] at h1
      refine add_le_add_left (le_trans (le_of_eq ?_) h1) _
      rw [Pi.smul_apply, norm_smul, Pi.sub_apply]
      congr 1
      rw [← Nat.cast_succ, Complex.norm_natCast, Nat.cast_succ]
    · have h := (slope_tendsto (hasDerivAt_dR hψ w' hΦ x)).sub_const (Grow.dR ψ w' Φ x)
      rw [sub_self, schr_zero] at h
      have h2 := lim h
      rw [enorm_zero, zero_pow two_ne_zero] at h2
      exact h2
  have hD : Grow.dR ψ w (T Φ) - T (Grow.dR ψ w' Φ) ∈ schA F κ :=
    sub_mem (dR_mem hψ w (hT.pres _ hΦ)) (hT.pres _ (dR_mem hψ w' hΦ))
  have t1 : ∀ x, Tendsto (fun n => T (q n) x) atTop (𝓝 ((Grow.dR ψ w (T Φ) - T (Grow.dR ψ w' Φ)) x)) := fun x => by
    have h := (slope_tendsto (hasDerivAt_dR hψ w (hT.pres _ hΦ) x)).sub_const (T (Grow.dR ψ w' Φ) x)
    rw [schr_zero] at h
    refine h.congr fun n => ?_
    have e : emb ((1 / ((n : ℝ) + 1)) • w') = s (emb ((1 / ((n : ℝ) + 1)) • w)) := by
      rw [emb_smul, emb_smul, map_smul, hw]
    simp only [q, map_sub, map_smul, e, hT.impl _ _ hΦ]
    rfl
  have t2 : nsq μ (Grow.dR ψ w (T Φ) - T (Grow.dR ψ w' Φ)) = 0 := by
    have h : ∫⁻ x, liminf (fun n => ‖T (q n) x‖ₑ ^ 2) atTop ∂μ ≤ liminf (fun n => ∫⁻ x, ‖T (q n) x‖ₑ ^ 2 ∂μ) atTop :=
      lintegral_liminf_le fun n => meas _ (hT.pres _ (hq n))
    simp only [fun x => (lim (t1 x)).liminf_eq] at h
    have e : (fun n => ∫⁻ x, ‖T (q n) x‖ₑ ^ 2 ∂μ) = fun n => nsq μ (q n) := funext fun n => hT.unit μ hμ _ (hq n)
    rw [e, t0.liminf_eq] at h
    exact le_antisymm h zero_le
  have t3 := (lintegral_eq_zero_iff (meas _ hD)).1 t2
  have t4 : (Grow.dR ψ w (T Φ) - T (Grow.dR ψ w' Φ)) =ᵐ[μ] 0 := t3.mono fun x hx => by simpa using hx
  exact (sub_eq_zero.1 (((continuous_of_mem hD).ae_eq_iff_eq μ continuous_const).1 t4)).symm

theorem dR_add (hψ : IsStd ψ) (w : V F κ × V F κ) {Φ Ψ : (κ → AF F) → ℂ} (hΦ : Φ ∈ schA F κ) (hΨ : Ψ ∈ schA F κ) :
    dR ψ w (Φ + Ψ) = dR ψ w Φ + dR ψ w Ψ := funext fun x => by
  have := (hasDerivAt_dR hψ w hΦ x).fun_add (hasDerivAt_dR hψ w hΨ x)
  simp only [dR, schr_add] at this ⊢
  exact this.deriv

theorem dR_smul (hψ : IsStd ψ) (w : V F κ × V F κ) (c : ℂ) {Φ : (κ → AF F) → ℂ} (hΦ : Φ ∈ schA F κ) :
    dR ψ w (c • Φ) = c • dR ψ w Φ := funext fun x => by
  have := (hasDerivAt_dR hψ w hΦ x).const_mul c
  simp only [dR, schr_smul] at this ⊢
  exact this.deriv

theorem word_mem (hψ : IsStd ψ) (l : List (V F κ × V F κ)) {Φ : (κ → AF F) → ℂ} (hΦ : Φ ∈ schA F κ) :
    word ψ l Φ ∈ schA F κ := by
  induction l with
  | nil => exact hΦ
  | cons w l ih => exact dR_mem hψ w ih

def wordL (hψ : IsStd ψ) (l : List (V F κ × V F κ)) : schA F κ →ₗ[ℂ] (κ → AF F) → ℂ where
  toFun Φ := word ψ l Φ
  map_add' Φ Ψ := by
    induction l with
    | nil => rfl
    | cons w l ih => exact (congrArg (dR ψ w) ih).trans (dR_add hψ w (word_mem hψ l Φ.2) (word_mem hψ l Ψ.2))
  map_smul' c Φ := by
    induction l with
    | nil => rfl
    | cons w l ih => exact (congrArg (dR ψ w) ih).trans (dR_smul hψ w c (word_mem hψ l Φ.2))

theorem linForm_sum {ι : Type} [Fintype ι] (a : ι → ℝ) (b : ι → V F κ) (p : V F κ) :
    linForm (∑ j, a j • b j) p = ∑ j, a j * linForm (b j) p := by
  simp only [linForm_apply, Finset.sum_apply, Pi.smul_apply, Finset.mul_sum, mul_smul_comm, map_sum, map_smul, smul_eq_mul]
  exact Finset.sum_comm

theorem dR_sum (hψ : IsStd ψ) {ι : Type} [Fintype ι] (a : ι → ℝ) (b : ι → V F κ × V F κ) {Φ : (κ → AF F) → ℂ}
    (hΦ : Φ ∈ schA F κ) : dR ψ (∑ j, a j • b j) Φ = ∑ j, (a j : ℂ) • dR ψ (b j) Φ := by
  induction hΦ using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨f, g, hg, rfl⟩ := hx
    funext x
    simp only [dR_pure hψ, Finset.sum_apply, Pi.smul_apply, pureA, dS_apply, Prod.fst_sum, Prod.snd_sum, Prod.smul_fst,
      Prod.smul_snd, linForm_sum, map_sum, map_smul, smul_eq_mul, Complex.real_smul, Complex.ofReal_sum, Complex.ofReal_mul,
      Finset.sum_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j _ => by ring
  | zero =>
    have : ∀ w : V F κ × V F κ, dR ψ w 0 = 0 := fun w => by
      have := dR_smul hψ w 0 (zero_mem (schA F κ))
      rwa [zero_smul, zero_smul] at this
    simp [this]
  | add x y hx hy h h' => simp only [dR_add hψ _ hx hy, h, h', smul_add, Finset.sum_add_distrib]
  | smul c x hx h => simp only [dR_smul hψ _ c hx, h, Finset.smul_sum, smul_comm c]

omit [Fintype κ] in
theorem nsq_sum_le (μ : @Measure (κ → AF F) (borel _)) {ι : Type} (s : Finset ι) (Θ : ι → (κ → AF F) → ℂ)
    (h : ∀ j, Continuous (Θ j)) : nsq μ (∑ j ∈ s, Θ j) ≤ 2 ^ s.card * ∑ j ∈ s, nsq μ (Θ j) := by
  induction s using Finset.induction_on with
  | empty => simp [nsq]
  | insert j s hj ih =>
    rw [Finset.sum_insert hj, Finset.sum_insert hj, Finset.card_insert_of_notMem hj, pow_succ', mul_add, mul_assoc, mul_assoc]
    refine (nsq_add_le μ (h j) _).trans (add_le_add (mul_le_mul' le_rfl ?_) (mul_le_mul' le_rfl ih))
    exact le_mul_of_one_le_left' (one_le_pow₀ one_le_two)

theorem word_bound (hψ : IsStd ψ) {μ : @Measure (κ → AF F) (borel _)} (hμ : IsHaar μ) (n : ℕ) :
    ∀ Φ ∈ schA F κ, ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ l : List (V F κ × V F κ), l.length = n → ∀ c : ℝ≥0, (∀ w ∈ l, ‖w‖ ≤ c) →
      nsq μ (word ψ l Φ) ≤ C * (c : ℝ≥0∞) ^ (2 * n) := by
  induction n with
  | zero =>
    intro Φ hΦ
    refine ⟨nsq μ Φ, (nsq_lt_top hμ hΦ).ne, fun l hl c _ => ?_⟩
    rw [List.length_eq_zero_iff.1 hl]
    simp [word]
  | succ n ih =>
    intro Φ hΦ
    let b := Module.finBasis ℝ (V F κ × V F κ)
    choose C hC hC' using fun j => ih _ (dR_mem hψ (b j) hΦ)
    let K : _ → ℝ≥0 := fun j => ‖LinearMap.toContinuousLinearMap (b.coord j)‖₊
    refine ⟨2 ^ (Finset.univ : Finset (Fin (Module.finrank ℝ (V F κ × V F κ)))).card * ∑ j, (K j : ℝ≥0∞) ^ 2 * C j,
      ENNReal.mul_ne_top (by simp) (ENNReal.sum_ne_top.2 fun j _ => ENNReal.mul_ne_top (by simp) (hC j)), fun l hl c hc => ?_⟩
    obtain rfl | ⟨l', w, rfl⟩ := List.eq_nil_or_concat l
    · simp at hl
    have e : word ψ (l'.concat w) Φ = ∑ j, (b.repr w j : ℂ) • word ψ l' (dR ψ (b j) Φ) := by
      have e1 : word ψ (l'.concat w) Φ = wordL hψ l' ⟨dR ψ w Φ, dR_mem hψ w hΦ⟩ := by
        simp [word, wordL]
      have e2 : (⟨dR ψ w Φ, dR_mem hψ w hΦ⟩ : schA F κ) = ∑ j, (b.repr w j : ℂ) • ⟨dR ψ (b j) Φ, dR_mem hψ _ hΦ⟩ := by
        apply Subtype.ext
        have := dR_sum hψ (b.repr w) b hΦ
        rw [b.sum_repr] at this
        simpa using this
      rw [e1, e2, map_sum]
      simp only [map_smul]
      rfl
    rw [e, mul_assoc, Finset.sum_mul]
    refine (nsq_sum_le μ _ _ fun j => (continuous_of_mem (word_mem hψ l' (dR_mem hψ _ hΦ))).const_smul _).trans
      (mul_le_mul' le_rfl (Finset.sum_le_sum fun j _ => ?_))
    have h1 := hC' j l' (by simpa using hl) c fun u hu => hc u (by simp [hu])
    have h2 : ‖(b.repr w j : ℂ)‖ₑ ≤ K j * c := by
      rw [enorm_eq_nnnorm, ← ENNReal.coe_mul, ENNReal.coe_le_coe, ← NNReal.coe_le_coe, coe_nnnorm, Complex.norm_real]
      exact ((LinearMap.toContinuousLinearMap (b.coord j)).le_opNorm w).trans
        (mul_le_mul_of_nonneg_left (hc w (by simp)) (norm_nonneg _))
    rw [nsq_smul]
    refine (mul_le_mul' (pow_le_pow_left' h2 2) h1).trans (le_of_eq ?_)
    ring

theorem Impl.word (hψ : IsStd ψ) {μ : @Measure (κ → AF F) (borel _)} (hμ : IsHaar μ) {T : Module.End ℂ ((κ → AF F) → ℂ)}
    {s : Pt F κ →ₗ[AF F] Pt F κ} (hT : Impl ψ T s) {d : ℕ} {c : ℝ} (hc : 0 ≤ c) (hs : Bd s d c) {Φ : (κ → AF F) → ℂ}
    (hΦ : Φ ∈ schA F κ) (R : ℝ) (l : List (V F κ × V F κ)) (hl : ∀ w ∈ l, ‖w‖ ≤ R) :
    ∃ l' : List (V F κ × V F κ), l'.length = l.length ∧ (∀ w ∈ l', ‖w‖ ≤ c * R) ∧ T (word ψ l' Φ) = word ψ l (T Φ) := by
  induction l with
  | nil => exact ⟨[], rfl, by simp, rfl⟩
  | cons w l ih =>
    obtain ⟨l', h1, h2, h3⟩ := ih fun u hu => hl u (List.mem_cons_of_mem _ hu)
    obtain ⟨w', h4, h5⟩ := hs.inf w
    refine ⟨w' :: l', by simp [h1], fun u hu => ?_, ?_⟩
    · rcases List.mem_cons.1 hu with rfl | hu
      · exact h5.trans (mul_le_mul_of_nonneg_left (hl w List.mem_cons_self) hc)
      · exact h2 u hu
    · exact (hT.dR hψ hμ h4 (word_mem hψ l' hΦ)).trans (congrArg (Grow.dR ψ w) h3)

end PositivityTheory.ThKF0.Grow
