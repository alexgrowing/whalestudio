import Mathlib
import Formalism.HermitianCurvature.LatticeHerglotzBound

open Filter Topology Finset

noncomputable section

open Classical

namespace Formalism.FourierDecayAlt.P.BoxAverageLimits

open Formalism.FourierDecayAlt.crystallineComparison

section Abstract

variable {Λ : Type} [AddCommGroup Λ] {ι : Type} [Fintype ι] [DecidableEq ι]

def box (ι : Type) [Fintype ι] [DecidableEq ι] (R : ℕ) : Finset (ι → ℕ) :=
  Fintype.piFinset (fun _ => range R)

def bpt (e : ι → Λ) (c : Λ) (m : ι → ℕ) : Λ := c + ∑ i, m i • e i

def avg (e : ι → Λ) (c : ℕ → Λ) (g : Λ → ℂ) (n : ℕ) : ℂ :=
  ((1 / ((n + 1 : ℝ) ^ Fintype.card ι) : ℝ) : ℂ) * ∑ m ∈ box ι (n + 1), g (bpt e (c n) m)

lemma card_box (R : ℕ) : (box ι R).card = R ^ Fintype.card ι := by
  simp [box, Fintype.card_piFinset, Finset.prod_const, Finset.card_univ]

lemma avg_norm_le (e : ι → Λ) (c : ℕ → Λ) (g : Λ → ℂ) (B : ℝ) (hB : ∀ x, ‖g x‖ ≤ B) (n : ℕ) :
    ‖avg e c g n‖ ≤ B := by
  have hpos : (0 : ℝ) < (n + 1 : ℝ) ^ Fintype.card ι := by positivity
  unfold avg
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  have h1 : ‖∑ m ∈ box ι (n + 1), g (bpt e (c n) m)‖ ≤ (box ι (n + 1)).card * B := by
    calc ‖∑ m ∈ box ι (n + 1), g (bpt e (c n) m)‖ ≤ ∑ m ∈ box ι (n + 1), ‖g (bpt e (c n) m)‖ :=
          norm_sum_le _ _
      _ ≤ ∑ _m ∈ box ι (n + 1), B := Finset.sum_le_sum (fun m _ => hB _)
      _ = (box ι (n + 1)).card * B := by rw [Finset.sum_const, nsmul_eq_mul]
  rw [card_box] at h1
  push_cast at h1
  rw [one_div, inv_mul_le_iff₀ hpos]
  linarith

lemma tendsto_lim_of_bdd (u : ℕ → ℂ) (B : ℝ) (hu : ∀ n, ‖u n‖ ≤ B) :
    Tendsto u (hyperfilter ℕ : Filter ℕ) (𝓝 (limUnder (hyperfilter ℕ : Filter ℕ) u)) := by
  have hc : IsCompact (Metric.closedBall (0 : ℂ) B) := isCompact_closedBall 0 B
  obtain ⟨x, -, hx⟩ := hc.ultrafilter_le_nhds ((hyperfilter ℕ).map u) (by
    rw [Ultrafilter.coe_map, le_principal_iff, Filter.mem_map]
    exact Filter.univ_mem' (fun n => by simpa using hu n))
  exact tendsto_nhds_limUnder ⟨x, hx⟩

lemma hyper_le_atTop : (hyperfilter ℕ : Filter ℕ) ≤ atTop := by
  rw [← Nat.cofinite_eq_atTop]; exact hyperfilter_le_cofinite

def LIMf (e : ι → Λ) (c : ℕ → Λ) (g : Λ → ℂ) : ℂ :=
  limUnder (hyperfilter ℕ : Filter ℕ) (avg e c g)

lemma LIMf_eq_of_tendsto (e : ι → Λ) (c : ℕ → Λ) (g : Λ → ℂ) (a : ℂ)
    (h : Tendsto (avg e c g) (hyperfilter ℕ : Filter ℕ) (𝓝 a)) : LIMf e c g = a :=
  h.limUnder_eq

lemma tendsto_LIMf (e : ι → Λ) (c : ℕ → Λ) (g : Λ → ℂ) (hg : Bdd g) :
    Tendsto (avg e c g) (hyperfilter ℕ : Filter ℕ) (𝓝 (LIMf e c g)) := by
  obtain ⟨B, hB⟩ := hg
  exact tendsto_lim_of_bdd _ B (avg_norm_le e c g B hB)

lemma avg_add (e : ι → Λ) (c : ℕ → Λ) (g h : Λ → ℂ) :
    avg e c (g + h) = avg e c g + avg e c h := by
  funext n; simp [avg, Finset.sum_add_distrib, mul_add]

lemma avg_smul (e : ι → Λ) (c : ℕ → Λ) (a : ℂ) (g : Λ → ℂ) :
    avg e c (a • g) = fun n => a * avg e c g n := by
  funext n; simp only [avg, Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum]; ring

lemma avg_one (e : ι → Λ) (c : ℕ → Λ) (n : ℕ) : avg e c (fun _ => 1) n = 1 := by
  unfold avg
  rw [Finset.sum_const, card_box, nsmul_eq_mul, mul_one]
  have hpos : (0 : ℝ) < (n + 1 : ℝ) ^ Fintype.card ι := by positivity
  push_cast
  field_simp

lemma avg_real_nonneg (e : ι → Λ) (c : ℕ → Λ) (g : Λ → ℂ)
    (hg : ∀ x, 0 ≤ (g x).re ∧ (g x).im = 0) (n : ℕ) :
    0 ≤ (avg e c g n).re ∧ (avg e c g n).im = 0 := by
  unfold avg
  rw [Complex.re_ofReal_mul, Complex.im_ofReal_mul, Complex.re_sum, Complex.im_sum]
  constructor
  · exact mul_nonneg (by positivity) (Finset.sum_nonneg (fun m _ => (hg _).1))
  · simp [(hg _).2]

lemma bpt_add_single (e : ι → Λ) (c : Λ) (m : ι → ℕ) (j : ι) :
    bpt e c m + e j = bpt e c (m + Pi.single j 1) := by
  unfold bpt
  simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
  rw [add_assoc]
  congr 2
  rw [Finset.sum_eq_single j]
  · simp
  · intro b _ hb; simp [hb]
  · intro h; exact absurd (Finset.mem_univ j) h

lemma card_slab (R : ℕ) (j : ι) (a : ℕ) :
    (Fintype.piFinset (Function.update (fun _ : ι => range R) j {a})).card =
      R ^ (Fintype.card ι - 1) := by
  rw [Fintype.card_piFinset]
  have : ∀ i, (Function.update (fun _ : ι => range R) j {a} i).card = if i = j then 1 else R := by
    intro i; by_cases h : i = j
    · subst h; simp
    · simp [h]
  simp_rw [this]
  rw [Finset.prod_ite, Finset.prod_const_one, one_mul, Finset.prod_const]
  congr 1
  rw [Finset.filter_ne' Finset.univ j, Finset.card_erase_of_mem (Finset.mem_univ j), Finset.card_univ]

lemma sdiff1 (R : ℕ) (j : ι) :
    box ι R \ (box ι R).image (fun m => m + Pi.single j 1) ⊆
      Fintype.piFinset (Function.update (fun _ : ι => range R) j {0}) := by
  intro m hm
  rw [Finset.mem_sdiff] at hm
  obtain ⟨hbox, hnot⟩ := hm
  have hb := Fintype.mem_piFinset.mp hbox
  rw [Fintype.mem_piFinset]
  intro i
  by_cases hij : i = j
  · subst hij
    simp only [Function.update_self, Finset.mem_singleton]
    by_contra h0
    apply hnot
    rw [Finset.mem_image]
    refine ⟨m - Pi.single i 1, ?_, ?_⟩
    · rw [box, Fintype.mem_piFinset]
      intro k
      have := hb k
      simp only [Finset.mem_range] at this ⊢
      simp only [Pi.sub_apply]
      omega
    · funext k
      simp only [Pi.add_apply, Pi.sub_apply]
      by_cases hk : k = i
      · subst hk; simp; omega
      · simp [hk]
  · simp only [Function.update_apply, hij, if_false]
    exact hb i

lemma sdiff2 (R : ℕ) (j : ι) :
    (box ι R).image (fun m => m + Pi.single j 1) \ box ι R ⊆
      Fintype.piFinset (Function.update (fun _ : ι => range R) j {R}) := by
  intro m hm
  rw [Finset.mem_sdiff, Finset.mem_image] at hm
  obtain ⟨⟨m', hm', rfl⟩, hnot⟩ := hm
  have hb := Fintype.mem_piFinset.mp hm'
  rw [Fintype.mem_piFinset]
  intro i
  by_cases hij : i = j
  · subst hij
    simp only [Function.update_self, Finset.mem_singleton, Pi.add_apply, Pi.single_eq_same]
    have h1 := hb i
    simp only [Finset.mem_range] at h1
    by_contra hne
    apply hnot
    rw [box, Fintype.mem_piFinset]
    intro k
    simp only [Finset.mem_range, Pi.add_apply]
    by_cases hk : k = i
    · subst hk; simp; omega
    · have := hb k; simp only [Finset.mem_range] at this; simp [hk, this]
  · simp only [Function.update_apply, hij, if_false, Pi.add_apply]
    simp [hij]
    simpa using hb i

lemma shift_sum_bound (R : ℕ) (j : ι) (G : (ι → ℕ) → ℂ) (B : ℝ) (hB : ∀ m, ‖G m‖ ≤ B) :
    ‖∑ m ∈ box ι R, G (m + Pi.single j 1) - ∑ m ∈ box ι R, G m‖ ≤
      2 * B * R ^ (Fintype.card ι - 1) := by
  have hinj : Set.InjOn (fun m : ι → ℕ => m + Pi.single j 1) (box ι R) :=
    fun a _ b _ h => add_right_cancel h
  rw [← Finset.sum_image (f := G) (g := fun m => m + Pi.single j 1) hinj]
  rw [← Finset.sum_sdiff_sub_sum_sdiff]
  have hB0 : 0 ≤ B := le_trans (norm_nonneg _) (hB 0)
  have e1 : ‖∑ x ∈ (box ι R).image (fun m => m + Pi.single j 1) \ box ι R, G x‖ ≤
      B * R ^ (Fintype.card ι - 1) := by
    calc _ ≤ ∑ x ∈ (box ι R).image (fun m => m + Pi.single j 1) \ box ι R, ‖G x‖ := norm_sum_le _ _
      _ ≤ ∑ _x ∈ (box ι R).image (fun m => m + Pi.single j 1) \ box ι R, B :=
          Finset.sum_le_sum (fun x _ => hB x)
      _ = _ * B := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (R ^ (Fintype.card ι - 1) : ℕ) * B := by
          gcongr
          rw [← card_slab R j R]
          exact Finset.card_le_card (sdiff2 R j)
      _ = _ := by push_cast; ring
  have e2 : ‖∑ x ∈ box ι R \ (box ι R).image (fun m => m + Pi.single j 1), G x‖ ≤
      B * R ^ (Fintype.card ι - 1) := by
    calc _ ≤ ∑ x ∈ box ι R \ (box ι R).image (fun m => m + Pi.single j 1), ‖G x‖ := norm_sum_le _ _
      _ ≤ ∑ _x ∈ box ι R \ (box ι R).image (fun m => m + Pi.single j 1), B :=
          Finset.sum_le_sum (fun x _ => hB x)
      _ = _ * B := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (R ^ (Fintype.card ι - 1) : ℕ) * B := by
          gcongr
          rw [← card_slab R j 0]
          exact Finset.card_le_card (sdiff1 R j)
      _ = _ := by push_cast; ring
  calc _ ≤ ‖∑ x ∈ (box ι R).image (fun m => m + Pi.single j 1) \ box ι R, G x‖ +
        ‖∑ x ∈ box ι R \ (box ι R).image (fun m => m + Pi.single j 1), G x‖ := norm_sub_le _ _
    _ ≤ _ := by linarith

lemma avg_shift_small (e : ι → Λ) (c : ℕ → Λ) (g : Λ → ℂ) (B : ℝ) (hB : ∀ x, ‖g x‖ ≤ B) (j : ι) (n : ℕ) :
    ‖avg e c (fun x => g (x + e j)) n - avg e c g n‖ ≤ 2 * B / (n + 1) := by
  have hd : 1 ≤ Fintype.card ι := Fintype.card_pos_iff.mpr ⟨j⟩
  unfold avg
  rw [← mul_sub, norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  have hs : ∑ m ∈ box ι (n + 1), g (bpt e (c n) m + e j) =
      ∑ m ∈ box ι (n + 1), (fun m => g (bpt e (c n) m)) (m + Pi.single j 1) := by
    refine Finset.sum_congr rfl (fun m _ => ?_); rw [bpt_add_single]
  rw [hs]
  have h := shift_sum_bound (n + 1) j (fun m => g (bpt e (c n) m)) B (fun m => hB _)
  have hpos : (0 : ℝ) < (n + 1 : ℝ) := by positivity
  have hpow : ((n + 1 : ℕ) : ℝ) ^ Fintype.card ι = (n + 1 : ℝ) * (n + 1 : ℝ) ^ (Fintype.card ι - 1) := by
    push_cast
    rw [← pow_succ']; congr 1; omega
  calc (1 / ((n + 1 : ℝ) ^ Fintype.card ι)) * ‖_‖
      ≤ (1 / ((n + 1 : ℝ) ^ Fintype.card ι)) * (2 * B * ((n + 1 : ℕ) : ℝ) ^ (Fintype.card ι - 1)) := by
        gcongr
    _ = 2 * B / (n + 1) := by
        have : ((n + 1 : ℕ) : ℝ) ^ Fintype.card ι = (n + 1 : ℝ) ^ Fintype.card ι := by push_cast; rfl
        rw [← this, hpow]
        push_cast
        field_simp

lemma LIMf_shift_gen (e : ι → Λ) (c : ℕ → Λ) (g : Λ → ℂ) (hg : Bdd g) (j : ι) :
    LIMf e c (fun x => g (x + e j)) = LIMf e c g := by
  obtain ⟨B, hB⟩ := hg
  have hg' : Bdd g := ⟨B, hB⟩
  apply LIMf_eq_of_tendsto
  have h0 : Tendsto (fun n => avg e c (fun x => g (x + e j)) n - avg e c g n)
      (hyperfilter ℕ : Filter ℕ) (𝓝 0) := by
    apply Tendsto.mono_left _ hyper_le_atTop
    apply squeeze_zero_norm (avg_shift_small e c g B hB j)
    have := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (2 * B)
    rw [mul_zero] at this
    refine this.congr (fun n => ?_)
    rw [mul_one_div]
  have := h0.add (tendsto_LIMf e c g hg')
  simpa using this

lemma bdd_shift {g : Λ → ℂ} (hg : Bdd g) (σ : Λ) : Bdd (fun x => g (x + σ)) := by
  obtain ⟨B, hB⟩ := hg; exact ⟨B, fun x => hB _⟩

def InvAt (e : ι → Λ) (c : ℕ → Λ) (σ : Λ) : Prop :=
  ∀ g, Bdd g → LIMf e c (fun x => g (x + σ)) = LIMf e c g

lemma invAt_add (e : ι → Λ) (c : ℕ → Λ) (a b : Λ) (ha : InvAt e c a) (hb : InvAt e c b) :
    InvAt e c (a + b) := by
  intro g hg
  have hfun : (fun x => g (x + (a + b))) = (fun x => (fun y => g (y + a)) (x + b)) := by
    funext x
    show g (x + (a + b)) = g (x + b + a)
    rw [add_comm a b, add_assoc]
  rw [hfun, hb _ (bdd_shift hg a), ha g hg]

lemma invAt_neg (e : ι → Λ) (c : ℕ → Λ) (a : Λ) (ha : InvAt e c a) : InvAt e c (-a) := by
  intro g hg
  calc LIMf e c (fun x => g (x + -a))
      = LIMf e c (fun x => (fun y => g (y + -a)) (x + a)) := (ha _ (bdd_shift hg (-a))).symm
    _ = LIMf e c g := by
        have hfun : (fun x => (fun y => g (y + -a)) (x + a)) = g := by
          funext x; show g (x + a + -a) = g x; rw [add_neg_cancel_right]
        rw [hfun]

lemma invAt_zero (e : ι → Λ) (c : ℕ → Λ) : InvAt e c 0 := by
  intro g _; simp

lemma invAt_all (e : ι → Λ) (c : ℕ → Λ) (he : AddSubgroup.closure (Set.range e) = ⊤) (σ : Λ) :
    InvAt e c σ := by
  have hσ : σ ∈ AddSubgroup.closure (Set.range e) := by rw [he]; exact AddSubgroup.mem_top σ
  induction hσ using AddSubgroup.closure_induction with
  | mem x hx =>
    obtain ⟨j, rfl⟩ := hx
    intro g hg; exact LIMf_shift_gen e c g hg j
  | zero => exact invAt_zero e c
  | add x y _ _ hx hy => exact invAt_add e c x y hx hy
  | neg x _ hx => exact invAt_neg e c x hx

theorem exists_mean (e : ι → Λ) (he : AddSubgroup.closure (Set.range e) = ⊤) (c : ℕ → Λ) :
    IsMean (LIMf e c) ∧ ∀ g, Bdd g →
      (∀ ε > 0, ∀ᶠ n in atTop, ∀ m ∈ box ι (n + 1), ‖g (bpt e (c n) m)‖ ≤ ε) → LIMf e c g = 0 := by
  refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · intro g h hg hh
    apply LIMf_eq_of_tendsto
    rw [avg_add]
    exact (tendsto_LIMf e c g hg).add (tendsto_LIMf e c h hh)
  · intro a g hg
    apply LIMf_eq_of_tendsto
    rw [avg_smul]
    exact (tendsto_LIMf e c g hg).const_mul a
  · intro g hg hpos
    have hcl : IsClosed {z : ℂ | 0 ≤ z.re ∧ z.im = 0} :=
      (isClosed_le continuous_const Complex.continuous_re).inter
        (isClosed_eq Complex.continuous_im continuous_const)
    exact hcl.mem_of_tendsto (tendsto_LIMf e c g hg)
      (Filter.Eventually.of_forall (fun n => avg_real_nonneg e c g hpos n))
  · apply LIMf_eq_of_tendsto
    have : avg e c (fun _ => (1 : ℂ)) = fun _ => 1 := funext (avg_one e c)
    rw [this]; exact tendsto_const_nhds
  · intro g σ hg
    exact invAt_all e c he σ g hg
  · intro g hg hsmall
    apply LIMf_eq_of_tendsto
    apply Tendsto.mono_left _ hyper_le_atTop
    rw [Metric.tendsto_nhds]
    intro ε hε
    filter_upwards [hsmall (ε / 2) (by positivity)] with n hn
    rw [dist_zero_right]
    have hpos : (0 : ℝ) < (n + 1 : ℝ) ^ Fintype.card ι := by positivity
    unfold avg
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
    have h1 : ‖∑ m ∈ box ι (n + 1), g (bpt e (c n) m)‖ ≤ (box ι (n + 1)).card * (ε / 2) := by
      calc _ ≤ ∑ m ∈ box ι (n + 1), ‖g (bpt e (c n) m)‖ := norm_sum_le _ _
        _ ≤ ∑ _m ∈ box ι (n + 1), (ε / 2) := Finset.sum_le_sum (fun m hm => hn m hm)
        _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]
    rw [card_box] at h1
    push_cast at h1
    rw [one_div, inv_mul_lt_iff₀ hpos]
    nlinarith

end Abstract

section Lattice

lemma exists_far {f : ℕ} (La : Submodule ℤ (V f)) [DiscreteTopology La] [IsZLattice ℝ La] (T : ℝ) :
    ∃ y ∈ La, ∀ v, T ≤ ‖y v‖ := by
  let b := Module.Free.chooseBasis ℤ La
  let bR := b.ofZLatticeBasis ℝ La
  set γ : ℝ := ∑ i, ‖bR i‖ with hγ
  have hγ0 : 0 ≤ γ := Finset.sum_nonneg (fun i _ => norm_nonneg _)
  let w : V f := fun _ => ((|T| + γ : ℝ) : ℂ)
  refine ⟨(ZSpan.floor bR w : V f), ?_, ?_⟩
  · have h := (ZSpan.floor bR w).2
    have hs : Submodule.span ℤ (Set.range bR) = La := Module.Basis.ofZLatticeBasis_span ℝ La b
    exact hs.le h
  · intro v
    have h1 := ZSpan.norm_fract_le bR w
    rw [ZSpan.fract_apply] at h1
    have h2 : ‖(w - (ZSpan.floor bR w : V f)) v‖ ≤ ‖w - (ZSpan.floor bR w : V f)‖ :=
      norm_le_pi_norm (w - (ZSpan.floor bR w : V f)) v
    have h3 : ‖w v‖ = |T| + γ := by
      simp only [w, Complex.norm_real]
      exact Real.norm_of_nonneg (by positivity)
    have h4 := norm_sub_norm_le (w v) ((ZSpan.floor bR w : V f) v)
    rw [Pi.sub_apply] at h2
    have h5 : T ≤ |T| := le_abs_self T
    linarith

lemma le_atInfAll (f : ℕ) :
    (⨅ T : ℝ, 𝓟 {x : V f | ∀ v, T ≤ ‖x v‖}) ≤ atInfAll f := by
  unfold atInfAll
  refine le_iInf (fun v => ?_)
  rw [← Filter.tendsto_iff_comap]
  rw [Filter.tendsto_atTop]
  intro T
  exact Filter.mem_iInf_of_mem T (Filter.mem_principal.mpr (fun x hx => hx v))

lemma exists_T_of_mem {f : ℕ} {t : Set (V f)} (ht : t ∈ atInfAll f) :
    ∃ T : ℝ, {x : V f | ∀ v, T ≤ ‖x v‖} ⊆ t := by
  have hdir : Directed (fun x1 x2 => x1 ⊇ x2) (fun T : ℝ => {x : V f | ∀ v, T ≤ ‖x v‖}) := by
    intro T1 T2
    refine ⟨max T1 T2, fun x hx v => le_trans (le_max_left _ _) (hx v),
      fun x hx v => le_trans (le_max_right _ _) (hx v)⟩
  have hb := Filter.hasBasis_iInf_principal hdir
  obtain ⟨T, -, hT⟩ := hb.mem_iff.mp (le_atInfAll f ht)
  exact ⟨T, hT⟩

theorem meanExists : MeanExists := by
  intro f La _ _
  let b := Module.Free.chooseBasis ℤ La
  let Λ := La.toAddSubgroup
  let e : Module.Free.ChooseBasisIndex ℤ La → Λ := fun i => ⟨(b i : V f), (b i).2⟩
  set β : ℝ := ∑ i, ‖(b i : V f)‖ with hβ
  have hβ0 : 0 ≤ β := Finset.sum_nonneg (fun i _ => norm_nonneg _)
  have hfar := fun n : ℕ => exists_far La ((n : ℝ) + (n + 1) * β)
  choose y hyLa hy using hfar
  let c : ℕ → Λ := fun n => ⟨y n, hyLa n⟩
  have he : AddSubgroup.closure (Set.range e) = ⊤ := by
    rw [eq_top_iff]
    intro z _
    suffices hall : ∀ zL : La, (⟨zL.1, zL.2⟩ : Λ) ∈ AddSubgroup.closure (Set.range e) from
      hall ⟨z.1, z.2⟩
    intro zL
    have hxs : zL ∈ Submodule.span ℤ (Set.range b) := by
      rw [b.span_eq]; exact Submodule.mem_top
    induction hxs using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨i, rfl⟩ := hz
      exact AddSubgroup.subset_closure ⟨i, rfl⟩
    | zero => exact (AddSubgroup.closure (Set.range e)).zero_mem
    | add z1 z2 _ _ h1 h2 =>
      have := (AddSubgroup.closure (Set.range e)).add_mem h1 h2
      convert this using 1
      apply Subtype.ext
      simp
    | smul a z _ h =>
      have := (AddSubgroup.closure (Set.range e)).zsmul_mem h a
      convert this using 1
      apply Subtype.ext
      simp
  obtain ⟨hmean, hvan⟩ := exists_mean e he c
  refine ⟨LIMf e c, hmean, ?_⟩
  intro g hg htend
  apply hvan g hg
  intro ε hε
  have h1 : g ⁻¹' Metric.closedBall 0 ε ∈ Filter.comap (fun x : Λ => (x : V f)) (atInfAll f) :=
    htend (Metric.closedBall_mem_nhds 0 hε)
  obtain ⟨t, ht, hts⟩ := Filter.mem_comap.mp h1
  obtain ⟨T, hT⟩ := exists_T_of_mem ht
  filter_upwards [Filter.eventually_ge_atTop ⌈T⌉₊] with n hn m hm
  have hmem : (bpt e (c n) m : Λ) ∈ (fun x : Λ => (x : V f)) ⁻¹' t := by
    apply hT
    intro v
    show T ≤ ‖((bpt e (c n) m : Λ) : V f) v‖
    have hcoe : ((bpt e (c n) m : Λ) : V f) = y n + ∑ i, m i • (b i : V f) := by
      simp [bpt, c, e]
    rw [hcoe, Pi.add_apply]
    have hs : ‖(∑ i, m i • (b i : V f)) v‖ ≤ (n + 1) * β := by
      calc ‖(∑ i, m i • (b i : V f)) v‖ ≤ ‖∑ i, m i • (b i : V f)‖ := norm_le_pi_norm _ v
        _ ≤ ∑ i, ‖m i • (b i : V f)‖ := norm_sum_le _ _
        _ ≤ ∑ i, (m i : ℝ) * ‖(b i : V f)‖ := Finset.sum_le_sum (fun i _ => norm_nsmul_le)
        _ ≤ ∑ i, ((n : ℝ) + 1) * ‖(b i : V f)‖ := by
            apply Finset.sum_le_sum
            intro i _
            have := Fintype.mem_piFinset.mp hm i
            simp only [Finset.mem_range] at this
            have : (m i : ℝ) ≤ n + 1 := by exact_mod_cast this.le
            gcongr
        _ = (n + 1) * β := by rw [hβ, Finset.mul_sum]
    have hyv := hy n v
    have htri := norm_sub_le (y n v + (∑ i, m i • (b i : V f)) v) ((∑ i, m i • (b i : V f)) v)
    rw [add_sub_cancel_right] at htri
    have hnT : T ≤ (n : ℝ) := le_trans (Nat.le_ceil T) (by exact_mod_cast hn)
    linarith
  have := hts hmem
  simpa using this

end Lattice

theorem _root_.Formalism.FourierDecayAlt.P.invariantMeanExists : Formalism.FourierDecayAlt.crystallineComparison.MeanExists := meanExists

end Formalism.FourierDecayAlt.P.BoxAverageLimits
