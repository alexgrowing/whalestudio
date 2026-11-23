import Mathlib
import ReciprocityTheory.DualLattices.VEqZeroOfPowEqOne
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.PtSolveMapFixedIff

namespace ReciprocityTheory.ChartRestriction.G.Sh

open MvPowerSeries ReciprocityTheory.PGsh

open Classical

noncomputable section

variable {C : Type} [Field C] {v : AddValuation C (WithTop ℝ)} {d : ℕ}

def ptAdd (G : LogFGL v d) {τ : Type*} (x y : Fin d → MvPowerSeries τ C) :
    Fin d → MvPowerSeries τ C :=
  fun a => subst (Sum.elim x y) (G.F a)

def ptSumL (G : LogFGL v d) {τ : Type*} :
    List (Fin d → MvPowerSeries τ C) → (Fin d → MvPowerSeries τ C)
  | [] => 0
  | x :: l => ptAdd G x (ptSumL G l)

theorem ptc_elim_const {τ : Type*} {x y : Fin d → MvPowerSeries τ C}
    (hx : ∀ a, constantCoeff (x a) = 0) (hy : ∀ a, constantCoeff (y a) = 0) :
    ∀ s, constantCoeff (Sum.elim x y s) = 0 := by
  intro s
  cases s with
  | inl s => exact hx s
  | inr s => exact hy s

private theorem hs_lemma {σ τ : Type*} [Finite σ] {a : σ → MvPowerSeries τ C}
    (ha : ∀ s, constantCoeff (a s) = 0) : HasSubst a :=
  MvPowerSeries.hasSubst_of_constantCoeff_zero ha

private theorem pc_lemma_9 {σ τ : Type*} {a : σ → MvPowerSeries τ C}
    (ha : ∀ s, constantCoeff (a s) = 0) {m : σ →₀ ℕ} (hm : m ≠ 0) :
    constantCoeff (m.prod fun s n => a s ^ n) = 0 := by
  obtain ⟨s, hs⟩ : ∃ s, m s ≠ 0 := by
    by_contra hc
    push_neg at hc
    exact hm (Finsupp.ext hc)
  unfold Finsupp.prod
  rw [map_prod]
  exact Finset.prod_eq_zero (Finsupp.mem_support_iff.mpr hs) (by simp [ha s, hs])

private theorem cc_lemma_2 {σ τ : Type*} [Finite σ] {a : σ → MvPowerSeries τ C}
    (ha : ∀ s, constantCoeff (a s) = 0) (f : MvPowerSeries σ C) (hf : constantCoeff f = 0) :
    constantCoeff (subst a f) = 0 := by
  rw [constantCoeff_subst (hs_lemma ha)]
  apply finsum_eq_zero_of_forall_eq_zero
  intro m
  by_cases hm : m = 0
  · rw [hm]
    simp [hf, MvPowerSeries.coeff_zero_eq_constantCoeff_apply]
  · rw [pc_lemma_9 ha hm, smul_zero]

private theorem fs_lemma_4 {α : Type*} (g : α → C) (hg : ∀ i, g i ∈ ptIntSub v) :
    ∑ᶠ i, g i ∈ ptIntSub v := by
  by_cases hfin : (Function.support g).Finite
  · rw [finsum_eq_sum g hfin]
    exact Subring.sum_mem _ fun i _ => hg i
  · rw [finsum_of_infinite_support hfin]
    exact Subring.zero_mem _

private theorem int_lemma_3 {σ τ : Type*} [Finite σ] {a : σ → MvPowerSeries τ C}
    (ha : ∀ s, constantCoeff (a s) = 0) (hai : ∀ s, a s ∈ ptIntSer v τ)
    (f : MvPowerSeries σ C) (hf : MvIsInt v f) : subst a f ∈ ptIntSer v τ := by
  show ∀ e, coeff e (subst a f) ∈ ptIntSub v
  intro e
  rw [coeff_subst (hs_lemma ha)]
  apply fs_lemma_4
  intro m
  have hp : (m.prod fun s n => a s ^ n) ∈ ptIntSer v τ := by
    unfold Finsupp.prod
    exact Subring.prod_mem _ fun s _ => Subring.pow_mem _ (hai s) _
  have hp' : ∀ α, coeff α (m.prod fun s n => a s ^ n) ∈ ptIntSub v := hp
  have hfm : coeff m f ∈ ptIntSub v := hf m
  rw [smul_eq_mul]
  exact Subring.mul_mem _ hfm (hp' e)

theorem ptAdd_good (G : LogFGL v d) {τ : Type*} {x y : Fin d → MvPowerSeries τ C}
    (hx : PTGood v x) (hy : PTGood v y) : PTGood v (ptAdd G x y) := by
  have hx0 : ∀ a, constantCoeff (x a) = 0 := fun a => (hx a).1
  have hy0 : ∀ a, constantCoeff (y a) = 0 := fun a => (hy a).1
  intro a
  refine ⟨cc_lemma_2 (ptc_elim_const hx0 hy0) (G.F a) (G.F_const a), ?_⟩
  refine int_lemma_3 (ptc_elim_const hx0 hy0) ?_ (G.F a) (G.F_int a)
  intro s
  cases s with
  | inl s => exact (hx s).2
  | inr s => exact (hy s).2

theorem ptAdd_const (G : LogFGL v d) {τ : Type*} {x y : Fin d → MvPowerSeries τ C}
    (hx : ∀ a, constantCoeff (x a) = 0) (hy : ∀ a, constantCoeff (y a) = 0) (a : Fin d) :
    constantCoeff (ptAdd G x y a) = 0 := by
  exact cc_lemma_2 (ptc_elim_const hx hy) (G.F a) (G.F_const a)

theorem ptAdd_lg (G : LogFGL v d) {τ : Type*} {x y : Fin d → MvPowerSeries τ C}
    (hx : ∀ a, constantCoeff (x a) = 0) (hy : ∀ a, constantCoeff (y a) = 0) (a : Fin d) :
    subst (ptAdd G x y) (G.lg a) = subst x (G.lg a) + subst y (G.lg a) := by
  have hxy := hs_lemma (ptc_elim_const hx hy)
  have hF := hs_lemma G.F_const
  have hl : HasSubst (fun b : Fin d => (X (Sum.inl b) : MvPowerSeries (Fin d ⊕ Fin d) C)) :=
    hs_lemma fun b => by simp
  have hr : HasSubst (fun b : Fin d => (X (Sum.inr b) : MvPowerSeries (Fin d ⊕ Fin d) C)) :=
    hs_lemma fun b => by simp
  rw [show ptAdd G x y = fun s => subst (Sum.elim x y) (G.F s) from rfl,
    ← subst_comp_subst_apply hF hxy, G.lg_F a, subst_add hxy,
    subst_comp_subst_apply hl hxy, subst_comp_subst_apply hr hxy]
  simp only [subst_X hxy, Sum.elim_inl, Sum.elim_inr]

private theorem sp_lemma_13 {σ τ : Type*} {a : σ → MvPowerSeries τ C} {m : σ →₀ ℕ} {s : σ}
    (hle : Finsupp.single s 1 ≤ m) :
    (m.prod fun s n => a s ^ n) = a s * ((m - Finsupp.single s 1).prod fun s n => a s ^ n) := by
  conv_lhs => rw [← add_tsub_cancel_of_le hle]
  rw [Finsupp.prod_add_index' (h := fun s n => a s ^ n) (fun _ => pow_zero _)
    (fun _ _ _ => pow_add _ _ _), Finsupp.prod_single_index (h := fun s n => a s ^ n) (pow_zero _),
    pow_one]

private theorem ml_lemma_10 {τ : Type*} {f g : MvPowerSeries τ C} (hf : constantCoeff f = 0)
    (hg : constantCoeff g = 0) (t : τ) : coeff (Finsupp.single t 1) (f * g) = 0 := by
  rw [coeff_mul]
  apply Finset.sum_eq_zero
  intro p hp
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
  have key : ∀ i, p.1 i + p.2 i = if t = i then 1 else 0 := fun i => by
    rw [← Finsupp.add_apply, hp, Finsupp.single_apply]
  by_cases h1 : p.1 t = 0
  · have hp1 : p.1 = 0 := by
      ext i
      have hi := key i
      show p.1 i = 0
      split_ifs at hi with hti
      · subst hti
        omega
      · omega
    rw [hp1, MvPowerSeries.coeff_zero_eq_constantCoeff_apply, hf, zero_mul]
  · have hp2 : p.2 = 0 := by
      ext i
      have hi := key i
      show p.2 i = 0
      split_ifs at hi with hti
      · subst hti
        omega
      · omega
    rw [hp2, MvPowerSeries.coeff_zero_eq_constantCoeff_apply, hg, mul_zero]

theorem ptAdd_lin (G : LogFGL v d) {τ : Type*} {x y : Fin d → MvPowerSeries τ C}
    (hx : ∀ a, constantCoeff (x a) = 0) (hy : ∀ a, constantCoeff (y a) = 0) (a : Fin d)
    (t : τ) :
    coeff (Finsupp.single t 1) (ptAdd G x y a) =
      coeff (Finsupp.single t 1) (x a) + coeff (Finsupp.single t 1) (y a) := by
  have h0 := ptc_elim_const hx hy
  have hs : HasSubst (Sum.elim x y) := hasSubst_of_constantCoeff_zero h0
  show coeff (Finsupp.single t 1) (subst (Sum.elim x y) (G.F a)) = _
  rw [pt_coeff_single_subst hs h0 (G.F_const a) t, Fintype.sum_sum_type]
  simp only [pt_F_lin, Sum.elim_inl, Sum.elim_inr, Sum.inl.injEq, Sum.inr.injEq, reduceCtorEq,
    if_false, add_zero, zero_add, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq',
    Finset.mem_univ, if_true]

theorem ptSumL_const (G : LogFGL v d) {τ : Type*} :
    ∀ l : List (Fin d → MvPowerSeries τ C), (∀ x ∈ l, ∀ a, constantCoeff (x a) = 0) →
      ∀ a, constantCoeff (ptSumL G l a) = 0
  | [], _, a => by simp [ptSumL]
  | x :: l, h, a => ptAdd_const G (h x (by simp))
      (ptSumL_const G l fun x' hx' => h x' (by simp [hx'])) a

theorem ptSumL_good (G : LogFGL v d) {τ : Type*} :
    ∀ l : List (Fin d → MvPowerSeries τ C), (∀ x ∈ l, PTGood v x) → PTGood v (ptSumL G l)
  | [], _ => ptGood_zero
  | x :: l, h => ptAdd_good G (h x (by simp)) (ptSumL_good G l fun x' hx' => h x' (by simp [hx']))

private theorem zs_lemma_5 {τ : Type*} (f : MvPowerSeries (Fin d) C) (hf : constantCoeff f = 0) :
    subst (0 : Fin d → MvPowerSeries τ C) f = 0 := by
  ext e
  rw [coeff_subst (hs_lemma (fun _ => by simp)), map_zero]
  apply finsum_eq_zero_of_forall_eq_zero
  intro m
  by_cases hm : m = 0
  · rw [hm]
    simp [hf, MvPowerSeries.coeff_zero_eq_constantCoeff_apply]
  · obtain ⟨s, hs⟩ : ∃ s, m s ≠ 0 := by
      by_contra hc
      push_neg at hc
      exact hm (Finsupp.ext hc)
    have h0 : (m.prod fun s n => (0 : Fin d → MvPowerSeries τ C) s ^ n) = 0 :=
      Finset.prod_eq_zero (Finsupp.mem_support_iff.mpr hs) (by simp [hs])
    rw [h0, map_zero, smul_zero]

theorem ptSumL_lg (G : LogFGL v d) {τ : Type*} :
    ∀ l : List (Fin d → MvPowerSeries τ C), (∀ x ∈ l, ∀ a, constantCoeff (x a) = 0) →
      ∀ b, subst (ptSumL G l) (G.lg b) = (l.map fun x => subst x (G.lg b)).sum
  | [], _, b => by
    simp only [ptSumL, List.map_nil, List.sum_nil]
    exact subst_zero_of_constantCoeff_zero (G.lg_const b)
  | x :: l, h, b => by
    have hl : ∀ x' ∈ l, ∀ a, constantCoeff (x' a) = 0 := fun x' hx' => h x' (by simp [hx'])
    rw [ptSumL, ptAdd_lg G (h x (by simp)) (ptSumL_const G l hl), ptSumL_lg G l hl b]
    simp

theorem ptSumL_lin (G : LogFGL v d) {τ : Type*} :
    ∀ l : List (Fin d → MvPowerSeries τ C), (∀ x ∈ l, ∀ a, constantCoeff (x a) = 0) →
      ∀ a t, coeff (Finsupp.single t 1) (ptSumL G l a) =
        (l.map fun x => coeff (Finsupp.single t 1) (x a)).sum
  | [], _, a, t => by simp [ptSumL]
  | x :: l, h, a, t => by
    have hl : ∀ x' ∈ l, ∀ a, constantCoeff (x' a) = 0 := fun x' hx' => h x' (by simp [hx'])
    rw [ptSumL, ptAdd_lin G (h x (by simp)) (ptSumL_const G l hl), ptSumL_lin G l hl a t]
    simp

private theorem mu_lemma_16 {τ : Type*} {f f' g g' : MvPowerSeries τ C} (n : ℕ)
    (hf : ∀ e : τ →₀ ℕ, e.degree < n → coeff e f = coeff e f')
    (hg : ∀ e : τ →₀ ℕ, e.degree < n → coeff e g = coeff e g') :
    ∀ e : τ →₀ ℕ, e.degree < n → coeff e (f * g) = coeff e (f' * g') := by
  intro e he
  rw [coeff_mul, coeff_mul]
  apply Finset.sum_congr rfl
  intro p hp
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
  have hd : p.1.degree + p.2.degree = e.degree := by rw [← hp, map_add]
  rw [hf p.1 (by omega), hg p.2 (by omega)]

private theorem m1_lemma_17 {τ : Type*} {f f' g g' : MvPowerSeries τ C} (n : ℕ)
    (hf0 : constantCoeff f = 0) (hf0' : constantCoeff f' = 0)
    (hg0 : constantCoeff g = 0) (hg0' : constantCoeff g' = 0)
    (hf : ∀ e : τ →₀ ℕ, e.degree < n → coeff e f = coeff e f')
    (hg : ∀ e : τ →₀ ℕ, e.degree < n → coeff e g = coeff e g') :
    ∀ e : τ →₀ ℕ, e.degree ≤ n → coeff e (f * g) = coeff e (f' * g') := by
  intro e he
  rw [coeff_mul, coeff_mul]
  apply Finset.sum_congr rfl
  intro p hp
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
  have hd : p.1.degree + p.2.degree = e.degree := by rw [← hp, map_add]
  by_cases h1 : p.1 = 0
  · rw [h1, MvPowerSeries.coeff_zero_eq_constantCoeff_apply,
      MvPowerSeries.coeff_zero_eq_constantCoeff_apply, hf0, hf0', zero_mul, zero_mul]
  · by_cases h2 : p.2 = 0
    · rw [h2, MvPowerSeries.coeff_zero_eq_constantCoeff_apply,
        MvPowerSeries.coeff_zero_eq_constantCoeff_apply, hg0, hg0', mul_zero, mul_zero]
    · have d1 : p.1.degree ≠ 0 := fun h => h1 ((Finsupp.degree_eq_zero_iff _).mp h)
      have d2 : p.2.degree ≠ 0 := fun h => h2 ((Finsupp.degree_eq_zero_iff _).mp h)
      rw [hf p.1 (by omega), hg p.2 (by omega)]

private theorem tp_lemma_14 {σ τ : Type*} {x y : σ → MvPowerSeries τ C} (n : ℕ)
    (hxy : ∀ s (e : τ →₀ ℕ), e.degree < n → coeff e (x s) = coeff e (y s)) (m : σ →₀ ℕ) :
    ∀ e : τ →₀ ℕ, e.degree < n →
      coeff e (m.prod fun s k => x s ^ k) = coeff e (m.prod fun s k => y s ^ k) := by
  have hpow : ∀ s (k : ℕ), ∀ e : τ →₀ ℕ, e.degree < n → coeff e (x s ^ k) = coeff e (y s ^ k) := by
    intro s k
    induction k with
    | zero =>
      intro e _
      simp
    | succ k ih =>
      rw [pow_succ, pow_succ]
      exact mu_lemma_16 n ih (hxy s)
  unfold Finsupp.prod
  induction m.support using Finset.induction_on with
  | empty =>
    intro e _
    simp
  | @insert j S hj ih =>
    rw [Finset.prod_insert hj, Finset.prod_insert hj]
    exact mu_lemma_16 n (hpow j (m j)) ih

private theorem ag_lemma_15 {σ τ : Type*} [Finite σ] {x y : σ → MvPowerSeries τ C}
    (hx : ∀ s, constantCoeff (x s) = 0) (hy : ∀ s, constantCoeff (y s) = 0) (n : ℕ)
    (hxy : ∀ s (e : τ →₀ ℕ), e.degree < n → coeff e (x s) = coeff e (y s))
    (r : MvPowerSeries σ C) (hr0 : constantCoeff r = 0)
    (hr1 : ∀ s, coeff (Finsupp.single s 1) r = 0) (e : τ →₀ ℕ) (he : e.degree ≤ n) :
    coeff e (subst x r) = coeff e (subst y r) := by
  rw [coeff_subst (hs_lemma hx), coeff_subst (hs_lemma hy)]
  apply finsum_congr
  intro m
  by_cases h0 : m = 0
  · rw [h0, MvPowerSeries.coeff_zero_eq_constantCoeff_apply, hr0, zero_smul, zero_smul]
  · obtain ⟨s, hs⟩ : ∃ s, m s ≠ 0 := by
      by_contra hc
      push_neg at hc
      exact h0 (Finsupp.ext hc)
    have hle : Finsupp.single s 1 ≤ m :=
      Finsupp.single_le_iff.mpr (Nat.one_le_iff_ne_zero.mpr hs)
    by_cases hm' : m - Finsupp.single s 1 = 0
    · have hms : m = Finsupp.single s 1 := by
        rw [← add_tsub_cancel_of_le hle, hm', add_zero]
      rw [hms, hr1 s, zero_smul, zero_smul]
    · rw [sp_lemma_13 hle, sp_lemma_13 hle]
      congr 1
      exact m1_lemma_17 n (hx s) (hy s) (pc_lemma_9 hx hm') (pc_lemma_9 hy hm') (hxy s)
        (tp_lemma_14 n hxy _) e he

theorem pt_agree_of_lg (G : LogFGL v d) {τ : Type*} {x y : Fin d → MvPowerSeries τ C}
    (hx : ∀ a, constantCoeff (x a) = 0) (hy : ∀ a, constantCoeff (y a) = 0) (k : ℕ)
    (h : ∀ a (e : τ →₀ ℕ), e.degree < k →
      coeff e (subst x (G.lg a)) = coeff e (subst y (G.lg a))) : PTAgree k x y := by
  have hsx := hs_lemma hx
  have hsy := hs_lemma hy
  have hr0 : ∀ i, constantCoeff (G.lg i - X i) = 0 := fun i => by simp [G.lg_const i]
  have hr1 : ∀ i s, coeff (Finsupp.single s 1) (G.lg i - X i) = 0 := fun i s => by
    rw [map_sub, G.lg_lin]
    by_cases his : i = s
    · subst his
      simp [coeff_X]
    · have hne : ¬ Finsupp.single s 1 = Finsupp.single i 1 := fun h' =>
        his (Finsupp.single_left_injective one_ne_zero h').symm
      simp [his, coeff_X, hne]
  have key : ∀ n, ∀ i (e : τ →₀ ℕ), e.degree = n → n < k → coeff e (x i) = coeff e (y i) := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro i e hen hnk
      have hlow : ∀ s (e' : τ →₀ ℕ), e'.degree < n → coeff e' (x s) = coeff e' (y s) :=
        fun s e' he' => ih _ he' s e' rfl (by omega)
      have h1 := h i e (by omega)
      have hlg : G.lg i = X i + (G.lg i - X i) := by ring
      rw [hlg, subst_add hsx, subst_add hsy, subst_X hsx, subst_X hsy, map_add, map_add,
        ag_lemma_15 hx hy n hlow _ (hr0 i) (hr1 i) e (le_of_eq hen)] at h1
      exact add_right_cancel h1
  intro i e he
  exact key _ i e rfl he

private theorem rs_lemma_6 (c : C) (f : PowerSeries C) (n : ℕ) :
    coeff (Finsupp.single () n) (PowerSeries.rescale c f) =
      c ^ n * coeff (Finsupp.single () n) f :=
  PowerSeries.coeff_rescale f c n

private theorem rc_lemma_8 (c : C) (f : PowerSeries C) (hf : constantCoeff f = 0) :
    constantCoeff (PowerSeries.rescale c f) = 0 := by
  have h1 := rs_lemma_6 c f 0
  rw [Finsupp.single_zero, MvPowerSeries.coeff_zero_eq_constantCoeff_apply,
    MvPowerSeries.coeff_zero_eq_constantCoeff_apply, hf, mul_zero] at h1
  exact h1

private theorem rp_lemma_7 (c : C) (ga : Fin d → PowerSeries C) (m : Fin d →₀ ℕ) :
    (m.prod fun b k => (rescaleCurve c ga b) ^ k) =
      PowerSeries.rescale c (m.prod fun b k => ga b ^ k) := by
  unfold Finsupp.prod
  rw [map_prod]
  simp only [map_pow]
  rfl

theorem pt_lg_rescale (G : LogFGL v d) (c : C) {ga : Fin d → PowerSeries C}
    (h0 : ∀ b, constantCoeff (ga b) = 0) (a : Fin d) :
    G.lgCurve (rescaleCurve c ga) a = PowerSeries.rescale c (G.lgCurve ga a) := by
  have hs : HasSubst ga := hs_lemma h0
  have hs' : HasSubst (rescaleCurve c ga) := hs_lemma fun b => rc_lemma_8 c (ga b) (h0 b)
  refine MvPowerSeries.ext fun e => ?_
  obtain ⟨n, rfl⟩ : ∃ n, e = Finsupp.single () n := ⟨e (), Finsupp.unique_single e⟩
  rw [rs_lemma_6, show G.lgCurve (rescaleCurve c ga) a = subst (rescaleCurve c ga) (G.lg a) from rfl,
    show G.lgCurve ga a = subst ga (G.lg a) from rfl, coeff_subst hs', coeff_subst hs,
    mul_finsum]
  apply finsum_congr
  intro m
  rw [rp_lemma_7, rs_lemma_6, smul_eq_mul, smul_eq_mul]
  ring

theorem pt_rescale_good {c : C} (hc : c ∈ ptIntSub v) {ga : Fin d → PowerSeries C}
    (h : PTGood v ga) : PTGood v (rescaleCurve c ga) := by
  intro i
  obtain ⟨h0, hi⟩ := h i
  have hi' : ∀ e, coeff e (ga i) ∈ ptIntSub v := hi
  refine ⟨rc_lemma_8 c (ga i) h0, ?_⟩
  show ∀ e, coeff e (PowerSeries.rescale c (ga i)) ∈ ptIntSub v
  intro e
  obtain ⟨n, rfl⟩ : ∃ n, e = Finsupp.single () n := ⟨e (), Finsupp.unique_single e⟩
  rw [rs_lemma_6]
  exact Subring.mul_mem _ (Subring.pow_mem _ hc n) (hi' _)

end

end ReciprocityTheory.ChartRestriction.G.Sh
