import Development.WeilBound.RepresentationTheoryGL.JacquetShalikaBounds.AbsoluteRigidity.NewtonLow

noncomputable section

open scoped ComplexConjugate
open Finset

namespace PositivityTheory.RgJS.Common0Aux

variable {W X : Type} {d : X → ℕ}

def Pw (q : W → ℕ) (A : ∀ x, W → Fin (d x) → ℂ) {ι : Type} [Fintype ι] (u : ι → X × ℝ) (w : W) (k : ℕ) : ℂ :=
  ∑ i, ∑ a, (A (u i).1 w a * (q w : ℂ) ^ (-((u i).2 : ℂ))) ^ (k + 1)

theorem cpow_real (q : ℕ) (t : ℝ) : (q : ℂ) ^ (-(t : ℂ)) = (((q : ℝ) ^ (-t) : ℝ) : ℂ) := by
  rw [Complex.ofReal_cpow (Nat.cast_nonneg q), Complex.ofReal_natCast, Complex.ofReal_neg]

theorem lterm_pair (q : W → ℕ) (hq : ∀ w, 2 ≤ q w) {α β : Type} [Fintype α] [Fintype β] (a : W → α → ℂ)
    (b : W → β → ℂ) (σ t t' : ℝ) (p : W × ℕ) :
    lterm q a b (((σ + t + t' : ℝ)) : ℂ) p =
      (∑ x, (a p.1 x * (q p.1 : ℂ) ^ (-(t : ℂ))) ^ (p.2 + 1)) *
        conj (∑ y, (b p.1 y * (q p.1 : ℂ) ^ (-(t' : ℂ))) ^ (p.2 + 1)) *
        ((q p.1 : ℂ) ^ (-(σ : ℂ))) ^ (p.2 + 1) / (p.2 + 1) := by
  have hq0 : (q p.1 : ℂ) ≠ 0 := by
    have := hq p.1
    exact_mod_cast (by omega : q p.1 ≠ 0)
  unfold lterm
  have e : (q p.1 : ℂ) ^ (-(((σ + t + t' : ℝ)) : ℂ)) =
      (q p.1 : ℂ) ^ (-(σ : ℂ)) * (q p.1 : ℂ) ^ (-(t : ℂ)) * (q p.1 : ℂ) ^ (-(t' : ℂ)) := by
    rw [← Complex.cpow_add _ _ hq0, ← Complex.cpow_add _ _ hq0]
    congr 1
    push_cast
    ring
  have hr' : conj ((q p.1 : ℂ) ^ (-(t' : ℂ))) = (q p.1 : ℂ) ^ (-(t' : ℂ)) := by
    rw [cpow_real, Complex.conj_ofReal]
  have h1 : ∑ x, (a p.1 x * (q p.1 : ℂ) ^ (-(t : ℂ))) ^ (p.2 + 1) =
      (∑ x, a p.1 x ^ (p.2 + 1)) * ((q p.1 : ℂ) ^ (-(t : ℂ))) ^ (p.2 + 1) := by
    rw [Finset.sum_mul]
    simp only [mul_pow]
  have h2 : ∑ y, (b p.1 y * (q p.1 : ℂ) ^ (-(t' : ℂ))) ^ (p.2 + 1) =
      (∑ y, b p.1 y ^ (p.2 + 1)) * ((q p.1 : ℂ) ^ (-(t' : ℂ))) ^ (p.2 + 1) := by
    rw [Finset.sum_mul]
    simp only [mul_pow]
  rw [h1, h2, map_mul, map_pow, hr', e]
  ring

theorem sum_lterm (q : W → ℕ) (hq : ∀ w, 2 ≤ q w) (A : ∀ x, W → Fin (d x) → ℂ) {ι κ : Type} [Fintype ι] [Fintype κ]
    (u : ι → X × ℝ) (v : κ → X × ℝ) (σ : ℝ) (p : W × ℕ) :
    ∑ i, ∑ j, lterm q (A (u i).1) (A (v j).1) (((σ + (u i).2 + (v j).2 : ℝ)) : ℂ) p =
      Pw q A u p.1 p.2 * conj (Pw q A v p.1 p.2) * ((q p.1 : ℂ) ^ (-(σ : ℂ))) ^ (p.2 + 1) / (p.2 + 1) := by
  simp only [lterm_pair q hq]
  unfold Pw
  rw [map_sum, Finset.sum_mul_sum]
  simp only [Finset.sum_mul, Finset.sum_div]

def cc (q : W → ℕ) (A : ∀ x, W → Fin (d x) → ℂ) {ι : Type} [Fintype ι] (u : ι → X × ℝ) (p : W × ℕ) : ℝ :=
  ‖Pw q A u p.1 p.2‖ ^ 2 / ((p.2 : ℝ) + 1)

def ll (q : W → ℕ) (p : W × ℕ) : ℝ := ((p.2 : ℝ) + 1) * Real.log (q p.1)

theorem cc_nonneg (q : W → ℕ) (A : ∀ x, W → Fin (d x) → ℂ) {ι : Type} [Fintype ι] (u : ι → X × ℝ) (p : W × ℕ) :
    0 ≤ cc q A u p := by
  unfold cc; positivity

theorem ll_nonneg (q : W → ℕ) (hq : ∀ w, 2 ≤ q w) (p : W × ℕ) : 0 ≤ ll q p := by
  unfold ll
  have h : (1 : ℝ) ≤ q p.1 := by exact_mod_cast (le_trans (by norm_num) (hq p.1))
  have := Real.log_nonneg h
  positivity

theorem term_real (q : W → ℕ) (hq : ∀ w, 2 ≤ q w) (A : ∀ x, W → Fin (d x) → ℂ) {ι : Type} [Fintype ι]
    (u : ι → X × ℝ) (σ : ℝ) (p : W × ℕ) :
    Pw q A u p.1 p.2 * conj (Pw q A u p.1 p.2) * ((q p.1 : ℂ) ^ (-(σ : ℂ))) ^ (p.2 + 1) / (p.2 + 1) =
      ((cc q A u p * Real.exp (-(ll q p * σ)) : ℝ) : ℂ) := by
  have hqpos : (0 : ℝ) < q p.1 := by exact_mod_cast (lt_of_lt_of_le (by norm_num) (hq p.1))
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, cpow_real]
  have e : ((q p.1 : ℝ) ^ (-σ)) ^ (p.2 + 1) = Real.exp (-(ll q p * σ)) := by
    rw [← Real.rpow_mul_natCast hqpos.le, Real.rpow_def_of_pos hqpos]
    unfold ll
    congr 1
    push_cast
    ring
  rw [← Complex.ofReal_pow, e]
  unfold cc
  push_cast
  ring

theorem exists_pos_le {ι : Type} [Fintype ι] (f : ι → ℝ) (P : ι → Prop) (h : ∀ i, P i → 0 < f i) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧ ∀ i, P i → δ ≤ f i := by
  classical
  by_cases hs : (univ.filter P).Nonempty
  · refine ⟨min 1 ((univ.filter P).inf' hs f), lt_min one_pos ((Finset.lt_inf'_iff hs).2 fun j hj => h j ?_),
      min_le_left _ _, fun i hi => (min_le_right _ _).trans (Finset.inf'_le _ ?_)⟩
    · simpa using hj
    · simpa using hi
  · exact ⟨1, one_pos, le_rfl, fun i hi => absurd ⟨i, by simpa using hi⟩ hs⟩

theorem sum_subtype_ite {ι : Type} [Fintype ι] (P : ι → Prop) [DecidablePred P] (f : ι → ℂ) :
    ∑ i : {i // P i}, f i = ∑ i, if P i then f i else 0 := by
  rw [← Finset.sum_filter]
  exact (Finset.sum_subtype (univ.filter P) (by simp) f).symm

theorem dsum_subtype {ι : Type} [Fintype ι] (P : ι → Prop) [DecidablePred P] (f : ι → ι → ℂ) :
    ∑ i : {i // P i}, ∑ j : {i // P i}, f i j = ∑ i, ∑ j, if P i ∧ P j then f i j else 0 := by
  rw [sum_subtype_ite P (fun i => ∑ j : {i // P i}, f i j)]
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases hi : P i
  · simp [hi, sum_subtype_ite P (fun j => f i j)]
  · simp [hi]

open Classical in

def gf {ι κ : Type} (F : ι × κ → ℂ → ℂ) (x : ι → X × ℝ) (y : κ → X × ℝ) (p : ι × κ) (s : ℂ) : ℂ :=
  if (x p.1).1 = (y p.2).1 then F p (s + (((x p.1).2 + (y p.2).2 : ℝ) : ℂ)) / (s + (((x p.1).2 + (y p.2).2 : ℝ) : ℂ) - 1)
  else F p (s + (((x p.1).2 + (y p.2).2 : ℝ) : ℂ))

end PositivityTheory.RgJS.Common0Aux

open PositivityTheory.RgJS.Common0Aux in
theorem PositivityTheory.RgJS.common_of_landau_euler : LandauL → EulerLog → Conv1 → Unb → Common0 := by
  classical
  intro hL hE hC hU W q X d A hS ι κ _ _ x y hR ht ht' h0
  by_contra hne
  push Not at hne
  have hq := hS.primes.two
  have hP : ∀ w k, Pw q A y w k = Pw q A x w k := fun w k => (hR w (k + 1)).symm
  have hxy : ∀ (σ : ℝ) (p : W × ℕ), ∑ i, ∑ j, lterm q (A (x i).1) (A (y j).1) (((σ + (x i).2 + (y j).2 : ℝ)) : ℂ) p =
      ((cc q A x p * Real.exp (-(ll q p * σ)) : ℝ) : ℂ) := fun σ p => by
    rw [sum_lterm q hq A x y σ p, hP, term_real q hq A x σ p]
  have hxx : ∀ (σ : ℝ) (p : W × ℕ), ∑ i, ∑ j, lterm q (A (x i).1) (A (x j).1) (((σ + (x i).2 + (x j).2 : ℝ)) : ℂ) p =
      ((cc q A x p * Real.exp (-(ll q p * σ)) : ℝ) : ℂ) := fun σ p => by
    rw [sum_lterm q hq A x x σ p, term_real q hq A x σ p]
  have hsum : ∀ (u v : X) (s : ℝ), 1 < s → Summable fun p => ‖lterm q (A u) (A v) (s : ℂ) p‖ :=
    fun u v s hs => (hC W q X d A hS u v).1 s hs
  have hcn : ∀ (σ : ℝ) (p : W × ℕ), 0 ≤ cc q A x p * Real.exp (-(ll q p * σ)) := fun σ p =>
    mul_nonneg (cc_nonneg q A x p) (Real.exp_pos _).le

  have hD1 : ∀ σ : ℝ, 1 < σ → Summable fun p => cc q A x p * Real.exp (-(ll q p * σ)) := by
    intro σ hσ
    refine Summable.of_nonneg_of_le (hcn σ) (fun p => ?_)
      (summable_sum (s := Finset.univ) fun i _ => summable_sum (s := Finset.univ) fun j _ =>
        hsum (x i).1 (y j).1 (σ + (x i).2 + (y j).2) (by linarith [ht i, ht' j]))
    calc cc q A x p * Real.exp (-(ll q p * σ)) = ‖((cc q A x p * Real.exp (-(ll q p * σ)) : ℝ) : ℂ)‖ := by
          rw [Complex.norm_real, Real.norm_of_nonneg (hcn σ p)]
      _ = ‖∑ i, ∑ j, lterm q (A (x i).1) (A (y j).1) (((σ + (x i).2 + (y j).2 : ℝ)) : ℂ) p‖ := by rw [hxy]
      _ ≤ ∑ i, ∑ j, ‖lterm q (A (x i).1) (A (y j).1) (((σ + (x i).2 + (y j).2 : ℝ)) : ℂ) p‖ :=
          (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => norm_sum_le _ _)

  obtain ⟨δ, hδ, hδ1, hδle⟩ := exists_pos_le (fun p : ι × κ => (x p.1).2 + (y p.2).2)
    (fun p => (x p.1).1 = (y p.2).1) (by
      rintro ⟨i, j⟩ hij
      have h1 := ht i
      have h2 := ht' j
      rcases (add_nonneg h1 h2).lt_or_eq with h | h
      · exact h
      · exfalso
        have a1 : (x i).2 = 0 := by linarith
        have a2 : (y j).2 = 0 := by linarith
        exact hne i j (Prod.ext hij (by rw [a1, a2])))
  choose F σ0 hFa hFe using fun p : ι × κ => hS.rs (x p.1).1 (y p.2).1
  have hGa' : ∀ σ : ℝ, 1 - δ < σ → ∀ p : ι × κ, AnalyticAt ℂ (gf F x y p) σ := by
    intro σ hσ p
    have hpos : 0 < σ + ((x p.1).2 + (y p.2).2) := by linarith [ht p.1, ht' p.2]
    have hF' : AnalyticAt ℂ (fun s : ℂ => F p (s + (((x p.1).2 + (y p.2).2 : ℝ) : ℂ))) (σ : ℂ) := by
      have := hFa p (σ + ((x p.1).2 + (y p.2).2)) hpos
      have hlin : AnalyticAt ℂ (fun s : ℂ => s + (((x p.1).2 + (y p.2).2 : ℝ) : ℂ)) (σ : ℂ) :=
        analyticAt_id.add analyticAt_const
      exact AnalyticAt.comp_of_eq this hlin (by push_cast; ring)
    by_cases hc : (x p.1).1 = (y p.2).1
    · have hne1 : (σ : ℂ) + (((x p.1).2 + (y p.2).2 : ℝ) : ℂ) - 1 ≠ 0 := by
        have h3 : 1 < σ + ((x p.1).2 + (y p.2).2) := by have := hδle p hc; linarith
        intro h
        have := congrArg Complex.re h
        simp at this
        linarith
      have : AnalyticAt ℂ (fun s : ℂ => F p (s + (((x p.1).2 + (y p.2).2 : ℝ) : ℂ)) /
          (s + (((x p.1).2 + (y p.2).2 : ℝ) : ℂ) - 1)) (σ : ℂ) :=
        hF'.div ((analyticAt_id.add analyticAt_const).sub analyticAt_const) hne1
      have hgf : gf F x y p = fun s : ℂ => F p (s + (((x p.1).2 + (y p.2).2 : ℝ) : ℂ)) /
          (s + (((x p.1).2 + (y p.2).2 : ℝ) : ℂ) - 1) := by
        funext s
        unfold gf
        rw [if_pos hc]
      rw [hgf]
      exact this
    · have hgf : gf F x y p = fun s : ℂ => F p (s + (((x p.1).2 + (y p.2).2 : ℝ) : ℂ)) := by
        funext s
        unfold gf
        rw [if_neg hc]
      rw [hgf]
      exact hF'
  have hGa : ∀ σ : ℝ, 1 - δ < σ → AnalyticAt ℂ (fun s => ∏ p, gf F x y p s) σ := by
    intro σ hσ
    have := Finset.analyticAt_prod (f := fun p => gf F x y p) Finset.univ (fun p _ => hGa' σ hσ p)
    rw [Finset.prod_fn] at this
    exact this
  set σ₁ : ℝ := 2 + ∑ p, |σ0 p| with hσ₁
  have hσ0le : ∀ p, σ0 p ≤ σ₁ - 2 := fun p => by
    have := Finset.single_le_sum (f := fun p => |σ0 p|) (fun p _ => abs_nonneg _) (Finset.mem_univ p)
    have := le_abs_self (σ0 p)
    simp only [hσ₁]
    linarith
  have hσ₁2 : 2 ≤ σ₁ := by
    have : 0 ≤ ∑ p, |σ0 p| := Finset.sum_nonneg fun p _ => abs_nonneg _
    simp only [hσ₁]
    linarith
  have hGe : ∀ σ : ℝ, σ₁ < σ → (fun s => ∏ p, gf F x y p s) σ =
      ((Real.exp (∑' p, cc q A x p * Real.exp (-(ll q p * σ))) : ℝ) : ℂ) := by
    intro σ hσ
    have hs' : ∀ p : ι × κ, Summable fun r => lterm q (A (x p.1).1) (A (y p.2).1) (((σ + (x p.1).2 + (y p.2).2 : ℝ)) : ℂ) r :=
      fun p => (hsum _ _ _ (by linarith [ht p.1, ht' p.2])).of_norm
    have hg : ∀ p : ι × κ, gf F x y p σ =
        Complex.exp (∑' r, lterm q (A (x p.1).1) (A (y p.2).1) (((σ + (x p.1).2 + (y p.2).2 : ℝ)) : ℂ) r) := by
      intro p
      have hs : σ0 p < σ + (x p.1).2 + (y p.2).2 := by linarith [hσ0le p, ht p.1, ht' p.2]
      have hs2 : 2 < ((((σ + (x p.1).2 + (y p.2).2 : ℝ)) : ℂ)).re := by
        rw [Complex.ofReal_re]
        linarith [ht p.1, ht' p.2]
      have hEL := (hE W q (Fin (d (x p.1).1)) (Fin (d (y p.2).1)) (A (x p.1).1) (A (y p.2).1) _ hS.primes
        (hS.bd _) (hS.bd _) hs2).2.1
      have hFE := hFe p _ hs
      have ecast : (σ : ℂ) + (((x p.1).2 + (y p.2).2 : ℝ) : ℂ) = (((σ + (x p.1).2 + (y p.2).2 : ℝ)) : ℂ) := by
        push_cast
        ring
      unfold gf
      rw [ecast]
      split_ifs with hc
      · have hne1 : ((((σ + (x p.1).2 + (y p.2).2 : ℝ)) : ℂ)) - 1 ≠ 0 := by
          intro h
          have := congrArg Complex.re h
          simp at this
          linarith [ht p.1, ht' p.2]
        rw [hFE, if_pos hc, mul_div_cancel_left₀ _ hne1, hEL]
      · rw [hFE, if_neg hc, one_mul, hEL]
    show ∏ p, gf F x y p σ = _
    simp only [hg]
    rw [← Complex.exp_sum, ← Summable.tsum_finsetSum (fun p _ => hs' p)]
    simp only [Fintype.sum_prod_type]
    rw [show (fun r => ∑ i, ∑ j, lterm q (A (x i).1) (A (y j).1) (((σ + (x i).2 + (y j).2 : ℝ)) : ℂ) r) =
      fun r => ((cc q A x r * Real.exp (-(ll q r * σ)) : ℝ) : ℂ) from funext (hxy σ)]
    rw [← Complex.ofReal_tsum, ← Complex.ofReal_exp]
  have hL1 := hL (W × ℕ) (cc q A x) (ll q) (1 - δ) σ₁ (fun s => ∏ p, gf F x y p s) (cc_nonneg q A x) (ll_nonneg q hq)
    hGa (fun σ hσ => hD1 σ (by linarith)) hGe 1 (by linarith)

  obtain ⟨τ, hτ, -, hτle⟩ := exists_pos_le (fun i => (x i).2) (fun i => (x i).2 ≠ 0)
    (fun i hi => lt_of_le_of_ne (ht i) (Ne.symm hi))
  choose M hM using fun i i' : ι => (hC W q X d A hS (x i).1 (x i').1).2 (1 + τ) (by linarith)
  obtain ⟨i₀, hi₀⟩ := h0
  have : Nonempty {i // (x i).2 = 0} := ⟨⟨i₀, hi₀⟩⟩
  refine hU W q X d A hS {i // (x i).2 = 0} (fun i => (x i.1).1)
    ⟨(∑' p, cc q A x p * Real.exp (-(ll q p * 1))) + ∑ i, ∑ i', |M i i'|, fun σ hσ1 hσ2 => ?_⟩
  have hs : ∀ i j, Summable fun p => lterm q (A (x i).1) (A (x j).1) (((σ + (x i).2 + (x j).2 : ℝ)) : ℂ) p :=
    fun i j => (hsum _ _ _ (by linarith [ht i, ht j])).of_norm
  have hform : ∑ i : {i // (x i).2 = 0}, ∑ j : {i // (x i).2 = 0}, ∑' p, lterm q (A (x i.1).1) (A (x j.1).1) (σ : ℂ) p =
      ∑ i : {i // (x i).2 = 0}, ∑ j : {i // (x i).2 = 0},
        ∑' p, lterm q (A (x i.1).1) (A (x j.1).1) (((σ + (x i.1).2 + (x j.1).2 : ℝ)) : ℂ) p := by
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [i.2, j.2, add_zero, add_zero]
  have htot : ∑ i, ∑ j, ∑' p, lterm q (A (x i).1) (A (x j).1) (((σ + (x i).2 + (x j).2 : ℝ)) : ℂ) p =
      ((∑' p, cc q A x p * Real.exp (-(ll q p * σ)) : ℝ) : ℂ) := by
    calc ∑ i, ∑ j, ∑' p, lterm q (A (x i).1) (A (x j).1) (((σ + (x i).2 + (x j).2 : ℝ)) : ℂ) p
        = ∑ i, ∑' p, ∑ j, lterm q (A (x i).1) (A (x j).1) (((σ + (x i).2 + (x j).2 : ℝ)) : ℂ) p :=
          Finset.sum_congr rfl fun i _ => (Summable.tsum_finsetSum fun j _ => hs i j).symm
      _ = ∑' p, ∑ i, ∑ j, lterm q (A (x i).1) (A (x j).1) (((σ + (x i).2 + (x j).2 : ℝ)) : ℂ) p :=
          (Summable.tsum_finsetSum fun i _ => summable_sum (s := Finset.univ) fun j _ => hs i j).symm
      _ = ∑' p, ((cc q A x p * Real.exp (-(ll q p * σ)) : ℝ) : ℂ) := tsum_congr fun p => hxx σ p
      _ = _ := (Complex.ofReal_tsum _).symm
  rw [hform, dsum_subtype (fun i => (x i).2 = 0)
    (fun i j => ∑' p, lterm q (A (x i).1) (A (x j).1) (((σ + (x i).2 + (x j).2 : ℝ)) : ℂ) p)]
  set f : ι → ι → ℂ := fun i j => ∑' p, lterm q (A (x i).1) (A (x j).1) (((σ + (x i).2 + (x j).2 : ℝ)) : ℂ) p with hf
  have hsplit : ∑ i, ∑ j, f i j = (∑ i, ∑ j, if (x i).2 = 0 ∧ (x j).2 = 0 then f i j else 0) +
      ∑ i, ∑ j, if (x i).2 = 0 ∧ (x j).2 = 0 then 0 else f i j := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    split_ifs <;> simp
  have hrest : ‖∑ i, ∑ j, if (x i).2 = 0 ∧ (x j).2 = 0 then (0 : ℂ) else f i j‖ ≤ ∑ i, ∑ i', |M i i'| := by
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => (norm_sum_le _ _).trans
      (Finset.sum_le_sum fun j _ => ?_))
    split_ifs with hij
    · simp
    · have hge : 1 + τ ≤ σ + (x i).2 + (x j).2 := by
        rcases not_and_or.1 hij with h | h
        · linarith [hτle i h, ht j]
        · linarith [hτle j h, ht i]
      exact (hM i j _ hge).trans (le_abs_self _)
  have hDle : (∑' p, cc q A x p * Real.exp (-(ll q p * σ))) ≤ ∑' p, cc q A x p * Real.exp (-(ll q p * 1)) := by
    refine Summable.tsum_le_tsum (fun p => ?_) (hD1 σ hσ1) hL1
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) (cc_nonneg q A x p)
    have := ll_nonneg q hq p
    nlinarith
  have hD0 : 0 ≤ ∑' p, cc q A x p * Real.exp (-(ll q p * σ)) := tsum_nonneg (hcn σ)
  have heq : (∑ i, ∑ j, if (x i).2 = 0 ∧ (x j).2 = 0 then f i j else 0) =
      ((∑' p, cc q A x p * Real.exp (-(ll q p * σ)) : ℝ) : ℂ) -
        ∑ i, ∑ j, if (x i).2 = 0 ∧ (x j).2 = 0 then 0 else f i j := by
    rw [← htot, hsplit]
    ring
  rw [heq]
  calc ‖((∑' p, cc q A x p * Real.exp (-(ll q p * σ)) : ℝ) : ℂ) -
        ∑ i, ∑ j, if (x i).2 = 0 ∧ (x j).2 = 0 then 0 else f i j‖
      ≤ ‖((∑' p, cc q A x p * Real.exp (-(ll q p * σ)) : ℝ) : ℂ)‖ +
        ‖∑ i, ∑ j, if (x i).2 = 0 ∧ (x j).2 = 0 then (0 : ℂ) else f i j‖ := norm_sub_le _ _
    _ ≤ _ := by
        rw [Complex.norm_real, Real.norm_of_nonneg hD0]
        linarith
