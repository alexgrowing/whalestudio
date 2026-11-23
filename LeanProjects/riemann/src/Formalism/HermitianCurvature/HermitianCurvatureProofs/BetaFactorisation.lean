import Formalism.HermitianCurvature.StatementSz

namespace Formalism.FourierDecayAlt.P

open Formalism.FourierDecayAlt.Sz Finset

namespace Sz6

theorem sqrt_prod_nonneg {α : Type} (s : Finset α) (f : α → ℝ) (h : ∀ i ∈ s, 0 ≤ f i) :
    Real.sqrt (∏ i ∈ s, f i) = ∏ i ∈ s, Real.sqrt (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [prod_insert ha, prod_insert ha, Real.sqrt_mul (h a (mem_insert_self a s)),
      ih (fun i hi => h i (mem_insert_of_mem hi))]

theorem Icc_one_eq (n : ℕ) : Icc 1 n = Ico 1 (n + 1) := by
  ext x; simp only [mem_Icc, mem_Ico]; omega

theorem prob_and_eq_mul_of_disjoint (c : Cfg) (hk : 1 ≤ c.k) (Y : ℝ) :
    c.P Y = (∏ i ∈ Icc 1 (c.k - 1), (Y + c.v i)) * ∏ j ∈ Icc 1 c.m, (Y - c.b j) := by
  have e1 : Icc 1 (c.k + c.m - 1) = Ico 1 (c.k + c.m) := by
    ext x; simp only [mem_Icc, mem_Ico]; omega
  have e2 : Icc 1 (c.k - 1) = Ico 1 c.k := by
    ext x; simp only [mem_Icc, mem_Ico]; omega
  unfold Cfg.P
  rw [e1, e2, Icc_one_eq, ← prod_Ico_consecutive _ hk (Nat.le_add_right c.k c.m)]
  congr 1
  · apply prod_congr rfl
    intro i hi
    rw [mem_Ico] at hi
    simp only [Cfg.lam, if_pos hi.2]
  · rw [prod_Ico_eq_prod_range, prod_Ico_eq_prod_range]
    have a1 : c.k + c.m - c.k = c.m := by omega
    have a2 : c.m + 1 - 1 = c.m := by omega
    rw [a1, a2]
    apply prod_congr rfl
    intro i _
    have n1 : ¬ (c.k + i < c.k) := by omega
    have n2 : c.k + i + 1 - c.k = 1 + i := by omega
    simp only [Cfg.lam, if_neg n1, n2]
    ring

theorem prod_split_first (k : ℕ) (hk : 1 ≤ k) (F : ℕ → ℝ) :
    ∏ i ∈ Icc 1 k, F i = F 1 * ∏ i ∈ Icc 1 (k - 1), F (i + 1) := by
  have e2 : Icc 1 (k - 1) = Ico 1 k := by
    ext x; simp only [mem_Icc, mem_Ico]; omega
  rw [Icc_one_eq, e2, prod_eq_prod_Ico_succ_bot (by omega), prod_Ico_add' F 1 k 1]

theorem u_succ (c : Cfg) (de : ℕ → ℝ) (hw : IsWord c.k de) (i : ℕ) (hi : 1 ≤ i)
    (hnt : ¬ (c.top = true ∧ i + 1 = c.k)) :
    c.u de (i + 1) = c.v i - 1 / 2 - de i * c.Del := by
  have n1 : ¬ (i + 1 = 1) := by omega
  by_cases hk : i + 1 = c.k
  · have ht : ¬ (c.top = true) := fun ht => hnt ⟨ht, hk⟩
    have hik : i = c.k - 1 := by omega
    have hiR : (i : ℝ) = (c.k : ℝ) - 1 := by
      have : ((i + 1 : ℕ) : ℝ) = (c.k : ℝ) := by rw [hk]
      push_cast at this; linarith
    have hd : de i = 0 := by rw [hik]; exact hw.2
    simp only [Cfg.u, if_neg n1, if_pos hk, Cfg.ulast, if_neg ht, Cfg.v, hiR, hd]
    ring
  · simp only [Cfg.u, if_neg n1, if_neg hk, Nat.add_sub_cancel]

theorem u_top (c : Cfg) (de : ℕ → ℝ) (i : ℕ) (hi : 1 ≤ i) (ht : c.top = true)
    (hk : i + 1 = c.k) : c.u de (i + 1) = -c.bp := by
  have n1 : ¬ (i + 1 = 1) := by omega
  simp only [Cfg.u, if_neg n1, if_pos hk, Cfg.ulast, if_pos ht]

end Sz6

theorem betaFactorisation : Factorisation := by
  intro c de de' ka T T' Y l h hw hw' hT hT' hl hlk hne hY
  obtain ⟨hY1, hY2⟩ := hY
  have hD := h.hDel
  have hk := h.hk
  have hk1 : 1 ≤ c.k := by omega
  have hlR : (l : ℝ) + 2 ≤ c.k := by exact_mod_cast hlk
  have hl1 : (1 : ℝ) ≤ l := by exact_mod_cast hl
  have hvl' : c.v l = c.vlast + 4 * c.Del * ((c.k : ℝ) - 1 - l) := rfl
  have m1 : 4 * c.Del * 1 ≤ 4 * c.Del * ((c.k : ℝ) - 1 - l) :=
    mul_le_mul_of_nonneg_left (by linarith) (by linarith)
  have hv0 := h.hv0
  have hYneg : Y ≤ -(7 / 2 * c.Del) := by linarith
  have hvl1 : c.v l ≤ c.v 1 := by simp only [Cfg.v]; push_cast; nlinarith
  have hkD : 0 < 4 * (c.k : ℝ) * c.Del := by
    have : (0 : ℝ) < c.k := by linarith
    positivity
  have ha : 0 < Y + 1 / 2 + c.a := by have := h.ha; linarith
  have hbj : ∀ j : ℕ, 1 ≤ j → j ≤ c.m → 1 ≤ c.b j := by
    intro j hj
    induction j, hj using Nat.le_induction with
    | base => intro _; exact h.hb1
    | succ n hn ih =>
      intro hm
      have i1 := ih (by omega)
      have i2 := h.hgap n hn (by omega)
      linarith
  have hvi : ∀ i : ℕ, c.v i + Y = (c.v l + Y) + 4 * c.Del * ((l : ℝ) - i) := by
    intro i; simp only [Cfg.v]; ring

  have hle : ∀ i : ℕ, i < l → c.v l + Y + 4 * c.Del ≤ c.v i + Y := by
    intro i hi
    have : (i : ℝ) + 1 ≤ l := by exact_mod_cast hi
    have : 4 * c.Del * 1 ≤ 4 * c.Del * ((l : ℝ) - i) :=
      mul_le_mul_of_nonneg_left (by linarith) (by linarith)
    rw [hvi i]; linarith
  have hge : ∀ i : ℕ, l < i → c.v i + Y ≤ c.v l + Y - 4 * c.Del := by
    intro i hi
    have : (l : ℝ) + 1 ≤ i := by exact_mod_cast hi
    have : 4 * c.Del * 1 ≤ 4 * c.Del * ((i : ℝ) - l) :=
      mul_le_mul_of_nonneg_left (by linarith) (by linarith)
    rw [hvi i]; linarith
  have hA0 : ∀ i : ℕ, Y + c.v i ≠ 0 ∧ Y + 1 + c.v i ≠ 0 := by
    intro i
    rcases lt_trichotomy i l with hi | hi | hi
    · have := hle i hi
      constructor <;> apply ne_of_gt <;> linarith
    · subst hi
      constructor <;> apply ne_of_gt <;> linarith
    · have := hge i hi
      constructor <;> apply ne_of_lt <;> linarith
  have hW : ∀ (e : ℕ → ℝ), IsWord c.k e → ∀ i : ℕ, c.v i - e i * c.Del - -Y ≠ 0 := by
    intro e he i
    rcases lt_trichotomy i l with hi | hi | hi
    · have := hle i hi
      apply ne_of_gt
      rcases he.1 i with a | a <;> rw [a] <;> linarith
    · subst hi
      rcases he.1 i with a | a <;> rw [a]
      · apply ne_of_gt; linarith
      · apply ne_of_lt; linarith
    · have := hge i hi
      apply ne_of_lt
      rcases he.1 i with a | a <;> rw [a] <;> linarith
  have hbp : c.top = true → 0 < c.bp + -Y - 1 / 2 := by
    intro ht
    obtain ⟨hb1, _⟩ := h.htop ht
    have := h.hb1
    linarith

  obtain ⟨A, hAdef⟩ : ∃ A : ℕ → ℝ, A = fun i => (c.v i - -Y) * (c.v i + 1 - -Y) := ⟨_, rfl⟩
  obtain ⟨B, hBdef⟩ : ∃ B : ℕ → ℝ,
      B = fun i => (Y + 1 / 2 + c.u de (i + 1)) * (Y + 1 / 2 + c.u de' (i + 1)) := ⟨_, rfl⟩
  obtain ⟨Nn, hNdef⟩ : ∃ Nn : ℕ → ℝ, Nn = fun j => (c.b j + -Y) * (c.b j + -Y - 1) := ⟨_, rfl⟩
  have hB : ∀ i ∈ Icc 1 (c.k - 1), B i ≠ 0 ∧
      c.rho de de' (-Y) i = Real.sqrt |A i| / Real.sqrt |B i| := by
    intro i hi
    rw [mem_Icc] at hi
    by_cases hc : c.top = true ∧ i + 1 = c.k
    · have p := hbp hc.1
      have eB : B i = (c.bp + -Y - 1 / 2) ^ 2 := by
        rw [hBdef]
        simp only [Sz6.u_top c de i hi.1 hc.1 hc.2, Sz6.u_top c de' i hi.1 hc.1 hc.2]
        ring
      refine ⟨by rw [eB]; positivity, ?_⟩
      rw [eB, abs_of_nonneg (sq_nonneg (c.bp + -Y - 1 / 2)), Real.sqrt_sq p.le, hAdef]
      simp only [Cfg.rho, if_pos hc]
    · have eB : B i = (c.v i - de i * c.Del - -Y) * (c.v i - de' i * c.Del - -Y) := by
        rw [hBdef]
        simp only [Sz6.u_succ c de hw i hi.1 hc, Sz6.u_succ c de' hw' i hi.1 hc]
        ring
      refine ⟨by rw [eB]; exact mul_ne_zero (hW de hw i) (hW de' hw' i), ?_⟩
      rw [eB, hAdef]
      simp only [Cfg.rho, if_neg hc]
  have hN : ∀ j ∈ Icc 1 c.m, 0 < Nn j := by
    intro j hj
    rw [mem_Icc] at hj
    have := hbj j hj.1 hj.2
    rw [hNdef]
    apply mul_pos <;> linarith
  have hq : c.q de de' T T' Y =
      -(T * T') * ((Y + 1 / 2 + c.a) ^ 2 * ∏ i ∈ Icc 1 (c.k - 1), B i) := by
    unfold Cfg.q
    rw [Sz6.prod_split_first c.k hk1, hBdef]
    have u1 : ∀ e : ℕ → ℝ, c.u e 1 = c.a := by intro e; simp only [Cfg.u, if_true]
    rw [u1, u1]
    ring
  have hPP : c.P Y * c.P (Y + 1) = (∏ j ∈ Icc 1 c.m, Nn j) * ∏ i ∈ Icc 1 (c.k - 1), A i := by
    rw [Sz6.prob_and_eq_mul_of_disjoint c hk1, Sz6.prob_and_eq_mul_of_disjoint c hk1, hNdef, hAdef]
    have x1 : (∏ j ∈ Icc 1 c.m, (c.b j + -Y) * (c.b j + -Y - 1)) =
        (∏ j ∈ Icc 1 c.m, (Y - c.b j)) * ∏ j ∈ Icc 1 c.m, (Y + 1 - c.b j) := by
      rw [← prod_mul_distrib]; apply prod_congr rfl; intro j _; ring
    have x2 : (∏ i ∈ Icc 1 (c.k - 1), (c.v i - -Y) * (c.v i + 1 - -Y)) =
        (∏ i ∈ Icc 1 (c.k - 1), (Y + c.v i)) * ∏ i ∈ Icc 1 (c.k - 1), (Y + 1 + c.v i) := by
      rw [← prod_mul_distrib]; apply prod_congr rfl; intro j _; ring
    rw [x1, x2]; ring
  have hbne : ∀ j ∈ Icc 1 c.m, Y - c.b j ≠ 0 ∧ Y + 1 - c.b j ≠ 0 := by
    intro j hj
    rw [mem_Icc] at hj
    have := hbj j hj.1 hj.2
    constructor <;> apply ne_of_lt <;> linarith
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hq]
    refine mul_ne_zero (neg_ne_zero.mpr (mul_pos hT hT').ne') (mul_ne_zero (by positivity) ?_)
    exact prod_ne_zero_iff.mpr (fun i hi => (hB i hi).1)
  · rw [Sz6.prob_and_eq_mul_of_disjoint c hk1]
    exact mul_ne_zero (prod_ne_zero_iff.mpr (fun i _ => (hA0 i).1))
      (prod_ne_zero_iff.mpr (fun j hj => (hbne j hj).1))
  · rw [Sz6.prob_and_eq_mul_of_disjoint c hk1]
    exact mul_ne_zero (prod_ne_zero_iff.mpr (fun i _ => (hA0 i).2))
      (prod_ne_zero_iff.mpr (fun j hj => (hbne j hj).2))
  · have hTT : 0 < T * T' := mul_pos hT hT'
    have hNpos : 0 ≤ ∏ j ∈ Icc 1 c.m, Nn j := prod_nonneg (fun j hj => (hN j hj).le)
    have habs : |c.P Y * c.P (Y + 1) / c.q de de' T T' Y| =
        ((∏ j ∈ Icc 1 c.m, Nn j) * ∏ i ∈ Icc 1 (c.k - 1), |A i|) /
          (T * T' * ((Y + 1 / 2 + c.a) ^ 2 * ∏ i ∈ Icc 1 (c.k - 1), |B i|)) := by
      rw [hPP, hq, abs_div, abs_mul, abs_mul, abs_mul, abs_neg, abs_of_pos hTT,
        abs_of_nonneg hNpos, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (Y + 1 / 2 + c.a) ^ 2),
        Finset.abs_prod, Finset.abs_prod]
    have hrho : ∏ i ∈ Icc 1 (c.k - 1), c.rho de de' (-Y) i =
        (∏ i ∈ Icc 1 (c.k - 1), Real.sqrt |A i|) / ∏ i ∈ Icc 1 (c.k - 1), Real.sqrt |B i| := by
      rw [← prod_div_distrib]
      exact prod_congr rfl (fun i hi => (hB i hi).2)
    have hNd : c.Nd (-Y) = ∏ j ∈ Icc 1 c.m, Real.sqrt (Nn j) := by
      rw [hNdef]; rfl
    have hU : c.U1 (-Y) = (Y + 1 / 2 + c.a)⁻¹ := by
      simp only [Cfg.U1, one_div]; congr 1; ring
    simp only [Cfg.be, Cfg.core]
    rw [habs, hrho, hNd, hU,
      Real.sqrt_div (mul_nonneg hNpos (prod_nonneg (fun i _ => abs_nonneg _))),
      Real.sqrt_mul hNpos, Real.sqrt_mul hTT.le, Real.sqrt_mul (sq_nonneg (Y + 1 / 2 + c.a)),
      Real.sqrt_sq ha.le, Sz6.sqrt_prod_nonneg _ _ (fun j hj => (hN j hj).le),
      Sz6.sqrt_prod_nonneg _ _ (fun i _ => abs_nonneg _),
      Sz6.sqrt_prod_nonneg _ _ (fun i _ => abs_nonneg _)]
    generalize Y + 1 / 2 + c.a = W
    ring

theorem nodeBound : NodeBound := by
  intro c Y l h hl hlk hY
  obtain ⟨hY1, hY2⟩ := hY
  have hD := h.hDel
  have hD0 : 0 < c.Del := by linarith
  have hb1 := h.hb1
  have hbj : ∀ j : ℕ, 1 ≤ j → j ≤ c.m → c.b 1 ≤ c.b j := by
    intro j hj
    induction j, hj using Nat.le_induction with
    | base => intro _; exact le_rfl
    | succ n hn ih =>
      intro hm
      have i1 := ih (by omega)
      have i2 := h.hgap n hn (by omega)
      linarith
  have hl1 : (1:ℝ) ≤ l := by exact_mod_cast hl
  have hlR : (l:ℝ) + 2 ≤ c.k := by exact_mod_cast hlk
  have hvl : c.v l ≤ c.v 1 := by simp only [Cfg.v]; push_cast; nlinarith
  have hvl' : c.v l = c.vlast + 4 * c.Del * ((c.k:ℝ) - 1 - l) := rfl
  have m1 : 4 * c.Del * 1 ≤ 4 * c.Del * ((c.k:ℝ) - 1 - l) :=
    mul_le_mul_of_nonneg_left (by linarith) (by linarith)
  have hv0 := h.hv0
  have hv1 := h.hv1
  obtain ⟨y, hy⟩ : ∃ y : ℝ, y = -Y := ⟨_, rfl⟩
  rw [← hy]
  have hy1 : 1 ≤ y := by rw [hy]; linarith
  have hy2 : y ≤ 4 * c.k * c.Del := by rw [hy]; linarith
  obtain ⟨E, hE⟩ : ∃ E : ℝ, E = Real.exp (4 * c.k * c.Del / c.b 1) := ⟨_, rfl⟩
  have hterm : ∀ j ∈ Icc 1 c.m, Real.sqrt ((c.b j + y) * (c.b j + y - 1)) ≤ c.b j * E := by
    intro j hj
    rw [mem_Icc] at hj
    have hb := hbj j hj.1 hj.2
    have hbpos : 0 < c.b j := by linarith
    have s1 : Real.sqrt ((c.b j + y) * (c.b j + y - 1)) ≤ c.b j + y := by
      rw [Real.sqrt_le_iff]; exact ⟨by linarith, by nlinarith⟩
    have s2 : c.b j + y ≤ c.b j * E := by
      have t1 : 1 + 4 * c.k * c.Del / c.b 1 ≤ E := by
        have := Real.add_one_le_exp (4 * c.k * c.Del / c.b 1); rw [hE]; linarith
      have t2 : y / c.b j ≤ 4 * c.k * c.Del / c.b 1 :=
        div_le_div₀ (by positivity) hy2 (by linarith) hb
      calc c.b j + y = c.b j * (1 + y / c.b j) := by field_simp
        _ ≤ c.b j * E := mul_le_mul_of_nonneg_left (by linarith) hbpos.le
    exact s1.trans s2
  simp only [Cfg.Nd, Cfg.prodb]
  calc ∏ j ∈ Icc 1 c.m, Real.sqrt ((c.b j + y) * (c.b j + y - 1))
      ≤ ∏ j ∈ Icc 1 c.m, (c.b j * E) := prod_le_prod (fun _ _ => Real.sqrt_nonneg _) hterm
    _ = (∏ j ∈ Icc 1 c.m, c.b j) * E ^ c.m := by
        rw [prod_mul_distrib, prod_const, Nat.card_Icc]; simp
    _ = Real.exp c.vth * ∏ j ∈ Icc 1 c.m, c.b j := by
        rw [mul_comm]; congr 1
        rw [hE, ← Real.exp_nat_mul]; congr 1; simp only [Cfg.vth]; ring

theorem edgeFactorBound : FirstBound := by
  intro c Y l h hl hlk hY
  obtain ⟨hY1, hY2⟩ := hY
  have hk4 : (4 : ℝ) ≤ c.k := by exact_mod_cast h.hk
  have hlR : (1 : ℝ) ≤ l := by exact_mod_cast hl
  have hD := h.hDel
  have hvl : c.v l ≤ c.v 1 := by
    simp only [Cfg.v]; push_cast; nlinarith
  have hpos : 0 < 4 * (c.k : ℝ) * c.Del := by positivity
  have ha := h.ha
  have hv1 := h.hv1
  have h1 : 0 < c.a - c.v 1 := by linarith
  have h2 : c.a - c.v 1 ≤ c.a + 1 / 2 - -Y := by linarith
  refine ⟨?_, ?_, ?_⟩
  · simp only [Cfg.U1]; apply one_div_pos.mpr; linarith
  · simp only [Cfg.U1]; exact one_div_le_one_div_of_le h1 h2
  · have ha0 : 0 < c.a := by
      have : 0 ≤ c.v 1 := by
        simp only [Cfg.v]; have := h.hv0; push_cast; nlinarith
      linarith
    rw [div_le_div_iff₀ h1 ha0]; linarith

theorem positionBefore : PositionBefore := by
  intro c de de' Y l i h hw hw' hi hil hlk hY
  obtain ⟨hY1, hY2⟩ := hY
  have hD := h.hDel
  have hnt : ¬ (c.top = true ∧ i + 1 = c.k) := by rintro ⟨_, h2⟩; omega
  obtain ⟨p, hp⟩ : ∃ p : ℝ, p = (l:ℝ) - i := ⟨_, rfl⟩
  have hp1 : 1 ≤ p := by
    have : (i:ℝ) + 1 ≤ l := by exact_mod_cast hil
    rw [hp]; linarith
  obtain ⟨d, hd⟩ : ∃ d : ℝ, d = c.v l + Y := ⟨_, rfl⟩
  rw [← hd] at hY1 hY2
  obtain ⟨X, hX⟩ : ∃ X : ℝ, X = 4 * c.Del * p + d := ⟨_, rfl⟩
  have hXv : c.v i + Y = X := by rw [hX, hd, hp]; simp only [Cfg.v]; ring
  simp only [Cfg.rho, if_neg hnt]
  rw [← hp]
  have e1 : (c.v i - -Y) * (c.v i + 1 - -Y) = X * (X + 1) := by rw [← hXv]; ring
  have e2 : (c.v i - de i * c.Del - -Y) * (c.v i - de' i * c.Del - -Y) =
      (X - de i * c.Del) * (X - de' i * c.Del) := by rw [← hXv]; ring
  rw [e1, e2]
  have mp : 4 * c.Del * 1 ≤ 4 * c.Del * p := mul_le_mul_of_nonneg_left hp1 (by linarith)
  have hXD : 0 < X - c.Del := by rw [hX]; linarith
  have hX0 : 0 < X := by linarith
  have ha : X - c.Del ≤ X - de i * c.Del := by
    rcases hw.1 i with a | a <;> rw [a] <;> linarith
  have hb : X - c.Del ≤ X - de' i * c.Del := by
    rcases hw'.1 i with a | a <;> rw [a] <;> linarith
  have hnum : Real.sqrt |X * (X + 1)| ≤ X + 1 := by
    rw [abs_of_pos (by positivity), Real.sqrt_le_iff]; exact ⟨by linarith, by nlinarith⟩
  have hden : X - c.Del ≤ Real.sqrt |(X - de i * c.Del) * (X - de' i * c.Del)| := by
    apply Real.le_sqrt_of_sq_le
    rw [abs_of_pos (mul_pos (by linarith) (by linarith)), sq]
    exact mul_le_mul ha hb hXD.le (by linarith)
  have h4p : 0 < 4 * p - 1 := by linarith
  have e3 : 1 + 2 / (4 * p - 1) = (4 * p + 1) / (4 * p - 1) := by field_simp; ring
  calc _ ≤ (X + 1) / (X - c.Del) := div_le_div₀ (by linarith) hnum hXD hden
    _ ≤ 1 + 2 / (4 * p - 1) := by
      rw [e3, div_le_div_iff₀ hXD h4p, hX]
      nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ p - 1) (by linarith : (0:ℝ) ≤ c.Del - 1)]

theorem positionAfter : PositionAfter := by
  intro c de de' Y l i h hw hw' hl hli hik hor hY
  obtain ⟨hY1, hY2⟩ := hY
  have hD := h.hDel
  have hnt : ¬ (c.top = true ∧ i + 1 = c.k) := by
    rintro ⟨h1, h2⟩
    rcases hor with h3 | h3
    · omega
    · rw [h1] at h3; exact absurd h3 (by decide)
  have hliR : (l:ℝ) + 1 ≤ i := by exact_mod_cast hli
  obtain ⟨X, hX⟩ : ∃ X : ℝ, X = -(c.v i + Y) := ⟨_, rfl⟩
  have hXge : 7 / 2 * c.Del ≤ X := by
    have e : c.v i = c.v l - 4 * c.Del * ((i:ℝ) - l) := by simp only [Cfg.v]; ring
    have : 4 * c.Del * 1 ≤ 4 * c.Del * ((i:ℝ) - l) :=
      mul_le_mul_of_nonneg_left (by linarith) (by linarith)
    rw [hX, e]; linarith
  simp only [Cfg.rho, if_neg hnt]
  have e1 : (c.v i - -Y) * (c.v i + 1 - -Y) = X * (X - 1) := by rw [hX]; ring
  have e2 : (c.v i - de i * c.Del - -Y) * (c.v i - de' i * c.Del - -Y) =
      (X + de i * c.Del) * (X + de' i * c.Del) := by rw [hX]; ring
  rw [e1, e2]
  have hX1 : 1 ≤ X := by linarith
  have ha : 0 ≤ de i * c.Del := by
    rcases hw.1 i with a | a <;> rw [a] <;> linarith
  have hb : 0 ≤ de' i * c.Del := by
    rcases hw'.1 i with a | a <;> rw [a] <;> linarith
  have hden : 0 < (X + de i * c.Del) * (X + de' i * c.Del) := by
    apply mul_pos <;> linarith
  rw [div_le_one (Real.sqrt_pos.mpr (abs_pos.mpr hden.ne'))]
  apply Real.sqrt_le_sqrt
  rw [abs_of_nonneg (mul_nonneg (by linarith) (by linarith)), abs_of_pos hden]
  nlinarith [mul_nonneg ha hb, mul_nonneg (by linarith : (0:ℝ) ≤ X) ha,
    mul_nonneg (by linarith : (0:ℝ) ≤ X) hb]

theorem slotAt_true : PositionAt := by
  intro c de de' Y l h hw hw' hl hlk hne hY
  obtain ⟨hY1, hY2⟩ := hY
  have hD := h.hDel
  set d := c.v l + Y with hd
  have hnt : ¬ (c.top = true ∧ l + 1 = c.k) := by rintro ⟨_, h2⟩; omega
  have hd0 : 0 < d := by linarith
  have hDd : 0 < c.Del - d := by linarith
  have e1 : c.v l - -Y = d := by rw [hd]; ring
  have e2 : c.v l + 1 - -Y = d + 1 := by rw [hd]; ring
  have hden : |(c.v l - de l * c.Del - -Y) * (c.v l - de' l * c.Del - -Y)| = d * (c.Del - d) := by
    rcases hw.1 l with a | a <;> rcases hw'.1 l with b | b
    · exact absurd (a.trans b.symm) hne
    · rw [a, b]
      have : (c.v l - 0 * c.Del - -Y) * (c.v l - 1 * c.Del - -Y) = -(d * (c.Del - d)) := by rw [hd]; ring
      rw [this, abs_neg, abs_of_pos (mul_pos hd0 hDd)]
    · rw [a, b]
      have : (c.v l - 1 * c.Del - -Y) * (c.v l - 0 * c.Del - -Y) = -(d * (c.Del - d)) := by rw [hd]; ring
      rw [this, abs_neg, abs_of_pos (mul_pos hd0 hDd)]
    · exact absurd (a.trans b.symm) hne
  have hrho : c.rho de de' (-Y) l = Real.sqrt ((d + 1) / (c.Del - d)) := by
    simp only [Cfg.rho, if_neg hnt, hden, e1, e2]
    rw [abs_of_pos (by positivity), ← Real.sqrt_div (by positivity)]
    congr 1
    field_simp
  refine ⟨hrho, ?_⟩
  rw [hrho]
  apply Real.sqrt_le_sqrt
  rw [div_le_div_iff₀ hDd (by positivity)]
  nlinarith

theorem positionTop : PositionTop := by
  intro c de de' Y l h ht hl hlk hY
  obtain ⟨hY1, hY2⟩ := hY
  have hD := h.hDel
  have hk := h.hk
  have hc : c.top = true ∧ c.k - 1 + 1 = c.k := ⟨ht, by omega⟩
  simp only [Cfg.rho, if_pos hc]
  obtain ⟨hb1, hb2⟩ := h.htop ht
  have hbp : 0 < c.bp := by have := h.hb1; linarith
  have hkc : ((c.k - 1 : ℕ) : ℝ) = (c.k:ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ c.k)]; norm_num
  have hvk : c.v (c.k - 1) = c.vlast := by simp only [Cfg.v, hkc]; ring
  obtain ⟨X, hX⟩ : ∃ X : ℝ, X = -(c.vlast + Y) := ⟨_, rfl⟩
  have hlR : (l:ℝ) + 2 ≤ c.k := by exact_mod_cast hlk
  have hl1 : (1:ℝ) ≤ l := by exact_mod_cast hl
  have hvl : c.v l = c.vlast + 4 * c.Del * ((c.k:ℝ) - 1 - l) := rfl
  have m1 : 4 * c.Del * 1 ≤ 4 * c.Del * ((c.k:ℝ) - 1 - l) :=
    mul_le_mul_of_nonneg_left (by linarith) (by linarith)
  have m2 : 4 * c.Del * ((c.k:ℝ) - 1 - l) ≤ 4 * c.Del * (c.k:ℝ) :=
    mul_le_mul_of_nonneg_left (by linarith) (by linarith)
  have hX1 : 7 / 2 * c.Del ≤ X := by rw [hX]; linarith
  have hX2 : X ≤ 4 * c.k * c.Del := by rw [hX]; linarith
  have hv0 := h.hv0
  rw [hvk]
  have e1 : (c.vlast - -Y) * (c.vlast + 1 - -Y) = X * (X - 1) := by rw [hX]; ring
  have hX0 : 0 ≤ X := by linarith
  rw [e1, abs_of_nonneg (mul_nonneg hX0 (by linarith))]
  have hs : Real.sqrt (X * (X - 1)) ≤ X := by
    rw [Real.sqrt_le_iff]; exact ⟨hX0, by nlinarith⟩
  have hden : c.bp ≤ c.bp + -Y - 1 / 2 := by
    have : -Y = X + c.vlast := by rw [hX]; ring
    linarith
  calc Real.sqrt (X * (X - 1)) / (c.bp + -Y - 1 / 2) ≤ X / c.bp := div_le_div₀ hX0 hs hbp hden
    _ ≤ 4 * c.k * c.Del / c.bp := div_le_div_of_nonneg_right hX2 hbp.le

theorem positionProduct : ProdOneAddTwoDivLeSqrt := by
  have key : ∀ p : ℕ, 1 ≤ p → 0 ≤ ∏ j ∈ Icc 1 p, (1 + 2 / (4 * (j : ℝ) - 1)) ∧
      (∏ j ∈ Icc 1 p, (1 + 2 / (4 * (j : ℝ) - 1))) ^ 2 ≤ 50 / 27 * ((p:ℝ) + 1 / 2) := by
    intro p hp
    induction p, hp using Nat.le_induction with
    | base => simp; norm_num
    | succ n hn ih =>
      obtain ⟨ih0, ih1⟩ := ih
      rw [Finset.prod_Icc_succ_top (by omega)]
      have hn1 : (1:ℝ) ≤ n := by exact_mod_cast hn
      have e : 1 + 2 / (4 * ((n + 1 : ℕ) : ℝ) - 1) = (4 * (n:ℝ) + 5) / (4 * (n:ℝ) + 3) := by
        have h4 : 4 * ((n:ℝ) + 1) - 1 ≠ 0 := by nlinarith
        push_cast; field_simp; ring
      rw [e]
      refine ⟨mul_nonneg ih0 (by positivity), ?_⟩
      rw [mul_pow, div_pow]
      have h3 : 0 < (4 * (n:ℝ) + 3) ^ 2 := by positivity
      rw [mul_div_assoc', div_le_iff₀ h3]
      push_cast
      have := mul_le_mul_of_nonneg_right ih1 (by positivity : (0:ℝ) ≤ (4 * (n:ℝ) + 5) ^ 2)
      nlinarith
  intro p hp
  obtain ⟨h0, h1⟩ := key p hp
  have hp1 : (1:ℝ) ≤ p := by exact_mod_cast hp
  have hs : 0 ≤ 3.3 * Real.sqrt p := by positivity
  refine (pow_le_pow_iff_left₀ h0 hs (two_ne_zero)).mp ?_
  rw [mul_pow, Real.sq_sqrt (by linarith)]
  norm_num
  linarith

theorem Sz6.positionsBefore_of (H1 : PositionBefore) (H2 : ProdOneAddTwoDivLeSqrt) : PositionsBefore := by
  intro c de de' Y l h hw hw' hl hlk hY
  have hk4 : (4:ℝ) ≤ c.k := by exact_mod_cast h.hk
  have step1 : ∏ i ∈ Ico 1 l, c.rho de de' (-Y) i ≤
      ∏ i ∈ Ico 1 l, (fun j : ℕ => (1 + 2 / (4 * (j : ℝ) - 1))) (l - i) := by
    apply prod_le_prod
    · intro i hi
      rw [mem_Ico] at hi
      have hnt : ¬ (c.top = true ∧ i + 1 = c.k) := by rintro ⟨_, h2⟩; omega
      simp only [Cfg.rho, if_neg hnt]; positivity
    · intro i hi
      rw [mem_Ico] at hi
      have := H1 c de de' Y l i h hw hw' hi.1 hi.2 hlk hY
      simp only [Nat.cast_sub hi.2.le]; exact this
  have step2 := Finset.prod_Ico_reflect (fun j : ℕ => (1 + 2 / (4 * (j : ℝ) - 1))) 1 (m := l) (n := l) (by omega)
  rw [step2] at step1
  have a1 : l + 1 - l = 1 := by omega
  have a2 : l + 1 - 1 = l := by omega
  rw [a1, a2] at step1
  refine step1.trans ?_
  obtain ⟨p, rfl⟩ : ∃ p, l = p + 1 := ⟨l - 1, by omega⟩
  rcases Nat.eq_zero_or_pos p with rfl | hp
  · simp
    have : (1:ℝ) ≤ Real.sqrt c.k := by rw [Real.one_le_sqrt]; linarith
    linarith
  · have e : Ico 1 (p + 1) = Icc 1 p := by ext x; simp only [mem_Ico, mem_Icc]; omega
    rw [e]
    refine (H2 p hp).trans ?_
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    apply Real.sqrt_le_sqrt
    exact_mod_cast (by omega : p ≤ c.k)

theorem positionsBefore : PositionsBefore :=
  Sz6.positionsBefore_of positionBefore positionProduct

end Formalism.FourierDecayAlt.P
