import Formalism.SharpRestriction.GrowthBounds.LogarithmicSums.PrimeSums

noncomputable section

open scoped BigOperators
open NumberField Formalism.FrobeniusOrbits Formalism.BasicNotions Formalism.MainNotions.G

namespace Formalism.MainNotions.AuxBlock8.Pf.G5

variable {D : D7} {L : SizeData₂ D}

private lemma scale_a_pos' (s : Scale) : 0 < s.a := by
  unfold Scale.a Scale.b
  exact mul_pos (by linarith [s.one_lt_alt]) (Real.exp_pos _)

private lemma scale_b_pos (s : Scale) : 0 < s.b := by
  unfold Scale.b
  exact Real.exp_pos _

theorem sc_b'_pos (s : Scale) : 0 < s.b' := by
  unfold Scale.b' Scale.X'
  exact div_pos (scale_a_pos' s) (Real.exp_pos _)

theorem sc_w''_pos (s : Scale) (n : ℕ) (hn : 1 ≤ n) : 0 < s.w'' n := by
  have hx : 0 < s.x := by linarith [s.one_lt_alt]
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  unfold Scale.w''
  exact div_pos (sc_b'_pos s) (mul_pos hx hn')

theorem n_pos (D : D7) : 1 ≤ D.R.n := by
  unfold Ranks.n
  have h1 := D.R.m_le_f
  have h2 := D.R.two_le_m
  omega

theorem fill_top (X : Inst D L) (b : HH D → ℤ) (j : ℕ) (s : HH D) (hs : s ∈ D.host.TT) :
    fill X b j (false, s) = (b s : ℝ) + X.off j (false, s) := by
  simp [fill, hs]

private lemma scale_w_double_prime_le_b_prime_div_x_of_one_le (s : Scale) (n : ℕ) (hn : 1 ≤ n) : s.w'' n ≤ s.b' / s.x := by
  have hx : 0 < s.x := by linarith [s.one_lt_alt]
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  unfold Scale.w''
  rw [← div_div]
  exact div_le_self (div_nonneg (sc_b'_pos s).le hx.le) hn'

private lemma scale_b_prime_div_x_le_b (s : Scale) : s.b' / s.x ≤ s.b := by
  have hx : 0 < s.x := by linarith [s.one_lt_alt]
  have hX : 1 ≤ s.X' := by
    unfold Scale.X'
    exact Real.one_le_exp (Real.rpow_nonneg hx.le _)
  have hX0 : s.X' ≠ 0 := (lt_of_lt_of_le one_pos hX).ne'
  have hb := scale_b_pos s
  have h : s.b' / s.x = s.b / s.X' := by
    unfold Scale.b' Scale.a
    field_simp <;> ring
  rw [h]
  exact div_le_self hb.le hX

theorem fill_ge (X : Inst D L) (b : HH D → ℤ) (hb : ∀ t ∈ D.host.TT, L.sc.b' ≤ (b t : ℝ)) (j : ℕ)
    (z : Bool × HH D) : L.sc.w'' D.R.n ≤ fill X b j z := by
  have hn := n_pos D
  have hI : X.off j z ≤ fill X b j z := by
    unfold fill
    split_ifs with h
    · have := hb z.2 h.2
      have := sc_b'_pos L.sc
      linarith
    · linarith
  have h1 := scale_w_double_prime_le_b_prime_div_x_of_one_le L.sc D.R.n hn
  have h2 := scale_b_prime_div_x_le_b L.sc
  by_cases ht : IsTopPl D z
  · have := (X.off_top j z ht).1
    linarith
  · by_cases hk : IsThickPl D z
    · have := (X.off_thick j z hk).1
      linarith
    · have := (X.off_thin j z ⟨ht, hk⟩).1
      linarith

theorem Sc_facts (P : ParameterChoice' D L) : 100 ≤ L.Sc ∧ 5 * L.Sc ≤ L.sc.w'' D.R.n := by
  have hk : (5 : ℝ) ≤ (D.R.k : ℝ) := by
    have h1 := D.R.m_add_three_le_k
    have h2 := D.R.two_le_m
    have h3 : 5 ≤ D.R.k := by omega
    exact_mod_cast h3
  have hm : (2 : ℝ) ≤ D.R.m := by exact_mod_cast D.R.two_le_m
  have hD := P.Del_ge.2.2.2
  have hN : D.R.k ≤ D.R.N D.R.m := by
    unfold Ranks.N
    exact Nat.le_add_right _ _
  have hNr : (D.R.k : ℝ) ≤ (D.R.N D.R.m : ℝ) := by exact_mod_cast hN
  have hm10 : (1024 : ℝ) ≤ (D.R.m : ℝ) ^ 10 := by
    calc (1024 : ℝ) = 2 ^ 10 := by norm_num
      _ ≤ (D.R.m : ℝ) ^ 10 := pow_le_pow_left₀ (by norm_num) hm 10
  have hprod : (5 : ℝ) * 1024 ≤ (D.R.N D.R.m : ℝ) * (D.R.m : ℝ) ^ 10 :=
    mul_le_mul (by linarith) hm10 (by norm_num) (by linarith)
  have hDel : (5120 : ℝ) ≤ (D.s.Del : ℝ) := by linarith
  have hkD := mul_le_mul hk hDel (by norm_num) (by linarith)
  have hSc := L.Sc_eq
  have hSc0 : 0 ≤ L.Sc := by
    rw [hSc]
    nlinarith
  constructor
  · rw [hSc]
    nlinarith
  · have h1 := P.kS_le
    nlinarith [mul_le_mul_of_nonneg_right hk hSc0]

theorem fillG_ge (P : ParameterChoice' D L) (X : Inst D L) (b : HH D → ℤ) (hb : ∀ t ∈ D.host.TT, L.sc.b' ≤ (b t : ℝ)) (j : ℕ)
    (hj : j ∈ SizeData₂.lifts D) (z : Bool × HH D) : L.sc.w'' D.R.n - L.Sc ≤ fillG X b j z := by
  have hf := fill_ge X b hb j z
  unfold SizeData₂.lifts at hj
  have hj' := Finset.mem_Icc.mp hj
  have hjm : (j : ℝ) ≤ D.R.m := by exact_mod_cast hj'.2
  have hj1 : (1 : ℝ) ≤ j := by exact_mod_cast hj'.1
  have ht0 : (0 : ℝ) ≤ D.R.t := Nat.cast_nonneg _
  have hk : (5 : ℝ) ≤ (D.R.k : ℝ) := by
    have h1 := D.R.m_add_three_le_k
    have h2 := D.R.two_le_m
    have h3 : 5 ≤ D.R.k := by omega
    exact_mod_cast h3
  have hm : (2 : ℝ) ≤ D.R.m := by exact_mod_cast D.R.two_le_m
  have hD := P.Del_ge.2.2.2
  have hNr : ((D.R.N D.R.m : ℕ) : ℝ) = D.R.k + D.R.m * (D.R.t + 1) := by
    unfold Ranks.N
    push_cast <;> ring
  have hm10 : (1 : ℝ) ≤ (D.R.m : ℝ) ^ 10 := one_le_pow₀ (by linarith)
  have hN0 : (0 : ℝ) ≤ (D.R.N D.R.m : ℝ) := Nat.cast_nonneg _
  have hNle : (D.R.N D.R.m : ℝ) ≤ D.s.Del := by
    nlinarith [mul_le_mul_of_nonneg_left hm10 hN0]
  have hDel0 : (0 : ℝ) ≤ D.s.Del := by linarith
  have hSc := L.Sc_eq
  have hka : kaJ D j ≤ L.Sc := by
    unfold kaJ
    rw [hSc]
    nlinarith [mul_le_mul_of_nonneg_right hjm (by linarith : (0 : ℝ) ≤ D.R.t + 1),
      mul_le_mul_of_nonneg_right hk hDel0]
  unfold fillG
  linarith

theorem summable_and_tsum_le_two_mul_div_of_le_div_pow (p y : ℝ) (hp : 2 ≤ p) (f : ℕ → ℝ) (h0 : ∀ e, 0 ≤ f e) (hz : f 0 = 0)
    (h1 : ∀ e, f e ≤ y / p ^ e) : Summable f ∧ ∑' e, f e ≤ 2 * y / p := by
  have hp0 : (0 : ℝ) < p := by linarith
  have hpne : p ≠ 0 := hp0.ne'
  have hy : 0 ≤ y := by
    have h := h1 0
    rw [pow_zero, div_one, hz] at h
    exact h
  have hr0 : (0 : ℝ) ≤ 1 / p := (one_div_pos.mpr hp0).le
  have hr1 : 1 / p < 1 := by
    rw [div_lt_one hp0]
    linarith
  have hgeo := summable_geometric_of_lt_one hr0 hr1
  have hfg : ∀ e, f e ≤ y * (1 / p) ^ e := fun e => by
    rw [one_div_pow, ← div_eq_mul_one_div]
    exact h1 e
  have hf : Summable f := Summable.of_nonneg_of_le h0 hfg (hgeo.mul_left y)
  refine ⟨hf, ?_⟩
  have hshift : Summable (fun e => f (e + 1)) := (summable_nat_add_iff 1).mpr hf
  rw [hf.tsum_eq_zero_add, hz, zero_add]
  have hle : ∀ e : ℕ, f (e + 1) ≤ y / p * (1 / p) ^ e := fun e => by
    have h := h1 (e + 1)
    calc f (e + 1) ≤ y / p ^ (e + 1) := h
      _ = y / p * (1 / p) ^ e := by
        rw [pow_succ, one_div_pow, div_mul_div_comm, mul_one, mul_comm (p ^ e) p]
  calc ∑' e, f (e + 1) ≤ ∑' e : ℕ, y / p * (1 / p) ^ e :=
        Summable.tsum_le_tsum hle hshift (hgeo.mul_left (y / p))
    _ = y / p * (1 - 1 / p)⁻¹ := by rw [tsum_mul_left, tsum_geometric_of_lt_one hr0 hr1]
    _ = y / (p - 1) := by
        rw [one_sub_div hpne, inv_div, div_mul_div_comm, mul_comm p (p - 1), mul_div_mul_right _ _ hpne]
    _ ≤ 2 * y / p := by
        have hp1' : (0 : ℝ) < p - 1 := by linarith
        rw [div_le_iff₀ hp1', div_mul_eq_mul_div, le_div_iff₀ hp0]
        nlinarith

def thW (D : D7) (s : Scale) : ℝ := 1 / ((D.R.k : ℝ) * s.x ^ (Scale.A / 2))

theorem k_ge (D : D7) : (5 : ℝ) ≤ (D.R.k : ℝ) := by
  have h1 := D.R.m_add_three_le_k
  have h2 := D.R.two_le_m
  have h3 : 5 ≤ D.R.k := by omega
  exact_mod_cast h3

theorem thW_bounds (D : D7) (s : Scale) : 0 < thW D s ∧ thW D s ≤ 1 / 5 := by
  have hk := k_ge D
  have hx : 1 ≤ s.x ^ (Scale.A / 2) :=
    Real.one_le_rpow s.one_lt_alt.le (by norm_num [Scale.A])
  have h5 : (5 : ℝ) ≤ (D.R.k : ℝ) * s.x ^ (Scale.A / 2) := by nlinarith
  have hpos : 0 < (D.R.k : ℝ) * s.x ^ (Scale.A / 2) := by linarith
  unfold thW
  exact ⟨one_div_pos.mpr hpos, one_div_le_one_div_of_le (by norm_num) h5⟩

theorem inWin_le {a b : HH D → ℤ} (h : InWin L a b) {t : HH D} (ht : t ∈ D.host.TT) :
    (a t : ℝ) ≤ L.sc.a * (1 + thW D L.sc) := by
  have h1 := (h t ht).2.1
  unfold thW
  calc (a t : ℝ) ≤ L.sc.a + L.sc.a / ((D.R.k : ℝ) * L.sc.x ^ (Scale.A / 2)) := h1
    _ = L.sc.a * (1 + 1 / ((D.R.k : ℝ) * L.sc.x ^ (Scale.A / 2))) := by ring

theorem ask_bounds (P : ParameterChoice' D L) (X : Inst D L) {a b : HH D → ℤ} (h : InWin L a b) (p : ℕ) (hp : p.Prime) (j : ℕ)
    (hj : j ∈ SizeData₂.lifts D) (s : HH D)
    (hs : s ∈ D.host.TT) : 0 ≤ askG X a b p j s ∧ askG X a b p j s ≤ 3 * L.sc.a / p := by
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  obtain ⟨hS100, hS5⟩ := Sc_facts P
  have hbT : ∀ t ∈ D.host.TT, L.sc.b' ≤ (b t : ℝ) := fun t ht => (h t ht).2.2
  have hfG : ∀ z, 0 ≤ fillG X b j z := fun z => by
    have := fillG_ge P X b hbT j hj z
    linarith
  have hapos := scale_a_pos' L.sc
  have has0 : 0 ≤ (a s : ℝ) := by linarith [(h s hs).1]
  have hn0 : ¬ Odd (0 : ℕ) := by
    rintro ⟨m, hm⟩
    omega
  have h0 : ∀ e : ℕ, 0 ≤ (if Odd e then max 0 ((a s : ℝ) / (p : ℝ) ^ e -
      fillG X b j (partner D p s e)) else 0) := by
    intro e
    split_ifs
    · exact le_max_left _ _
    · exact le_rfl
  have hz : (if Odd 0 then max 0 ((a s : ℝ) / (p : ℝ) ^ 0 -
      fillG X b j (partner D p s 0)) else 0) = 0 := if_neg hn0
  have h1 : ∀ e : ℕ, (if Odd e then max 0 ((a s : ℝ) / (p : ℝ) ^ e -
      fillG X b j (partner D p s e)) else 0) ≤ (a s : ℝ) / (p : ℝ) ^ e := by
    intro e
    split_ifs
    · exact max_le (div_nonneg has0 (by positivity)) (by linarith [hfG (partner D p s e)])
    · exact div_nonneg has0 (by positivity)
  obtain ⟨_, hle⟩ := summable_and_tsum_le_two_mul_div_of_le_div_pow (p : ℝ) (a s : ℝ) hp2 _ h0 hz h1
  have hθ := thW_bounds D L.sc
  have haw := inWin_le h hs
  refine ⟨tsum_nonneg h0, ?_⟩
  have h6 : 2 * (a s : ℝ) ≤ 3 * L.sc.a := by
    nlinarith [mul_le_mul_of_nonneg_left hθ.2 hapos.le]
  calc askG X a b p j s ≤ 2 * (a s : ℝ) / p := hle
    _ ≤ 3 * L.sc.a / p := by
      apply div_le_div_of_nonneg_right h6
      positivity

theorem X''_eq (s : Scale) (n : ℕ) (hn : 1 ≤ n) : s.w'' n * s.X'' n = s.a := by
  have hw := (sc_w''_pos s n hn).ne'
  unfold Scale.X''
  field_simp

def thS (L : SizeData₂ D) : ℝ := thW D L.sc + 3 * L.Sc / L.sc.w'' D.R.n

theorem thS_bounds (P : ParameterChoice' D L) : thW D L.sc ≤ thS L ∧ thS L ≤ 4 / 5 := by
  obtain ⟨h100, h5⟩ := Sc_facts P
  have hθ := thW_bounds D L.sc
  have hW : 0 < L.sc.w'' D.R.n := by linarith
  have hq0 : 0 ≤ 3 * L.Sc / L.sc.w'' D.R.n := div_nonneg (by linarith) hW.le
  have hq1 : 3 * L.Sc / L.sc.w'' D.R.n ≤ 3 / 5 := by
    rw [div_le_iff₀ hW]
    linarith
  unfold thS
  constructor <;> linarith [hθ.2]

theorem thS_key (P : ParameterChoice' D L) :
    L.sc.w'' D.R.n * (1 + thW D L.sc) ≤ (L.sc.w'' D.R.n - L.Sc) * (1 + thS L) := by
  obtain ⟨h100, h5⟩ := Sc_facts P
  have hθ := thW_bounds D L.sc
  have hW : 0 < L.sc.w'' D.R.n := by linarith
  have hSc : 0 ≤ L.Sc := by linarith
  have hq : 3 * L.Sc / L.sc.w'' D.R.n * L.sc.w'' D.R.n = 3 * L.Sc := div_mul_cancel₀ _ hW.ne'
  have hq1 : 3 * L.Sc / L.sc.w'' D.R.n ≤ 3 / 5 := by
    rw [div_le_iff₀ hW]
    linarith
  unfold thS
  nlinarith [mul_le_mul_of_nonneg_left hθ.2 hSc, mul_le_mul_of_nonneg_left hq1 hSc]

private lemma scale_b_le_a (s : Scale) : s.b ≤ s.a := by
  have hb := scale_b_pos s
  have h := mul_pos (sub_pos.mpr s.one_lt_alt) hb
  unfold Scale.a
  nlinarith

theorem ask_high (P : ParameterChoice' D L) (X : Inst D L) {a b : HH D → ℤ} (h : InWin L a b) (p : ℕ)
    (hpX : L.sc.X'' D.R.n < (p : ℝ)) (j : ℕ) (hj : j ∈ SizeData₂.lifts D) (s : HH D) (hs : s ∈ D.host.TT) :
    askG X a b p j s ≤
      if (p : ℝ) < L.sc.X'' D.R.n * (1 + thS L) then thW D L.sc * L.sc.w'' D.R.n + L.Sc else 0 := by
  obtain ⟨hS100, hS5⟩ := Sc_facts P
  have hn := n_pos D
  have hW : 0 < L.sc.w'' D.R.n := sc_w''_pos L.sc D.R.n hn
  have hθ := thW_bounds D L.sc
  have hkey := thS_key P
  have hapos := scale_a_pos' L.sc
  have hXa := X''_eq L.sc D.R.n hn
  have hX : 0 < L.sc.X'' D.R.n := by
    unfold Scale.X''
    exact div_pos hapos hW
  have hX1 : 1 ≤ L.sc.X'' D.R.n := by
    have h1 := scale_w_double_prime_le_b_prime_div_x_of_one_le L.sc D.R.n hn
    have h2 := scale_b_prime_div_x_le_b L.sc
    have h3 := scale_b_le_a L.sc
    unfold Scale.X''
    rw [le_div_iff₀ hW]
    linarith
  have hp : (0 : ℝ) < p := lt_trans hX hpX
  have hp2 : (2 : ℝ) ≤ p := by
    have h1 : (1 : ℝ) < p := lt_of_le_of_lt hX1 hpX
    have h2 : 1 < p := by exact_mod_cast h1
    have h3 : 2 ≤ p := by omega
    exact_mod_cast h3
  have hbT : ∀ t ∈ D.host.TT, L.sc.b' ≤ (b t : ℝ) := fun t ht => (h t ht).2.2
  have hfG : ∀ z, L.sc.w'' D.R.n - L.Sc ≤ fillG X b j z := fun z => fillG_ge P X b hbT j hj z
  have haw := inWin_le h hs
  have has0 : 0 ≤ (a s : ℝ) := by linarith [(h s hs).1]
  have hap0 : (a s : ℝ) ≤ L.sc.w'' D.R.n * (1 + thW D L.sc) * p := by
    have hc : 0 < L.sc.w'' D.R.n * (1 + thW D L.sc) := mul_pos hW (by linarith [hθ.1])
    have h1 := mul_lt_mul_of_pos_left hpX hc
    calc (a s : ℝ) ≤ L.sc.a * (1 + thW D L.sc) := haw
      _ = L.sc.w'' D.R.n * (1 + thW D L.sc) * L.sc.X'' D.R.n := by rw [← hXa]; ring
      _ ≤ L.sc.w'' D.R.n * (1 + thW D L.sc) * p := h1.le
  have hsingle : ∀ e : ℕ, e ≠ 1 → (if Odd e then max 0 ((a s : ℝ) / (p : ℝ) ^ e -
      fillG X b j (partner D p s e)) else 0) = 0 := by
    intro e he
    split_ifs with ho
    · refine le_antisymm ?_ (le_max_left _ _)
      apply max_le le_rfl
      have he3 : 3 ≤ e := by
        obtain ⟨m, hm⟩ := ho
        omega
      have hpe : (p : ℝ) ^ 3 ≤ (p : ℝ) ^ e := pow_le_pow_right₀ (by linarith) he3
      have hp3 : 4 * (p : ℝ) ≤ (p : ℝ) ^ 3 := by
        nlinarith [mul_nonneg (mul_nonneg hp.le (by linarith : (0 : ℝ) ≤ p - 2))
          (by linarith : (0 : ℝ) ≤ p + 2)]
      have hwp := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hθ.2 hW.le) hp.le
      have hle : (a s : ℝ) ≤ (L.sc.w'' D.R.n - L.Sc) * (p : ℝ) ^ e := by
        calc (a s : ℝ) ≤ L.sc.w'' D.R.n * (1 + thW D L.sc) * p := hap0
          _ ≤ (4 / 5 * L.sc.w'' D.R.n) * (4 * p) := by nlinarith [mul_pos hW hp]
          _ ≤ (L.sc.w'' D.R.n - L.Sc) * (p : ℝ) ^ e :=
            mul_le_mul (by linarith) (by linarith) (by positivity) (by linarith)
      have h2 : (a s : ℝ) / (p : ℝ) ^ e ≤ L.sc.w'' D.R.n - L.Sc := by
        rw [div_le_iff₀ (by positivity)]
        linarith
      linarith [hfG (partner D p s e)]
    · rfl
  unfold askG
  rw [tsum_eq_single 1 hsingle, if_pos odd_one, pow_one]
  split_ifs with hlt
  · apply max_le (add_nonneg (mul_nonneg hθ.1.le hW.le) (by linarith))
    have h2 : (a s : ℝ) / p ≤ L.sc.w'' D.R.n * (1 + thW D L.sc) := by
      rw [div_le_iff₀ hp]
      exact hap0
    linarith [hfG (partner D p s 1)]
  · push_neg at hlt
    apply max_le le_rfl
    have hθS := thS_bounds P
    have h1 : (a s : ℝ) ≤ (L.sc.w'' D.R.n - L.Sc) * p := by
      calc (a s : ℝ) ≤ L.sc.a * (1 + thW D L.sc) := haw
        _ = L.sc.X'' D.R.n * (L.sc.w'' D.R.n * (1 + thW D L.sc)) := by rw [← hXa]; ring
        _ ≤ L.sc.X'' D.R.n * ((L.sc.w'' D.R.n - L.Sc) * (1 + thS L)) :=
          mul_le_mul_of_nonneg_left hkey hX.le
        _ = (L.sc.w'' D.R.n - L.Sc) * (L.sc.X'' D.R.n * (1 + thS L)) := by ring
        _ ≤ (L.sc.w'' D.R.n - L.Sc) * p := mul_le_mul_of_nonneg_left hlt (by linarith)
    have h2 : (a s : ℝ) / p ≤ L.sc.w'' D.R.n - L.Sc := by
      rw [div_le_iff₀ hp]
      linarith
    linarith [hfG (partner D p s 1)]

end Formalism.MainNotions.AuxBlock8.Pf.G5

end
