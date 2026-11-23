import Formalism.SharpRestriction.GrowthBounds.LogarithmicSums.PartnerCountOfCentral

noncomputable section

open scoped BigOperators
open NumberField Formalism.FrobeniusOrbits Formalism.BasicNotions Formalism.MainNotions.G Filter

namespace Formalism.MainNotions.AuxBlock8.Pf.St

theorem ev_log (c α : ℝ) (hα : 0 < α) : ∀ᶠ x : ℝ in atTop, c * Real.log x ≤ x ^ α := by
  have hε : (0 : ℝ) < 1 / (|c| + 1) := by positivity
  have h := (isLittleO_log_rpow_atTop hα).def hε
  filter_upwards [h, eventually_gt_atTop 0] with x hx hx0
  have hxa : 0 < x ^ α := Real.rpow_pos_of_pos hx0 α
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hxa] at hx
  have hc : |c| * (1 / (|c| + 1)) ≤ 1 := by
    rw [mul_one_div, div_le_one (by positivity)]
    linarith
  calc c * Real.log x ≤ |c| * |Real.log x| := by rw [← abs_mul]; exact le_abs_self _
    _ ≤ |c| * (1 / (|c| + 1) * x ^ α) := by gcongr
    _ = (|c| * (1 / (|c| + 1))) * x ^ α := by ring
    _ ≤ 1 * x ^ α := by gcongr
    _ = x ^ α := one_mul _

theorem ev_pow (c α β : ℝ) (h : α < β) : ∀ᶠ x : ℝ in atTop, c * x ^ α ≤ x ^ β := by
  have ht := tendsto_rpow_atTop (sub_pos.2 h)
  filter_upwards [ht.eventually_ge_atTop c, eventually_gt_atTop 0] with x hx hx0
  have hsplit : x ^ β = x ^ α * x ^ (β - α) := by
    rw [← Real.rpow_add hx0]
    ring_nf
  rw [hsplit, mul_comm c]
  exact mul_le_mul_of_nonneg_left hx (Real.rpow_pos_of_pos hx0 α).le

def rE (eps : ℝ) : ℕ := ⌈8 * (2 + 8 * eps + 2) / eps⌉₊ + 1

theorem rG_rE (s : Scale) : rG s = rE s.eps := rfl

def cGE (eps : ℝ) : ℝ := (((2 + 8 * eps + 3) * 10 ^ (6 * rE eps + 1) + 1) + 5) * (6 * (rE eps : ℝ) + 1) * 2

def cNE (eps : ℝ) : ℝ := 18 * cGE eps + 2 * (2 + 8 * eps + 3) + 2

theorem cGE_nonneg (eps : ℝ) (he : 0 < eps) : 0 ≤ cGE eps := by
  unfold cGE
  have h1 : 0 ≤ 2 + 8 * eps + 3 := by linarith
  have h2 : (0 : ℝ) ≤ 10 ^ (6 * rE eps + 1) := by positivity
  have h3 : (0 : ℝ) ≤ 6 * (rE eps : ℝ) + 1 := by positivity
  have h4 := mul_nonneg h1 h2
  exact mul_nonneg (mul_nonneg (by linarith) h3) (by norm_num)

theorem inv_delta1 (s : Scale) : 1 / s.delta1 = s.x ^ (s.eps / 8) := by
  unfold Scale.delta1
  rw [Real.rpow_neg (le_of_lt (zero_lt_one.trans s.one_lt_alt)), one_div, inv_inv]

theorem one_le_xpow (s : Scale) (y : ℝ) (hy : 0 ≤ y) : 1 ≤ s.x ^ y :=
  Real.one_le_rpow s.one_lt_alt.le hy

theorem Gp_le (s : Scale) (hx : Real.exp 1 ≤ s.x) :
    (Gp s : ℝ) ≤ cGE s.eps * Real.log s.x * s.x ^ (s.eps / 8) := by
  have he := s.eps_pos
  have hL : 1 ≤ Real.log s.x := by
    rw [← Real.log_exp 1]
    exact Real.log_le_log (Real.exp_pos 1) hx
  have hy : 1 ≤ s.x ^ (s.eps / 8) := one_le_xpow s _ (by linarith)
  set r := rG s with hr
  set A : ℝ := (2 + 8 * s.eps + 3) * 10 ^ (6 * r + 1) with hA
  have hA0 : 0 ≤ A := mul_nonneg (by linarith) (by positivity)
  have hM : (orbitSmallMultiplicity r (hG s) s.x : ℝ) ≤ A * Real.log s.x + 1 := by
    unfold orbitSmallMultiplicity
    have harg : (hG s + 3) * Real.log s.x / (10 : ℝ) ^ (-((6 * r + 1 : ℕ) : ℤ)) =
        A * Real.log s.x := by
      rw [zpow_neg, zpow_natCast, div_inv_eq_mul, hA, hG]
      ring
    rw [harg]
    exact (Nat.ceil_lt_add_one (mul_nonneg hA0 (by linarith))).le
  have hE : (goodEll r s.delta1 : ℝ) ≤ (6 * (r : ℝ) + 1) * (2 * s.x ^ (s.eps / 8)) := by
    unfold goodEll goodU
    push_cast
    rw [inv_delta1]
    have hc := (Nat.ceil_lt_add_one (by linarith : (0 : ℝ) ≤ s.x ^ (s.eps / 8))).le
    have h6 : (0 : ℝ) ≤ 6 * (r : ℝ) + 1 := by positivity
    exact mul_le_mul_of_nonneg_left (by linarith) h6
  have hc : cGE s.eps = (A + 1 + 5) * (6 * (r : ℝ) + 1) * 2 := rfl
  unfold Gp goodG'
  push_cast
  have h1 : A * Real.log s.x + 1 + 5 ≤ (A + 1 + 5) * Real.log s.x := by nlinarith
  have h2 : 0 ≤ (6 * (r : ℝ) + 1) * (2 * s.x ^ (s.eps / 8)) := by positivity
  calc ((orbitSmallMultiplicity r (hG s) s.x : ℝ) + 5) * (goodEll r s.delta1 : ℝ)
      ≤ (A * Real.log s.x + 1 + 5) * ((6 * (r : ℝ) + 1) * (2 * s.x ^ (s.eps / 8))) := by
        gcongr
    _ ≤ ((A + 1 + 5) * Real.log s.x) * ((6 * (r : ℝ) + 1) * (2 * s.x ^ (s.eps / 8))) :=
        mul_le_mul_of_nonneg_right h1 h2
    _ = cGE s.eps * Real.log s.x * s.x ^ (s.eps / 8) := by rw [hc]; ring

theorem first_count_le_log (s : Scale) (hx : Real.exp 1 ≤ s.x) : (N1 s : ℝ) ≤ cNE s.eps * Real.log s.x := by
  have he := s.eps_pos
  have hx0 : 0 < s.x := lt_of_lt_of_le (Real.exp_pos 1) hx
  have hL : 1 ≤ Real.log s.x := by
    rw [← Real.log_exp 1]
    exact Real.log_le_log (Real.exp_pos 1) hx
  have hcg := cGE_nonneg s.eps he
  have hd0 : 0 < s.delta1 := by unfold Scale.delta1; exact Real.rpow_pos_of_pos hx0 _
  have hyd : s.x ^ (s.eps / 8) * s.delta1 = 1 := by
    rw [← inv_delta1, one_div, inv_mul_cancel₀ hd0.ne']
  have hGp := Gp_le s hx
  unfold Gp at hGp
  have hG1 : 6 * Real.exp 1 * (goodG' (rG s) s.delta1 (hG s) s.x : ℝ) * s.delta1 ≤
      18 * cGE s.eps * Real.log s.x := by
    have he3 : Real.exp 1 < 3 := lt_trans Real.exp_one_lt_d9 (by norm_num)
    have hstep : (goodG' (rG s) s.delta1 (hG s) s.x : ℝ) * s.delta1 ≤ cGE s.eps * Real.log s.x := by
      calc (goodG' (rG s) s.delta1 (hG s) s.x : ℝ) * s.delta1
          ≤ cGE s.eps * Real.log s.x * s.x ^ (s.eps / 8) * s.delta1 :=
            mul_le_mul_of_nonneg_right hGp hd0.le
        _ = cGE s.eps * Real.log s.x := by rw [mul_assoc _ (s.x ^ _), hyd, mul_one]
    have hcl : 0 ≤ cGE s.eps * Real.log s.x := mul_nonneg hcg (by linarith)
    nlinarith [Real.exp_pos 1]
  have hlog2 : 1 / 2 < Real.log 2 := lt_trans (by norm_num) Real.log_two_gt_d9
  have hG2 : (hG s + 3) * Real.logb 2 s.x ≤ 2 * (2 + 8 * s.eps + 3) * Real.log s.x := by
    unfold Real.logb hG
    have hl2 : 0 < Real.log 2 := by linarith
    rw [mul_div_assoc', div_le_iff₀ hl2]
    have hX : 0 < (2 + 8 * s.eps + 3) * Real.log s.x := mul_pos (by linarith) (by linarith)
    nlinarith [mul_pos hX (sub_pos.2 hlog2)]
  have hmax : max (6 * Real.exp 1 * (goodG' (rG s) s.delta1 (hG s) s.x : ℝ) * s.delta1)
      ((hG s + 3) * Real.logb 2 s.x) ≤ (18 * cGE s.eps + 2 * (2 + 8 * s.eps + 3)) * Real.log s.x := by
    refine max_le ?_ ?_
    · nlinarith
    · nlinarith
  have hnn : 0 ≤ max (6 * Real.exp 1 * (goodG' (rG s) s.delta1 (hG s) s.x : ℝ) * s.delta1)
      ((hG s + 3) * Real.logb 2 s.x) := le_max_of_le_left (by positivity)
  unfold N1 orbitWindowCount
  push_cast
  have hceil := (Nat.ceil_lt_add_one hnn).le
  unfold cNE
  nlinarith

theorem k_le_x_pow_six {D : D7} (L : SizeData₂ D) (hS : Formalism.MainNotions.SizesAt L) : (D.R.k : ℝ) ≤ L.sc.x ^ (6 : ℝ) := by
  have hk := hS.2.2.1.2
  have he := L.sc.eps_lt
  have he0 := L.sc.eps_pos
  refine hk.trans (Real.rpow_le_rpow_of_exponent_le L.sc.one_lt_alt.le ?_)
  unfold Formalism.MainNotions.szTh
  linarith

theorem one_le_k (D : D7) : (1 : ℝ) ≤ (D.R.k : ℝ) := by
  have h := D.R.m_add_three_le_k
  exact_mod_cast (by omega : 1 ≤ D.R.k)

theorem xpow_le_exp (x N y : ℝ) (hx : 0 < x) (h : N * Real.log x ≤ y) : x ^ N ≤ Real.exp y := by
  rw [Real.rpow_def_of_pos hx]
  exact Real.exp_le_exp.2 (by rw [mul_comm]; exact h)

theorem second_level_lt_good_of_log {D : D7} (L : SizeData₂ D) (hS : Formalism.MainNotions.SizesAt L) (hx : Real.exp 1 ≤ L.sc.x)
    (h : 514 * Real.log L.sc.x ≤ L.sc.x ^ (L.sc.eps / 8)) : L2 D L.sc < goodU L.sc.delta1 := by
  have hx0 : 0 < L.sc.x := lt_trans zero_lt_one L.sc.one_lt_alt
  have hL : 1 ≤ Real.log L.sc.x := by
    rw [← Real.log_exp 1]
    exact Real.log_le_log (Real.exp_pos 1) hx
  have hk1 := one_le_k D
  have hk6 := k_le_x_pow_six L hS
  have hlogk : Real.log (D.R.k : ℝ) ≤ 6 * Real.log L.sc.x := by
    calc Real.log (D.R.k : ℝ) ≤ Real.log (L.sc.x ^ (6 : ℝ)) := Real.log_le_log (by linarith) hk6
      _ = 6 * Real.log L.sc.x := by rw [Real.log_rpow hx0]
  have hlog2 := Real.log_two_gt_d9
  have hL1 : ∀ p : ℕ, p.Prime → L1 D L.sc p ≤ ⌈186 * Real.log L.sc.x⌉₊ := by
    intro p hp
    unfold L1
    apply Nat.ceil_mono
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
    have hlp : Real.log 2 ≤ Real.log p := Real.log_le_log (by norm_num) hp2
    have hlp0 : 0 < Real.log p := by linarith
    have hk0 : (D.R.k : ℝ) ≠ 0 := ne_of_gt (by linarith)
    have hxA : L.sc.x ^ Scale.A ≠ 0 := (Real.rpow_pos_of_pos hx0 _).ne'
    have hy : Real.log (((D.R.k : ℝ) * L.sc.x ^ Scale.A) ^ 4) =
        4 * (Real.log D.R.k + Scale.A * Real.log L.sc.x) := by
      rw [Real.log_pow, Real.log_mul hk0 hxA, Real.log_rpow hx0]
      push_cast
      ring
    have hy0 : 0 ≤ Real.log (D.R.k : ℝ) := Real.log_nonneg hk1
    have hA : Scale.A = 26 := rfl
    unfold Real.logb
    rw [hy, div_le_iff₀ hlp0, hA]
    have hLn : (0 : ℝ) ≤ 186 * Real.log L.sc.x := by linarith
    nlinarith [mul_le_mul_of_nonneg_left hlp hLn, mul_le_mul_of_nonneg_left hlog2.le hLn]
  have hSup : sSup {l | ∃ p : ℕ, p.Prime ∧ D.host.cls p = PrimeClass.inertClass ∧ l = L1 D L.sc p} ≤
      ⌈186 * Real.log L.sc.x⌉₊ := by
    apply csSup_le'
    rintro l ⟨p, hp, -, rfl⟩
    exact hL1 p hp
  have hL2 : L2 D L.sc ≤ 2 * ⌈186 * Real.log L.sc.x⌉₊ := by
    unfold L2
    exact Nat.mul_le_mul_left 2 hSup
  have hL2r : (L2 D L.sc : ℝ) ≤ 2 * (⌈186 * Real.log L.sc.x⌉₊ : ℝ) := by exact_mod_cast hL2
  have hceil := Nat.ceil_lt_add_one (by linarith : (0 : ℝ) ≤ 186 * Real.log L.sc.x)
  have hU : L.sc.x ^ (L.sc.eps / 8) ≤ (goodU L.sc.delta1 : ℝ) := by
    unfold goodU
    rw [inv_delta1]
    exact Nat.le_ceil _
  have hlt : (L2 D L.sc : ℝ) < goodU L.sc.delta1 := by linarith
  exact_mod_cast hlt

def CStar (eps : ℝ) (K : Consts) (C31 : ℝ) : ℝ :=
  3 + K.tII * (rE eps : ℝ) + (2 * (3 : ℝ) + 4 * K.tII + 160 * C31 + 7) + K.Pr1 * C31 + K.kappaThresholdOne * |cNE eps|

theorem CStar_nonneg (eps : ℝ) (K : Consts) (hK : K.Nonneg) (C31 : ℝ) (hC31 : 0 < C31) : 0 ≤ CStar eps K C31 := by
  obtain ⟨-, -, -, htII, -, -, -, -, htI1, -, -, -, -, hPr1, -⟩ := hK
  unfold CStar
  have a := mul_nonneg htII (Nat.cast_nonneg (α := ℝ) (rE eps))
  have b := mul_nonneg hPr1 hC31.le
  have c := mul_nonneg htI1 (abs_nonneg (cNE eps))
  linarith

def SmallB (D : D7) (L : SizeData₂ D) (K : Consts) (C31 bo : ℝ) : Prop :=
  (∀ p : ℕ, p.Prime → (p : ℝ) < L.sc.p0 D.R.k → (D.R.k : ℝ) * Qp L.sc p ≤ L.sc.b') ∧
  (∀ p : ℕ, p.Prime →
    K.DII * ((N1 L.sc : ℝ) ^ 3 + (rG L.sc : ℝ) ^ 5 + (D.R.k : ℝ) ^ 2) * Real.logb p L.sc.a ≤ L.sc.b') ∧
  (∀ p : ℕ, p.Prime → L.sc.p0 D.R.k ≤ (p : ℝ) → (p : ℝ) < L.sc.X' → ∀ n' : ℕ, n' ≤ D.R.n →
    K.Pr1 * (C31 * Real.log L.sc.x / L.sc.delta1) * (L.etaSz + cG L + Nm D) +
      K.kappaThresholdTwo * (Qp L.sc p * c6f K L p n' +
        (D.R.k : ℝ) * Qp L.sc p + (D.R.k : ℝ) * Real.logb p L.sc.a + cG L) +
      2 * (C31 * Real.log L.sc.x / L.sc.delta1) * cG L +
      40 * C31 * Real.log L.sc.x * (K.DI * (L.sc.x ^ (Scale.A / 2)) ^ 2 *
        ((N1 L.sc : ℝ) ^ 5 + (D.R.k : ℝ) ^ 3) * Real.logb p L.sc.a) + 3 ≤ bo)

theorem numStar_ev (eps : ℝ) (K : Consts) (hK : K.Nonneg) (C31 : ℝ) (hC31 : 0 < C31) :
    ∀ᶠ x : ℝ in atTop, ∀ (D : D7) (L : SizeData₂ D), L.sc.x = x → L.sc.eps = eps → Formalism.MainNotions.SizesAt L →
      ParameterChoice' D L → ∀ bo : ℝ, SmallB D L K C31 bo → ∀ C : ℝ, CStar eps K C31 ≤ C → NumStar D L K C31 C bo := by
  by_cases heps : 0 < eps ∧ eps < 1 / 52
  swap
  · exact Filter.Eventually.of_forall fun x D L _ hLe =>
      absurd ⟨hLe ▸ L.sc.eps_pos, hLe ▸ L.sc.eps_lt⟩ heps
  obtain ⟨he0, he1⟩ := heps
  have E1 : ∀ᶠ x : ℝ in atTop, Real.exp 1 ≤ x := eventually_ge_atTop _
  have E2 := ev_log 514 (eps / 8) (by linarith)
  have E3 := ev_log (3 * cGE eps) (eps / 8) (by linarith)
  have E4 := ev_log (4 * C31) (1 - eps / 8) (by linarith)
  have E5 : ∀ᶠ x : ℝ in atTop, (2 : ℝ) ≤ x := eventually_ge_atTop _
  filter_upwards [E1, E2, E3, E4, E5] with x h1 h2 h3 h4 h5
  intro D L hx hLe hS P bo hSB C hC
  subst hx
  subst hLe
  have hx0 : 0 < L.sc.x := sc_x_pos L.sc
  have hL : 1 ≤ Real.log L.sc.x := by
    rw [← Real.log_exp 1]
    exact Real.log_le_log (Real.exp_pos 1) h1
  have hy0 : 0 ≤ L.sc.x ^ (L.sc.eps / 8) := (Real.rpow_pos_of_pos hx0 _).le
  have hGp := Gp_le L.sc h1
  have hN1 := first_count_le_log L.sc h1
  obtain ⟨-, -, -, htII, -, -, -, -, htI1, -, -, -, -, hPr1, -⟩ := hK
  have hCS : CStar L.sc.eps K C31 ≤ C := hC
  unfold CStar at hCS
  have ha := mul_nonneg htII (Nat.cast_nonneg (α := ℝ) (rE L.sc.eps))
  have hb := mul_nonneg hPr1 hC31.le
  have hc := mul_nonneg htI1 (abs_nonneg (cNE L.sc.eps))
  obtain ⟨hw500, hcGw, hwb, hcG0, hScG⟩ := base P
  obtain ⟨-, hNmSc, -⟩ := Nm_le_Sc P
  have hn1 : 1 ≤ D.R.n := by
    have hexp : 0 ≤ 2 + 8 * L.sc.eps - Formalism.MainNotions.szTh L := by
      unfold Formalism.MainNotions.szTh
      linarith
    have h1n : (1 : ℝ) ≤ D.R.n := le_trans (Real.one_le_rpow L.sc.one_lt_alt.le hexp) hS.1.1
    exact_mod_cast h1n
  obtain ⟨hwx, -⟩ := w''_le L.sc D.R.n hn1
  have hb0 : 0 ≤ L.sc.b' := by linarith
  have hbx : L.sc.b' / L.sc.x ≤ L.sc.b' / 2 := div_le_div_of_nonneg_left hb0 (by norm_num) h5
  have hEta := hS.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have ht1 : (1 : ℝ) ≤ D.R.t := by exact_mod_cast D.R.t_odd.pos
  have heta0 : 0 ≤ L.etaSz := by linarith [hEta.1]
  have heta : L.etaSz ≤ L.sc.w'' D.R.n := by
    have h4e := hEta.2.2.2.1
    have hwx' : L.sc.w'' D.R.n / L.sc.x ≤ L.sc.w'' D.R.n :=
      div_le_self (by linarith) L.sc.one_lt_alt.le
    nlinarith
  have hNm : Nm D ≤ L.sc.w'' D.R.n := by
    unfold Nm
    linarith
  have hS4 : L.sc.w'' D.R.n + L.etaSz + cG L + Nm D ≤ 4 * (L.sc.b' / L.sc.x) := by linarith
  have hkey : 4 * C31 * Real.log L.sc.x * L.sc.x ^ (L.sc.eps / 8) ≤ L.sc.x := by
    calc 4 * C31 * Real.log L.sc.x * L.sc.x ^ (L.sc.eps / 8)
        ≤ L.sc.x ^ (1 - L.sc.eps / 8) * L.sc.x ^ (L.sc.eps / 8) :=
          mul_le_mul_of_nonneg_right h4 hy0
      _ = L.sc.x := by rw [← Real.rpow_add hx0]; simp
  have hinv := inv_delta1 L.sc
  have hrG : (rG L.sc : ℝ) = (rE L.sc.eps : ℝ) := rfl
  exact
    { hL2 := second_level_lt_good_of_log L hS h1 h2
      h3G := by
        push_cast
        calc (3 : ℝ) * (Gp L.sc : ℝ) ≤ 3 * (cGE L.sc.eps * Real.log L.sc.x * L.sc.x ^ (L.sc.eps / 8)) := by
              linarith
          _ = (3 * cGE L.sc.eps * Real.log L.sc.x) * L.sc.x ^ (L.sc.eps / 8) := by ring
          _ ≤ L.sc.x ^ (L.sc.eps / 8) * L.sc.x ^ (L.sc.eps / 8) := mul_le_mul_of_nonneg_right h3 hy0
          _ = L.sc.x ^ (L.sc.eps / 4) := by rw [← Real.rpow_add hx0]; ring_nf
      hlx := hL
      hGu := by
        have hpos : 0 ≤ C31 * Real.log L.sc.x * L.sc.x ^ (L.sc.eps / 8) :=
          mul_nonneg (mul_nonneg hC31.le (by linarith)) hy0
        calc C31 * Real.log L.sc.x / L.sc.delta1 * (L.sc.w'' D.R.n + L.etaSz + cG L + Nm D)
            = (C31 * Real.log L.sc.x * (1 / L.sc.delta1)) *
                (L.sc.w'' D.R.n + L.etaSz + cG L + Nm D) := by ring
          _ = (C31 * Real.log L.sc.x * L.sc.x ^ (L.sc.eps / 8)) *
                (L.sc.w'' D.R.n + L.etaSz + cG L + Nm D) := by rw [hinv]
          _ ≤ (C31 * Real.log L.sc.x * L.sc.x ^ (L.sc.eps / 8)) * (4 * (L.sc.b' / L.sc.x)) :=
              mul_le_mul_of_nonneg_left hS4 hpos
          _ = (4 * C31 * Real.log L.sc.x * L.sc.x ^ (L.sc.eps / 8)) * L.sc.b' / L.sc.x := by ring
          _ ≤ L.sc.x * L.sc.b' / L.sc.x := by gcongr
          _ = L.sc.b' := by field_simp
      hc0 := by
        unfold c0num
        linarith
      hkQ := hSB.1
      hDII := hSB.2.1
      hC3 := by linarith
      hCt := by rw [hrG]; linarith
      hCD := by linarith
      hCP := by linarith
      hN1 := by
        have hN1' : (N1 L.sc : ℝ) ≤ |cNE L.sc.eps| * Real.log L.sc.x :=
          hN1.trans (mul_le_mul_of_nonneg_right (le_abs_self _) (by linarith))
        calc K.kappaThresholdOne * (N1 L.sc : ℝ) ≤ K.kappaThresholdOne * (|cNE L.sc.eps| * Real.log L.sc.x) :=
              mul_le_mul_of_nonneg_left hN1' htI1
          _ = (K.kappaThresholdOne * |cNE L.sc.eps|) * Real.log L.sc.x := by ring
          _ ≤ C * Real.log L.sc.x := mul_le_mul_of_nonneg_right (by linarith) (by linarith)
      hbo := hSB.2.2 }

end Formalism.MainNotions.AuxBlock8.Pf.St

end
