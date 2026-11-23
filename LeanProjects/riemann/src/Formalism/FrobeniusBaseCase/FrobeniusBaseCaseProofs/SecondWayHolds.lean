import Formalism.FrobeniusBaseCase.FrobeniusBaseCaseProofs.ChainI
import Formalism.FrobeniusBaseCase.FrobeniusBaseCaseProofs.BaseCaseKOneHolds

open MvPowerSeries

namespace Formalism.BaseCaseIdentities

noncomputable section

open Classical

namespace Data

variable {k : Type*} [Field k] {Z C : Type*} [Fintype Z] [Fintype C] (D : Data k Z C)

def mu (J : ℕ) (c : C) : MvPowerSeries Z k := if D.lev c < J then D.m (D.lev c) c else 0

theorem inWTo_iff (J : ℕ) (t : C → MvPowerSeries Z k) :
    D.InWTo J t ↔ ∀ c, D.Wt D.top (t c - D.mu J c) := by
  constructor
  · intro h c
    unfold mu
    split_ifs with hc
    · exact h.1 c hc
    · rw [sub_zero]; exact h.2 c (not_lt.1 hc)
  · intro h
    refine ⟨fun c hc => ?_, fun c hc => ?_⟩
    · have := h c
      rwa [mu, if_pos hc] at this
    · have := h c
      rwa [mu, if_neg (not_lt.2 hc), sub_zero] at this

def main (J : ℕ) (c b : C) : MvPowerSeries Z k :=
  if D.lev c < J ∧ D.lev c + 1 < D.K then
    MvPowerSeries.C (-(D.l : k)⁻¹ * D.g c b) * frob D.q (D.m (D.lev c) c) else 0

theorem main_eq_zero (J : ℕ) (c b : C) (h : D.lev b ≠ D.lev c + 1) : D.main J c b = 0 := by
  unfold main
  split_ifs with h1
  · rw [D.g_supp c h1.2 b h, mul_zero, map_zero, zero_mul]
  · rfl

theorem mu_succ (J : ℕ) (hJ1 : 1 ≤ J) (hJK : J ≤ D.K) (b : C) :
    D.mu (min (J + 1) D.K) b = D.zvec b + ∑ c, D.main J c b := by
  have hK := D.K_pos
  by_cases hb0 : D.lev b = 0
  · have h1 : D.mu (min (J + 1) D.K) b = D.zvec b := by
      rw [mu, if_pos (by rw [hb0]; omega), hb0]
      rfl
    rw [h1, Finset.sum_eq_zero, add_zero]
    intro c _
    exact D.main_eq_zero J c b (by omega)
  · rw [D.zvec_eq_zero hb0, zero_add]
    by_cases hb : D.lev b < min (J + 1) D.K
    · obtain ⟨s, hs⟩ : ∃ s, D.lev b = s + 1 := ⟨D.lev b - 1, by omega⟩
      rw [mu, if_pos hb, hs, m_succ, Finset.mul_sum]
      refine Finset.sum_congr rfl fun c _ => ?_
      by_cases hc : D.lev c = s
      · rw [main, if_pos ⟨by omega, by omega⟩, hc, map_mul]
        ring
      · rw [D.m_eq_zero (by omega) hc, frob_zero D.q_pos, zero_mul, mul_zero,
          D.main_eq_zero J c b (by omega)]
    · rw [mu, if_neg hb]
      symm
      apply Finset.sum_eq_zero
      intro c _
      unfold main
      split_ifs with h
      · rw [D.g_supp c h.2 b (by omega), mul_zero, map_zero, zero_mul]
      · rfl

theorem rho_le_top : rho D.l ≤ D.top := by
  unfold top
  linarith

theorem v_al_two (c : C) (hg : D.good c) (b : C) : ((-1 : ℝ) : WithTop ℝ) ≤ D.v (D.al c 2 b) := by
  have h := D.al_good c hg 2 b (by norm_num)
  have h1 : (-(((2 : ℕ) : ℝ) - 1)) = (-1 : ℝ) := by norm_num
  rwa [h1] at h

theorem wt_two (J : ℕ) (hJK : J ≤ D.K) (c b : C) (hcJ : D.lev c < J) (τ : MvPowerSeries Z k)
    (hν : D.Wt D.top (τ - D.m (D.lev c) c)) :
    D.Wt D.top (MvPowerSeries.C (D.al c 2 b) * τ ^ (D.l ^ 2) + D.main J c b) := by
  have hl := D.l_ge
  have hcK : D.lev c < D.K := by omega
  have hgood := D.pure_good c hcK
  have hal := D.v_al_two c hgood b
  have hρ := rho_pos hl
  obtain ⟨μ, hμdef⟩ : ∃ μ, μ = D.m (D.lev c) c := ⟨_, rfl⟩
  obtain ⟨ν, hνdef⟩ : ∃ ν, ν = τ - μ := ⟨_, rfl⟩
  have hτ : τ = μ + ν := by rw [hνdef]; ring
  have hμ : D.Wt (rho D.l) μ := by rw [hμdef]; exact D.wt_m_rho _ _
  have hν' : D.Wt D.top ν := by rw [hνdef, hμdef]; exact hν
  have hdec : MvPowerSeries.C (D.al c 2 b) * τ ^ (D.l ^ 2) + D.main J c b =
      MvPowerSeries.C (D.al c 2 b) * (μ ^ (D.l ^ 2) - frob D.q μ)
      + MvPowerSeries.C (D.al c 2 b) * ((μ + ν) ^ (D.l ^ 2) - μ ^ (D.l ^ 2) - ν ^ (D.l ^ 2))
      + MvPowerSeries.C (D.al c 2 b) * ν ^ (D.l ^ 2)
      + (MvPowerSeries.C (D.al c 2 b) * frob D.q μ + D.main J c b) := by
    rw [hτ]; ring
  rw [hdec]
  have hqρ := D.q_rho
  refine HasWt.add (HasWt.add (HasWt.add ?_ ?_) ?_) ?_
  · have h1 : D.Wt (1 + qnum D.l * rho D.l) (μ ^ (D.l ^ 2) - frob D.q μ) := by
      rw [hμdef]; exact D.wt_m_pow_sub_frob hcK c
    refine HasWt.mono ?_ (HasWt.C_mul hal h1)
    unfold top
    linarith
  · have h1 := hasWt_add_pow_sub (e := 2) D.l_prime D.v_l D.rho_le_top hμ hν'
    refine HasWt.mono ?_ (HasWt.C_mul hal h1)
    have := rho_mul hl
    push_cast
    linarith
  · have h1 := HasWt.pow hν' (D.l ^ 2)
    refine HasWt.mono ?_ (HasWt.C_mul hal h1)
    have := num_good hl (j := 2) le_rfl
    unfold top
    push_cast at this ⊢
    linarith
  · by_cases hK1 : D.lev c + 1 < D.K
    · rw [main, if_pos ⟨hcJ, hK1⟩, ← hμdef, ← add_mul, ← map_add]
      have h1 : D.al c 2 b + -(D.l : k)⁻¹ * D.g c b = D.lam c b := by
        rw [D.al_two c hcK b]
        have := D.l_ne
        field_simp
        ring
      rw [h1]
      have h2 : ((0 : ℝ) : WithTop ℝ) ≤ D.v (D.lam c b) := by simpa using D.lam_int c b
      refine HasWt.mono ?_ (HasWt.C_mul h2 (HasWt.frob hμ D.q))
      rw [D.q_cast]
      unfold top
      linarith
    · rw [main, if_neg (fun h => hK1 h.2), add_zero]
      have h1 : D.Wt (rho D.l + qnum D.l ^ (D.lev c) * sg D.l D.i) μ := by
        rw [hμdef]; exact D.wt_m _ _
      refine HasWt.mono ?_ (HasWt.C_mul hal (HasWt.frob h1 D.q))
      rw [D.q_cast]
      have hlev : D.lev c + 1 = Kn D.i := by
        have : D.K = Kn D.i := rfl
        omega
      have h2 := identity_twenty_d D.l D.i (by omega) D.i_odd
      rw [← hlev, pow_succ'] at h2
      have := D.lR
      unfold top
      nlinarith

theorem wt_contrib (J : ℕ) (hJK : J ≤ D.K) (t : C → MvPowerSeries Z k)
    (ht : ∀ c, D.Wt D.top (t c - D.mu J c)) (N : ℕ) (hN : 2 ≤ N) (c b : C) :
    D.Wt D.top
      (∑ j ∈ Finset.Icc 1 N, MvPowerSeries.C (D.al c j b) * t c ^ (D.l ^ j) + D.main J c b) := by
  have hl := D.l_ge
  by_cases hcJ : D.lev c < J
  · have hcK : D.lev c < D.K := by omega
    have hgood := D.pure_good c hcK
    have hν : D.Wt D.top (t c - D.m (D.lev c) c) := by
      have := ht c
      rwa [mu, if_pos hcJ] at this
    have ht' : D.Wt (rho D.l) (t c) := by
      have h1 := HasWt.add (D.wt_m_rho (D.lev c) c) (HasWt.mono D.rho_le_top hν)
      rwa [add_sub_cancel] at h1
    have h2mem : 2 ∈ Finset.Icc 1 N := Finset.mem_Icc.2 ⟨by norm_num, hN⟩
    rw [← Finset.add_sum_erase _ _ h2mem, add_right_comm]
    refine HasWt.add (D.wt_two J hJK c b hcJ (t c) hν) ?_
    apply HasWt.sum
    intro j hj
    have hj' : j ≠ 2 ∧ 1 ≤ j ∧ j ≤ N := by
      simpa [Finset.mem_erase, Finset.mem_Icc] using hj
    by_cases hj1 : j = 1
    · subst hj1
      rw [D.al_one c hgood b, map_zero, zero_mul]
      exact HasWt.zero
    · have hj3 : 3 ≤ j := by omega
      refine HasWt.mono ?_ (HasWt.C_mul (D.al_good c hgood j b (by omega))
        (HasWt.pow ht' (D.l ^ j)))
      have := num_c hl hj3
      unfold top
      push_cast
      exact this
  · have ht' : D.Wt D.top (t c) := by
      have := ht c
      rwa [mu, if_neg hcJ, sub_zero] at this
    rw [main, if_neg (fun h => hcJ h.1), add_zero]
    apply HasWt.sum
    intro j hj
    have hj' : 1 ≤ j ∧ j ≤ N := by simpa [Finset.mem_Icc] using hj
    by_cases hg : D.good c
    · by_cases hj1 : j = 1
      · subst hj1
        rw [D.al_one c hg b, map_zero, zero_mul]
        exact HasWt.zero
      · refine HasWt.mono ?_ (HasWt.C_mul (D.al_good c hg j b (by omega))
          (HasWt.pow ht' (D.l ^ j)))
        have := num_good hl (j := j) (by omega)
        unfold top
        push_cast
        exact this
    · refine HasWt.mono ?_ (HasWt.C_mul (D.al_all c j b) (HasWt.pow ht' (D.l ^ j)))
      have := num_d hl (j := j) hj'.1
      unfold top
      push_cast
      exact this

theorem step (J : ℕ) (hJ1 : 1 ≤ J) (hJK : J ≤ D.K) (t : C → MvPowerSeries Z k)
    (hnc : NoConst t) (ht : D.InWTo J t) : D.InWTo (min (J + 1) D.K) (D.Psi t) := by
  rw [inWTo_iff] at ht ⊢
  intro b A
  have h1 : coeff A (D.Psi t b - D.mu (min (J + 1) D.K) b) =
      coeff A (D.PsiPartial (max A.degree 2) t b - D.mu (min (J + 1) D.K) b) := by
    rw [map_sub, map_sub, D.opIsLimit t hnc b A _ (le_max_left _ _)]
  rw [h1]
  have h2 : D.PsiPartial (max A.degree 2) t b - D.mu (min (J + 1) D.K) b =
      -∑ c, (∑ j ∈ Finset.Icc 1 (max A.degree 2),
        MvPowerSeries.C (D.al c j b) * t c ^ (D.l ^ j) + D.main J c b) := by
    rw [D.mu_succ J hJ1 hJK b, PsiPartial, Finset.sum_add_distrib]
    ring
  rw [h2]
  exact (HasWt.neg (HasWt.sum _ fun c _ =>
    D.wt_contrib J hJK t ht _ (le_max_right _ _) c b)) A

theorem start_in_W_holds : D.StartInW := by
  refine ⟨?_, ?_, ?_⟩
  · intro c
    unfold start
    split_ifs with h
    · exact D.ord_m h c
    · exact OrdGE.zero
  · intro c hc
    unfold start
    rw [if_pos hc, sub_self]
    exact HasWt.zero
  · intro c hc
    unfold start
    rw [if_neg (not_lt.2 hc)]
    exact HasWt.zero

theorem psi_in_W_holds : D.PsiW := by
  intro t hnc hW
  refine ⟨D.noConst_Psi t, ?_⟩
  have h := D.step D.K D.K_pos le_rfl t hnc hW
  rwa [min_eq_right (by omega)] at h

theorem chainII_holds : D.ChainII := by
  intro t hnc hfix
  have hit : ∀ n, NoConst ((D.Psi)^[n] D.start) ∧ D.InW ((D.Psi)^[n] D.start) := by
    intro n
    induction n with
    | zero => exact D.start_in_W_holds
    | succ n ih =>
      rw [Function.iterate_succ_apply']
      exact D.psi_in_W_holds _ ih.1 ih.2
  unfold InW
  rw [inWTo_iff]
  intro c A
  have h := (D.inWTo_iff _ _).1 (hit A.degree).2 c A
  have hc := D.hasUniqueFixedPoint.2 D.start t D.start_in_W_holds.1 hnc hfix A.degree A le_rfl c
  rw [map_sub] at h ⊢
  rw [← hc]
  exact h

theorem second_way_holds : D.SecondWay := by
  have h1 : D.InWTo 1 D.zvec := by
    refine ⟨?_, ?_⟩
    · intro c hc
      have : D.lev c = 0 := by omega
      rw [this]
      show D.Wt D.top (D.zvec c - D.zvec c)
      rw [sub_self]
      exact HasWt.zero
    · intro c hc
      rw [D.zvec_eq_zero (by omega)]
      exact HasWt.zero
  refine ⟨h1, fun J t hJ1 hJK hnc ht => D.step J hJ1 hJK t hnc ht, ?_⟩
  have hK := D.K_pos
  have hit : ∀ n, D.InWTo (min (n + 1) D.K) ((D.Psi)^[n] D.zvec) := by
    intro n
    induction n with
    | zero =>
      rw [min_eq_left (by omega)]
      exact h1
    | succ n ih =>
      rw [Function.iterate_succ_apply']
      have h2 := D.step _ (by omega) (min_le_right _ _) _ (D.noConst_iterate D.noConst_zvec n) ih
      have h3 : min (min (n + 1) D.K + 1) D.K = min (n + 1 + 1) D.K := by omega
      rwa [h3] at h2
  intro n hn
  have h2 := hit n
  rwa [min_eq_right (by omega)] at h2

end Data

end

end Formalism.BaseCaseIdentities
