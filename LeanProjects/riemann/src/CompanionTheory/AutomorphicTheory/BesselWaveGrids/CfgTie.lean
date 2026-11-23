import Formalism.HermitianCurvature.StatementSz
import CompanionTheory.AutomorphicTheory.BesselWaveGrids.NqMovedExample

namespace CompanionTheory.WaveGrid

open Formalism.FourierDecayAlt Finset

noncomputable def cfgPar (c : Sz.Cfg) (r : ℕ) (T T' : ℝ) (de de' : ℕ → ℝ) : M.Par := ⟨c.k, r, T, T', c.u de, c.u de'⟩

section cfg

variable (c : Sz.Cfg)

theorem cfg_v_step (i : ℕ) : c.v i = c.v (i + 1) + 4 * c.Del := by
  simp only [Sz.Cfg.v]
  push_cast
  ring

theorem cfg_v_mem (hok : c.Ok) (i : ℕ) (hi1 : 1 ≤ i) (hi : i + 1 ≤ c.k) : c.vlast ≤ c.v i ∧ c.v i ≤ c.v 1 := by
  have hD : (1:ℝ) ≤ c.Del := hok.hDel
  have h1 : (1:ℝ) ≤ i := by exact_mod_cast hi1
  have h2 : (i:ℝ) + 1 ≤ c.k := by exact_mod_cast hi
  simp only [Sz.Cfg.v, Nat.cast_one]
  constructor
  · nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ 4 * c.Del) (by linarith : (0:ℝ) ≤ (c.k:ℝ) - 1 - i)]
  · nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ 4 * c.Del) (by linarith : (0:ℝ) ≤ (i:ℝ) - 1)]

theorem cfg_v_last (hk : 1 ≤ c.k) : c.v (c.k - 1) = c.vlast := by
  simp only [Sz.Cfg.v, Nat.cast_sub hk, Nat.cast_one]
  ring

theorem cfg_b_pos (hok : c.Ok) : ∀ j : ℕ, 1 ≤ j → j ≤ c.m → 1 ≤ c.b j := by
  intro j hj
  induction j, hj using Nat.le_induction with
  | base => intro _; exact hok.hb1
  | succ n hn ih =>
    intro hnm
    have h1 := hok.hgap n hn (by omega)
    have h2 := ih (by omega)
    linarith

theorem cfg_inter (hok : c.Ok) (de : ℕ → ℝ) (hde : ∀ i, de i = 0 ∨ de i = 1) (s : ℕ) (hs1 : 1 ≤ s)
    (hsk : s ≤ c.k - 1) : c.lam s + 1 / 2 ≤ c.u de s ∧ c.u de (s + 1) ≤ c.lam s - 1 / 2 := by
  have hk4 : 4 ≤ c.k := hok.hk
  have hD : (1:ℝ) ≤ c.Del := hok.hDel
  have hk' : (4:ℝ) ≤ c.k := by exact_mod_cast hk4
  have hlam : c.lam s = c.v s := by
    rw [Sz.Cfg.lam, if_pos (by omega)]
  rw [hlam]
  constructor
  · rcases Nat.lt_or_ge s 2 with h | h
    · have hs : s = 1 := by omega
      subst hs
      rw [Sz.Cfg.u, if_pos rfl]
      have := hok.ha
      nlinarith [mul_nonneg (sub_nonneg.2 hk') (sub_nonneg.2 hD)]
    · rw [Sz.Cfg.u, if_neg (by omega), if_neg (by omega)]
      have hstep := cfg_v_step c (s - 1)
      rw [Nat.sub_add_cancel hs1] at hstep
      rcases hde (s - 1) with h0 | h0 <;> rw [h0] <;> linarith
  · rw [Sz.Cfg.u, if_neg (by omega)]
    by_cases hks : s + 1 = c.k
    · rw [if_pos hks, Sz.Cfg.ulast]
      have hv : c.v s = c.vlast := by
        have := cfg_v_last c (by omega : 1 ≤ c.k)
        rw [show s = c.k - 1 by omega]
        exact this
      rw [hv]
      split_ifs with ht
      · obtain ⟨h1, _⟩ := hok.htop ht
        have := hok.hb1
        have := hok.hv0
        linarith
      · linarith
    · rw [if_neg hks, Nat.add_sub_cancel]
      rcases hde s with h0 | h0 <;> rw [h0] <;> linarith

theorem cfg_u_le (hok : c.Ok) (de : ℕ → ℝ) (hde : ∀ i, de i = 0 ∨ de i = 1) (b : ℝ) (ha : c.a ≤ b)
    (hb1 : c.b 1 ≤ b) (i : ℕ) (hi1 : 1 ≤ i) (hik : i ≤ c.k) : |c.u de i| ≤ b := by
  have hk4 : 4 ≤ c.k := hok.hk
  have hD : (1:ℝ) ≤ c.Del := hok.hDel
  have hk' : (4:ℝ) ≤ c.k := by exact_mod_cast hk4
  have hprod : 16 * c.Del ≤ 4 * c.k * c.Del := by
    nlinarith [mul_nonneg (sub_nonneg.2 hk') (by linarith : (0:ℝ) ≤ c.Del)]
  have hv1 : c.vlast ≤ c.v 1 := (cfg_v_mem c hok 1 le_rfl (by omega)).1
  have hv0 := hok.hv0
  have hav := hok.ha
  have hb1 := hok.hb1
  rw [Sz.Cfg.u, abs_le]
  split_ifs with h1 h2
  · constructor <;> linarith
  · rw [Sz.Cfg.ulast]
    split_ifs with ht
    · obtain ⟨h3, h4⟩ := hok.htop ht
      constructor <;> linarith
    · constructor <;> linarith
  · have hm := cfg_v_mem c hok (i - 1) (by omega) (by omega)
    rcases hde (i - 1) with h0 | h0 <;> rw [h0] <;> constructor <;> linarith [hm.1, hm.2]

theorem lamData_cfg (r : ℕ) (hm : c.m = 2 * r + 2) (hok : c.Ok) (T T' : ℝ) (de de' : ℕ → ℝ)
    (hde : ∀ i, de i = 0 ∨ de i = 1) (hde' : ∀ i, de' i = 0 ∨ de' i = 1) (cs b : ℝ) (hc0 : 0 < cs)
    (hc : 1 + cs ≤ 4 * c.Del) (ha : c.a ≤ b) (hb : ∀ j, 1 ≤ j → j ≤ c.m → c.b j ≤ b) :
    LamData (cfgPar c r T T' de de') c.lam cs (4 * c.Del) b := by
  have hk4 : 4 ≤ c.k := hok.hk
  have hD : (1:ℝ) ≤ c.Del := hok.hDel
  have hk' : (4:ℝ) ≤ c.k := by exact_mod_cast hk4
  have hprod : 16 * c.Del ≤ 4 * c.k * c.Del := by
    nlinarith [mul_nonneg (sub_nonneg.2 hk') (by linarith : (0:ℝ) ≤ c.Del)]
  have hkD : (c.k:ℝ) ≤ 4 * c.k * c.Del := by
    nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ c.k) (sub_nonneg.2 hD)]
  have hv1 : c.vlast ≤ c.v 1 := (cfg_v_mem c hok 1 le_rfl (by omega)).1
  have hv0 := hok.hv0
  have hav := hok.ha
  have hbpos := cfg_b_pos c hok
  refine ⟨hc0, hc, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · linarith
  · show (c.k:ℝ) ≤ b
    linarith
  · linarith
  · intro s hs1 hs2
    change s ≤ c.k + 2 * r + 1 at hs2
    rw [Sz.Cfg.lam]
    split_ifs with hsk
    · have := cfg_v_mem c hok s hs1 (by omega)
      rw [abs_le]
      constructor <;> linarith [this.1, this.2]
    · have hj1 : 1 ≤ s + 1 - c.k := by omega
      have hj2 : s + 1 - c.k ≤ c.m := by omega
      have h1 := hbpos _ hj1 hj2
      have h2 := hb _ hj1 hj2
      rw [abs_neg, abs_of_pos (by linarith)]
      exact h2
  · intro s hs1 hs2
    change s + 1 ≤ c.k - 1 at hs2
    rw [Sz.Cfg.lam, Sz.Cfg.lam, if_pos (by omega), if_pos (by omega)]
    have := cfg_v_step c s
    linarith
  · intro s hs1 hs2
    exact ⟨cfg_inter c hok de hde s hs1 hs2, cfg_inter c hok de' hde' s hs1 hs2⟩
  · intro i hi1 hi2
    have hb1 := hb 1 le_rfl (by omega)
    exact ⟨cfg_u_le c hok de hde b ha hb1 i hi1 hi2, cfg_u_le c hok de' hde' b ha hb1 i hi1 hi2⟩

end cfg

noncomputable def cfg₀ : Sz.Cfg where
  k := 4
  m := 2
  Del := 15
  vlast := 0
  b := fun j => (j : ℝ) + 1
  a := 400
  top := false
  bp := 0

theorem cfg₀_ok : cfg₀.Ok where
  hk := by
    norm_num [cfg₀]
  hm := by norm_num [cfg₀]
  hDel := by norm_num [cfg₀]
  hv0 := by norm_num [cfg₀]
  hv1 := by norm_num [cfg₀, Sz.Cfg.v]
  hb1 := by norm_num [cfg₀]
  hgap := by
    intro j _ _
    simp only [cfg₀]
    push_cast
    linarith
  ha := by norm_num [cfg₀, Sz.Cfg.v]
  htop := by simp [cfg₀]

theorem lamData_cfg₀ :
    LamData (cfgPar cfg₀ 0 1 1 (fun _ => 0) (fun i => if i = 1 then 1 else 0)) cfg₀.lam 10 (4 * cfg₀.Del) 400 := by
  refine lamData_cfg cfg₀ 0 (by norm_num [cfg₀]) cfg₀_ok 1 1 _ _ (fun _ => Or.inl rfl) ?_ 10 400
    (by norm_num) (by norm_num [cfg₀]) (by norm_num [cfg₀]) ?_
  · intro i
    split_ifs <;> simp
  · intro j _ hj
    simp only [cfg₀] at hj ⊢
    have : (j:ℝ) ≤ 2 := by exact_mod_cast hj
    linarith

end CompanionTheory.WaveGrid
