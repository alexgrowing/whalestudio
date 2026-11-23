import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.DepthNumbersThresholdEq
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.OddLevelBlockBoundAttainedStatement
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.CharacterBlocksAttainBound
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.MonomialBlockSupplyBothTypingsStatement

open Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds Formalism.UnitaryBoundIntegral
open scoped BigOperators

namespace GlobalTheory.GoodDepth.ConjPkg

theorem exists_good (l S W : ℕ) (G : Set ℕ) (h : RF.Windows S G) :
    ∃ y u : ℕ, W = (l + 1) * y + u ∧ y ∈ G ∧ u ≤ (l + 1) * S := by
  have hd := Nat.div_add_mod W (l + 1)
  have hm := Nat.mod_lt W (Nat.succ_pos l)
  set q := W / (l + 1)
  set r := W % (l + 1)
  by_cases hq : q + 1 ≤ S
  · refine ⟨0, W, by simp, h.1, ?_⟩
    have : (l + 1) * (q + 1) ≤ (l + 1) * S := Nat.mul_le_mul_left _ hq
    rw [Nat.mul_add] at this
    omega
  · obtain ⟨y, hy, h1, h2⟩ := h.2 (q + 1 - S)
    obtain ⟨c, hc⟩ : ∃ c, q = y + c := ⟨q - y, by omega⟩
    refine ⟨y, (l + 1) * c + r, ?_, hy, ?_⟩
    · rw [← hd, hc]; ring
    · have : (l + 1) * (c + 1) ≤ (l + 1) * S := Nat.mul_le_mul_left _ (by omega)
      rw [Nat.mul_add] at this
      omega

theorem one_le_log (x : ℝ) (hx : 4 ≤ x) : 1 ≤ Real.log x := by
  rw [Real.le_log_iff_exp_le (by linarith)]
  have := Real.exp_one_lt_d9
  linarith

theorem logb_le_log (l : ℕ) (hl : 5 ≤ l) (x : ℝ) (hx : 1 ≤ x) : Real.logb l x ≤ Real.log x := by
  have h1 : 1 ≤ Real.log l := one_le_log _ (by exact_mod_cast (by omega : 4 ≤ l))
  have h2 : 0 ≤ Real.log x := Real.log_nonneg hx
  unfold Real.logb
  exact div_le_self h2 h1

theorem place_bound (l n m S y u : ℕ) (hl : 5 ≤ l) (hn : 1 ≤ n) (hu : u ≤ (l + 1) * S) :
    RF.blockBd l n m 1 y + RF.chBd l n m u ≤
      Formalism.IncomingBounds.rho l * n * (((l + 1) * y + u : ℕ) : ℝ) + 4 * m * (((l + 1) * y + u : ℕ) : ℝ) / l +
        (n * (Real.logb l n + 1) + 2 * n * S) := by
  have hl' : (5 : ℝ) ≤ l := by exact_mod_cast hl
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hu' : (u : ℝ) ≤ (l + 1) * S := by exact_mod_cast hu
  have hlog : 0 ≤ Real.logb l n := Real.logb_nonneg (by linarith) hn'
  have h1 : (0 : ℝ) < (l : ℝ) - 1 := by linarith
  have h2 : (0 : ℝ) < (l : ℝ) + 1 := by linarith
  have h3 : (l : ℝ) ^ 2 - 1 = ((l : ℝ) - 1) * (l + 1) := by ring
  have hy0 : (0 : ℝ) ≤ y := Nat.cast_nonneg _
  have hu0 : (0 : ℝ) ≤ u := Nat.cast_nonneg _
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg _
  have hS0 : (0 : ℝ) ≤ S := Nat.cast_nonneg _
  have hrho : 0 ≤ Formalism.IncomingBounds.rho l := by unfold Formalism.IncomingBounds.rho; rw [h3]; positivity
  have hb : RF.blockBd l n m 1 y ≤ Formalism.IncomingBounds.rho l * n * ((l + 1) * y) + n * (Real.logb l n + 1) +
      2 * m * ((l + 1) * y) / ((l : ℝ) - 1) := by
    unfold RF.blockBd
    split_ifs with h
    · positivity
    · apply le_of_eq
      unfold bdP Formalism.IncomingBounds.gam Formalism.IncomingBounds.rho
      rw [h3]
      field_simp
      ring
  have hc : RF.chBd l n m u ≤ 2 * n * S + m * u / ((l : ℝ) - 1) := by
    unfold RF.chBd Formalism.IncomingBounds.gam
    have : (u : ℝ) * (n * ((l : ℝ) / ((l : ℝ) ^ 2 - 1))) ≤ 2 * n * S := by
      calc (u : ℝ) * (n * ((l : ℝ) / ((l : ℝ) ^ 2 - 1)))
          ≤ ((l + 1) * S) * (n * ((l : ℝ) / ((l : ℝ) ^ 2 - 1))) := by
            apply mul_le_mul_of_nonneg_right hu'; rw [h3]; positivity
        _ = n * S * ((l : ℝ) / ((l : ℝ) - 1)) := by rw [h3]; field_simp
        _ ≤ n * S * 2 := by
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            rw [div_le_iff₀ h1]; linarith
        _ = _ := by ring
    have e : (u : ℝ) * (n * ((l : ℝ) / ((l : ℝ) ^ 2 - 1)) + m / ((l : ℝ) - 1)) =
        (u : ℝ) * (n * ((l : ℝ) / ((l : ℝ) ^ 2 - 1))) + m * u / ((l : ℝ) - 1) := by ring
    rw [e]; linarith
  have hd : 2 * m * ((l + 1) * y) / ((l : ℝ) - 1) + m * u / ((l : ℝ) - 1) ≤
      4 * m * ((l + 1) * y + u) / l := by
    have hi : 1 / ((l : ℝ) - 1) ≤ 2 / l := by
      rw [div_le_div_iff₀ h1 (by linarith)]; linarith
    calc 2 * m * ((l + 1) * y) / ((l : ℝ) - 1) + m * u / ((l : ℝ) - 1)
        = (2 * m * ((l + 1) * y) + m * u) * (1 / ((l : ℝ) - 1)) := by ring
      _ ≤ (2 * m * ((l + 1) * y) + 2 * m * u) * (2 / l) := by
          apply mul_le_mul _ hi (by positivity) (by positivity)
          nlinarith [mul_nonneg hm0 hu0]
      _ = _ := by ring
  have he : 0 ≤ Formalism.IncomingBounds.rho l * n * u := by positivity
  push_cast
  have e2 : Formalism.IncomingBounds.rho l * n * (((l : ℝ) + 1) * y + u) =
      Formalism.IncomingBounds.rho l * n * ((l + 1) * y) + Formalism.IncomingBounds.rho l * n * u := by ring
  rw [e2]
  linarith

theorem additive_bound (l n : ℕ) (hl : 5 ≤ l) (hn : 3 ≤ n) :
    (n : ℝ) * (Real.logb l n + 1) + 2 * n * (S0 l 1 n : ℝ) ≤ 900 * ((n : ℝ) ^ 3 * Real.log ((n : ℝ) + 1)) := by
  have hl' : (5 : ℝ) ≤ l := by exact_mod_cast hl
  have hn' : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have hL : 1 ≤ Real.log ((n : ℝ) + 1) := one_le_log _ (by linarith)
  have h1 : Real.logb l n ≤ Real.log ((n : ℝ) + 1) :=
    (logb_le_log l hl _ (by linarith)).trans (Real.log_le_log (by linarith) (by linarith))
  have h2 : Real.logb l ((n : ℝ) + 1) ≤ Real.log ((n : ℝ) + 1) := logb_le_log l hl _ (by linarith)
  have h2' : 0 ≤ Real.logb l ((n : ℝ) + 1) := Real.logb_nonneg (by linarith) (by linarith)
  set L := Real.log ((n : ℝ) + 1)
  have hn2 : (1 : ℝ) ≤ (n : ℝ) ^ 2 := by nlinarith
  have hnL : 1 ≤ (n : ℝ) ^ 2 * L := by nlinarith
  have hnL' : L ≤ (n : ℝ) ^ 2 * L := by nlinarith
  have hS : (S0 l 1 n : ℝ) ≤ 449 * ((n : ℝ) ^ 2 * L) := by
    unfold S0
    have := Nat.ceil_lt_add_one (a := 64 * (n : ℝ) ^ 2 * (((1 : ℕ) : ℝ) + 3 + 3 * Real.logb l ((n : ℝ) + 1)))
      (by positivity)
    have h4 : 64 * (n : ℝ) ^ 2 * (((1 : ℕ) : ℝ) + 3 + 3 * Real.logb l ((n : ℝ) + 1)) ≤ 64 * (n : ℝ) ^ 2 * (7 * L) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      push_cast; linarith
    nlinarith
  have : Real.logb l n + 1 + 2 * (S0 l 1 n : ℝ) ≤ 900 * ((n : ℝ) ^ 2 * L) := by linarith
  calc _ = (n : ℝ) * (Real.logb l n + 1 + 2 * (S0 l 1 n : ℝ)) := by ring
    _ ≤ n * (900 * ((n : ℝ) ^ 2 * L)) := mul_le_mul_of_nonneg_left this (by linarith)
    _ = _ := by ring

theorem thl_nonneg (k l : ℕ) : 0 ≤ thl k l := by
  unfold thl
  apply Real.sSup_nonneg
  rintro t ⟨i, -, -, -, rfl⟩
  positivity

theorem rk_alt {C : Type} [Field C] {V : VF C} {I J : Fin 2 → Type} [∀ g, Fintype (I g)] [∀ g, Fintype (J g)]
    (X : RowData C V 2 I J) (h : X.Alt) : X.big 0 0 ∧ X.rkF 0 0 = X.n + X.j ∧ X.rkF 0 1 = X.j' := by
  have h0 : X.big 0 0 := (h.2 0).2 (by decide)
  have h1 : ¬ X.big 0 1 := fun hb => absurd ((h.2 1).1 hb) (by decide)
  exact ⟨h0, X.rk_big 0 0 h0, X.rk_small 0 1 h1⟩

def expEven (n x : ℕ) (ga : ZMod 2 → ℕ → ℕ) : ZMod 2 → ℕ → ℕ :=
  fun a k => if a = 0 then (if k = n then x else ga 0 k) else 0

def expOdd (ga : ZMod 2 → ℕ → ℕ) : ZMod 2 → ℕ → ℕ := fun a k => if a = 1 then ga 1 k else 0

theorem sum_two (f : ZMod 2 → ℝ) : ∑ a, f a = f 0 + f 1 := Fin.sum_univ_two f
theorem sum_two' (f : ZMod 2 → ℕ) : ∑ a, f a = f 0 + f 1 := Fin.sum_univ_two f

theorem monDeg_le (N N' : ℕ) (e : ℕ → ℕ) : (monDeg N N' e : ℝ) ≤ ∑ k ∈ Finset.Icc 1 N, (k : ℝ) * e k := by
  unfold monDeg
  push_cast
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.Icc_subset_Icc_right (min_le_left _ _))
    (fun _ _ _ => by positivity)

theorem deg_le {C : Type} [Field C] {V : VF C} {I J : Fin 2 → Type} [∀ g, Fintype (I g)] [∀ g, Fintype (J g)]
    (X : RowData C V 2 I J) (n x r : ℕ) (ga : ZMod 2 → ℕ → ℕ) :
    (RF.monDegAll X 0 (expEven n x ga) r : ℝ) + RF.monDegAll X 0 (expOdd ga) r ≤
      (∑ s : ZMod 2, ∑ k ∈ Finset.Icc 1 r, (if s = 0 ∧ k = n then (0 : ℝ) else (k : ℝ) * ga s k)) + (n : ℝ) * x := by
  have h10 : (1 : ZMod 2) ≠ 0 := by decide
  unfold RF.monDegAll
  rw [sum_two', sum_two', sum_two]
  push_cast
  have a1 := monDeg_le r (X.rkF 0 0) (expEven n x ga 0)
  have a2 := monDeg_le r (X.rkF 0 1) (expEven n x ga 1)
  have a3 := monDeg_le r (X.rkF 0 0) (expOdd ga 0)
  have a4 := monDeg_le r (X.rkF 0 1) (expOdd ga 1)
  have b2 : ∑ k ∈ Finset.Icc 1 r, (k : ℝ) * (expEven n x ga 1 k) = 0 := by simp [expEven, h10]
  have b3 : ∑ k ∈ Finset.Icc 1 r, (k : ℝ) * (expOdd ga 0 k) = 0 := by simp [expOdd, h10.symm]
  have b4 : ∑ k ∈ Finset.Icc 1 r, (k : ℝ) * (expOdd ga 1 k) =
      ∑ k ∈ Finset.Icc 1 r, (if (1 : ZMod 2) = 0 ∧ k = n then (0 : ℝ) else (k : ℝ) * ga 1 k) := by
    simp [expOdd, h10]
  have b1 : ∑ k ∈ Finset.Icc 1 r, (k : ℝ) * (expEven n x ga 0 k) ≤
      ∑ k ∈ Finset.Icc 1 r, (if (0 : ZMod 2) = 0 ∧ k = n then (0 : ℝ) else (k : ℝ) * ga 0 k) + (n : ℝ) * x := by
    have : ∑ k ∈ Finset.Icc 1 r, (if k = n then (n : ℝ) * x else 0) ≤ (n : ℝ) * x := by
      rw [Finset.sum_ite_eq']
      split_ifs
      · exact le_rfl
      · positivity
    refine le_trans (le_of_eq ?_) (add_le_add le_rfl this)
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    by_cases hk : k = n <;> simp [expEven, hk]
  linarith

theorem val_le (hC : RF.CHSupply) (hM : RF.MONSupply) (C1 : ℝ) (P : RF.Par) (l : ℕ) (hP : ParOK P) (hl : 5 ≤ l)
    (Pk : RF.PkgPhiC P l C1) (y u : P.Pl → ℕ) (hW : ∀ z, Pk.W z = (l + 1) * y z + u z)
    (hy : ∀ z, (RF.GlobalTheory.bi 0 0 1 (y z)).Attains (Pk.R.X z) (Pk.R.F z) (RF.blockBd l (P.k - 1) P.m 1 (y z))) :
    Pk.ν ≤ ∑ z, (RF.blockBd l (P.k - 1) P.m 1 (y z) + RF.chBd l (P.k - 1) P.m (u z)) + Pk.rest / ((l : ℝ) - 1) := by
  obtain ⟨R, alt, gaC, W, nW, T, θ0, rest, ν, hsupp, hmain, hrest, hrows, hD, hval⟩ := Pk
  obtain ⟨C, V, hV, I, J, X, F, hX⟩ := R
  dsimp only at *
  subst hV
  have hk : 4 ≤ P.k := by have := hP.mk_le; have := hP.m_pos; omega
  have hl' : (5 : ℝ) ≤ V.l := by exact_mod_cast hl
  have h10 : (1 : ZMod 2) ≠ 0 := by decide
  have hrk := fun z => rk_alt (X z) (alt z)
  have hr : P.r = P.k - 1 + P.m := hP.r_eq
  have hm : ∀ z, (X z).j + (X z).j' = P.m := fun z => (hX z).2
  have key := hval (fun z =>
    [(RF.GlobalTheory.bi 0 0 1 (y z), RF.blockBd V.l (P.k - 1) P.m 1 (y z)),
     (RF.GlobalTheory.ch 0 0 (u z), RF.chBd V.l (X z).n (X z).m (u z)),
     (RF.GlobalTheory.mon 0 (expEven (P.k - 1) 0 (gaC z)) P.r,
       (RF.monDegAll (X z) 0 (expEven (P.k - 1) 0 (gaC z)) P.r : ℝ) / ((V.l : ℝ) - 1)),
     (RF.GlobalTheory.mon 0 (expOdd (gaC z)) P.r,
       (RF.monDegAll (X z) 0 (expOdd (gaC z)) P.r : ℝ) / ((V.l : ℝ) - 1))]) ?_ ?_ ?_ ?_
  · refine key.trans ?_
    rw [hrest, Finset.sum_div, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun z _ => ?_
    have hd := deg_le (X z) (P.k - 1) 0 P.r (gaC z)
    rw [Nat.cast_zero, mul_zero, add_zero] at hd
    have hd' := div_le_div_of_nonneg_right hd (c := (V.l : ℝ) - 1) (by linarith)
    rw [add_div] at hd'
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, (hX z).1, (hX z).2]
    linarith
  · intro z p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl
    · exact hy z
    · exact (hC C V 2 (I z) (J z) (X z) (F z) 0 0 (hrk z).1 (u z)).1 (alt z)
    · exact (hM C V 2 (I z) (J z) (X z) (F z) 0 _ _).1
    · exact (hM C V 2 (I z) (J z) (X z) (F z) 0 _ _).1
  · intro z p hp g e M he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl
    · cases he
    · cases he
    · cases he
      exact ⟨0, fun a k ha => by simp [expEven, ha]⟩
    · cases he
      exact ⟨1, fun a k ha => by simp [expOdd, ha]⟩
  · refine le_trans ?_ hrows
    have : ∀ z : P.Pl, (X z).n + ((X z).n + (P.r + (P.r + 0))) ≤ 4 * P.r := by
      intro z; rw [(hX z).1]; omega
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, RF.GlobalTheory.what₂]
    have h2 := Finset.sum_le_sum (s := Finset.univ) fun z _ => this z
    rw [Finset.sum_const, Finset.card_univ, hP.card, smul_eq_mul] at h2
    nlinarith
  · intro z s k
    have e0 := (hrk z).2.1
    have e1 := (hrk z).2.2
    have hn := (hX z).1
    have hmz := hm z
    have hs := hsupp z s k
    have hw := hW z
    have hma := hmain z
    have hs2 : s = 0 ∨ s = 1 := (by decide : ∀ s : ZMod 2, s = 0 ∨ s = 1) s
    have h11 : (1 : ZMod 2) + 1 = 0 := by decide
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, RF.GlobalTheory.wt, hn]
    rcases hs2 with rfl | rfl
    · have hmin : min P.r ((X z).rkF 0 0) = (X z).rkF 0 0 := min_eq_right (by omega)
      by_cases hkn : k = P.k - 1
      · subst hkn
        have c1 : 1 ≤ P.k - 1 := by omega
        have c2 : P.k - 1 ≤ (X z).rkF 0 0 := by omega
        simp [expEven, expOdd, hmin, c1, c2, hma, hw, h10.symm]
        ring
      · by_cases hg : gaC z 0 k = 0
        · simp [expEven, expOdd, hkn, hg, h10.symm]
        · simp [expEven, expOdd, hkn, hmin, hs hg, h10.symm]
    · have hmin : min P.r ((X z).rkF 0 1) = (X z).rkF 0 1 := min_eq_right (by omega)
      by_cases hg : gaC z 1 k = 0
      · simp [expEven, expOdd, hg, h10, h11, h10.symm]
      · simp [expEven, expOdd, hmin, hs hg, h10, h11, h10.symm]

theorem of_supplies (hB : RF.BiSupply) (hC : RF.CHSupply) (hM : RF.MONSupply) : PhiCBd := by
  intro C1 hC1
  refine ⟨900 + 7 * C1, by linarith, fun P l hP hp hl Pk => ?_⟩
  have hk : 4 ≤ P.k := by have := hP.mk_le; have := hP.m_pos; omega
  have hG : ∀ z, RF.Windows (S0 l 1 (P.k - 1)) {y | (RF.GlobalTheory.bi 0 0 1 y).Attains (Pk.R.X z) (Pk.R.F z)
      (RF.blockBd l (P.k - 1) P.m 1 y)} := by
    intro z
    have := hB Pk.R.C Pk.R.V 2 (Pk.R.I z) (Pk.R.J z) (Pk.R.X z) (Pk.R.F z) (Pk.alt z) (by rw [Pk.R.hVl]; exact hl)
      (by rw [(Pk.R.hn z).1]; omega) 0 0 (rk_alt _ (Pk.alt z)).1 1 odd_one (by norm_num)
    rwa [(Pk.R.hn z).1, (Pk.R.hn z).2, Pk.R.hVl] at this
  choose y u hW hy hu using fun z => exists_good l _ (Pk.W z) _ (hG z)
  have h1 := val_le hC hM C1 P l hP hl Pk y u hW hy
  have hD := Pk.deg
  generalize Pk.T = T at *
  generalize Pk.ν = ν at *
  generalize Pk.rest = rest at *
  generalize Pk.W = W at *
  clear hG hy
  obtain ⟨n, hn⟩ : ∃ n, P.k = n + 1 := ⟨P.k - 1, by omega⟩
  have hn3 : 3 ≤ n := by omega
  have hn1 : P.k - 1 = n := by omega
  have hkr : (P.k : ℝ) = n + 1 := by exact_mod_cast hn
  have hl' : (5 : ℝ) ≤ l := by exact_mod_cast hl
  have hn' : (3 : ℝ) ≤ n := by exact_mod_cast hn3
  have hmn : (P.m : ℝ) ≤ n := by have := hP.mk_le; exact_mod_cast (by omega : P.m ≤ n)
  rw [hn1] at h1 hu
  have hT : 0 < T := by linarith [hD.T_one]
  have hSE := hP.SE_nonneg
  have hl2 : (0 : ℝ) < (l : ℝ) ^ 2 - 1 := by nlinarith
  have hrho : 0 ≤ Formalism.IncomingBounds.rho l := by
    unfold Formalism.IncomingBounds.rho; positivity
  have hrho' : Formalism.IncomingBounds.rho l ≤ 1 / l := by
    unfold Formalism.IncomingBounds.rho
    apply one_div_le_one_div_of_le (by linarith); nlinarith
  set L := Real.log ((n : ℝ) + 1) with hLdef
  have hL : 1 ≤ L := one_le_log _ (by linarith)
  have h2 : ∀ z, T * (RF.blockBd l n P.m 1 (y z) + RF.chBd l n P.m (u z)) ≤
      Formalism.IncomingBounds.rho l * (n * P.w z) + 4 * P.m * P.w z / l + 5 * C1 * ((n + 1) * P.SE / l) +
        T * (900 * ((n : ℝ) ^ 3 * L)) := by
    intro z
    have a1 := place_bound l n P.m _ (y z) (u z) hl (by omega) (hu z)
    rw [← hW z] at a1
    have a2 := additive_bound l n hl hn3
    have a3 := hD.TW_hi z
    have a4 : 0 ≤ Formalism.IncomingBounds.rho l * n + 4 * P.m / l := by positivity
    have a5 : Formalism.IncomingBounds.rho l * n + 4 * P.m / l ≤ 5 * (n + 1) / l := by
      have b1 : Formalism.IncomingBounds.rho l * n ≤ 1 / l * (n + 1) := by gcongr; linarith
      have b2 : (4 : ℝ) * P.m / l ≤ 4 * (n + 1) / l := by gcongr; linarith
      calc _ ≤ 1 / l * (n + 1) + 4 * ((n : ℝ) + 1) / l := add_le_add b1 b2
        _ = _ := by ring
    have a6 := mul_le_mul_of_nonneg_right a5 (mul_nonneg hC1 hSE)
    calc _ ≤ T * (Formalism.IncomingBounds.rho l * n * (W z : ℝ) + 4 * P.m * (W z : ℝ) / l + 900 * ((n : ℝ) ^ 3 * L)) :=
          mul_le_mul_of_nonneg_left (by linarith) hT.le
      _ = (Formalism.IncomingBounds.rho l * n + 4 * P.m / l) * (T * W z) + T * (900 * ((n : ℝ) ^ 3 * L)) := by ring
      _ ≤ (Formalism.IncomingBounds.rho l * n + 4 * P.m / l) * (P.w z + C1 * P.SE) + T * (900 * ((n : ℝ) ^ 3 * L)) := by
          gcongr
      _ = Formalism.IncomingBounds.rho l * (n * P.w z) + 4 * P.m * P.w z / l + (Formalism.IncomingBounds.rho l * n + 4 * P.m / l) * (C1 * P.SE) +
          T * (900 * ((n : ℝ) ^ 3 * L)) := by ring
      _ ≤ Formalism.IncomingBounds.rho l * (n * P.w z) + 4 * P.m * P.w z / l + (5 * (n + 1) / l) * (C1 * P.SE) +
          T * (900 * ((n : ℝ) ^ 3 * L)) := by linarith
      _ = _ := by ring
  have h3 : T * ∑ z, (RF.blockBd l n P.m 1 (y z) + RF.chBd l n P.m (u z)) ≤
      n * (∑ z, P.w z) / ((l : ℝ) ^ 2 - 1) + 4 * (P.m * (∑ z, P.w z) / l) + 5 * C1 * (P.f * (n + 1) * P.SE / l) +
        900 * (T * P.f * (n : ℝ) ^ 3 * L) := by
    rw [Finset.mul_sum]
    refine (Finset.sum_le_sum fun z _ => h2 z).trans (le_of_eq ?_)
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_const, Finset.sum_const,
      Finset.card_univ, hP.card, ← Finset.mul_sum, ← Finset.sum_div, ← Finset.mul_sum, ← Finset.mul_sum,
      nsmul_eq_mul, nsmul_eq_mul]
    unfold Formalism.IncomingBounds.rho
    ring
  have hw : 0 ≤ ∑ z, P.w z := Finset.sum_nonneg fun z _ => (hD.w_pos z).le
  have h4 : T * (rest / ((l : ℝ) - 1)) ≤ 2 * C1 * (P.f * (n + 1) * P.SE / l) := by
    have hi : 1 / ((l : ℝ) - 1) ≤ 2 / l := by
      rw [div_le_div_iff₀ (by linarith) (by linarith)]; linarith
    have h1l : 0 ≤ 1 / ((l : ℝ) - 1) := div_nonneg zero_le_one (by linarith)
    calc T * (rest / ((l : ℝ) - 1)) = T * rest * (1 / ((l : ℝ) - 1)) := by ring
      _ ≤ C1 * (P.f * P.k * P.SE) * (2 / l) :=
          mul_le_mul hD.rest_le hi h1l (by positivity)
      _ = _ := by rw [hkr]; ring
  have h8 := mul_le_mul_of_nonneg_left h1 hT.le
  rw [mul_add] at h8
  have hth := thl_nonneg P.k l
  unfold errB
  rw [hkr, ← hLdef, add_sub_cancel_right]
  have eA : L * P.m * (∑ z, P.w z) / l = L * (P.m * (∑ z, P.w z) / l) := by ring
  have eD : T * P.f * (n : ℝ) ^ 3 * L ^ 2 = L * (T * P.f * (n : ℝ) ^ 3 * L) := by ring
  rw [eA, eD]
  have pA : 0 ≤ P.m * (∑ z, P.w z) / l := by positivity
  have pB : 0 ≤ P.f * ((n : ℝ) + 1) * P.SE / l := by positivity
  have pC : 0 ≤ ((n : ℝ) + 1) * thl P.k l * ∑ z, P.w z := by positivity
  have pD : 0 ≤ T * P.f * (n : ℝ) ^ 3 * L := by positivity
  generalize P.m * (∑ z, P.w z) / l = A at *
  generalize P.f * ((n : ℝ) + 1) * P.SE / l = B at *
  generalize ((n : ℝ) + 1) * thl P.k l * ∑ z, P.w z = Cth at *
  generalize T * P.f * (n : ℝ) ^ 3 * L = D at *
  have qA : A ≤ L * A := le_mul_of_one_le_left pA hL
  have qD : D ≤ L * D := le_mul_of_one_le_left pD hL
  have r1 : 0 ≤ C1 * (L * A + Cth + L * D) := mul_nonneg hC1 (by linarith)
  nlinarith

theorem phiCBd : PhiCBd := of_supplies GlobalTheory.T.oddLevelBlock_bound_attained.2 GlobalTheory.CharBlock.chSupply.2 GlobalTheory.T.monomialBlock_supply_both_typings.2

end GlobalTheory.GoodDepth.ConjPkg
