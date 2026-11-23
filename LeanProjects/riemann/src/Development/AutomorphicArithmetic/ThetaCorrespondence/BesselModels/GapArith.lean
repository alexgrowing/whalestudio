import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LevelModelsOfFunctoriality
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HighestWeightBelow
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CartFrSgn

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open Formalism.IndefR.Mult IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace UpperTheory.Lit.Bur.Gap

section Num

open GlobalTheory.SignedHC GlobalTheory.PairLift

variable (D : D7) (C : ℝ) (τ : D.what₂.Tau)

theorem b_spec {a : ℕ} (ha : a < D.R.m) : (D.hc τ).b ⟨a, ha⟩ = ((num D C τ).b (a + 1) : ℚ) :=
  (GlobalTheory.SignedHC.GridData.ofHCParam_spec (D.hc τ) (sLen D) (gap D C) (cen D C τ)).2.1 ⟨a, ha⟩

theorem e_spec {a : ℕ} (ha : a < D.R.m) : (D.hc τ).e ⟨a, ha⟩ = ((num D C τ).e (a + 1) : ℚ) :=
  (GlobalTheory.SignedHC.GridData.ofHCParam_spec (D.hc τ) (sLen D) (gap D C) (cen D C τ)).2.2 ⟨a, ha⟩

theorem v_spec {a : ℕ} (ha : a < D.R.k - 1) : (D.hc τ).v ⟨a, ha⟩ = ((num D C τ).v (a + 2) : ℚ) :=
  (GlobalTheory.SignedHC.GridData.ofHCParam_spec (D.hc τ) (sLen D) (gap D C) (cen D C τ)).1 ⟨a, ha⟩

theorem b_add_le_e {l : ℕ} (h1 : 1 ≤ l) (h2 : l ≤ D.R.m) :
    ((num D C τ).b l : ℚ) + ((D.R.t : ℚ) + 3) / 2 ≤ (num D C τ).e l := by
  obtain ⟨a, rfl⟩ : ∃ a, l = a + 1 := ⟨l - 1, by omega⟩
  have h := (D.hc τ).gap_be ⟨a, by omega⟩
  rw [e_spec D C τ (by omega), b_spec D C τ (by omega)] at h
  linarith

theorem e_add_le_b {l : ℕ} (h1 : 1 ≤ l) (h2 : l + 1 ≤ D.R.m) :
    ((num D C τ).e l : ℚ) + ((D.R.t : ℚ) + 3) / 2 ≤ (num D C τ).b (l + 1) := by
  obtain ⟨a, rfl⟩ : ∃ a, l = a + 1 := ⟨l - 1, by omega⟩
  have h : ((D.R.t : ℚ) + 3) / 2 ≤ (D.hc τ).b ⟨a + 1, by omega⟩ - (D.hc τ).e ⟨a, by omega⟩ :=
    (D.hc τ).gap_eb ⟨a, by omega⟩ (by simpa using h2)
  rw [e_spec D C τ (by omega), b_spec D C τ (by omega)] at h
  linarith

theorem b_lt {l l' : ℕ} (h1 : 1 ≤ l) (h2 : l < l') (h3 : l' ≤ D.R.m) : ((num D C τ).b l : ℚ) < (num D C τ).b l' := by
  exact_mod_cast (num D C τ).b_mono l l' h1 h2 h3

theorem b_le {l l' : ℕ} (h1 : 1 ≤ l) (h2 : l ≤ l') (h3 : l' ≤ D.R.m) : ((num D C τ).b l : ℚ) ≤ (num D C τ).b l' := by
  rcases h2.eq_or_lt with rfl | h
  · exact le_rfl
  · exact (b_lt D C τ h1 h h3).le

theorem cloud_gt {x : ℚ} (h : x ∈ (num D C τ).cloud) : -((num D C τ).b 1 : ℚ) < x := by
  obtain ⟨i, h1, h2, rfl⟩ := GlobalTheory.SignedHC.GridData.mem_cloud.1 h
  have hk : D.R.m + 3 ≤ D.R.k := D.R.m_add_three_le_k
  have hm : 2 ≤ D.R.m := D.R.two_le_m
  have hik : i ≤ D.R.k := h2
  have a1 := (D.hc τ).u_last_gt (by omega) (by omega)
  have a2 := (D.hc τ).v_gt_u ⟨D.R.k - 2, by omega⟩
  have e : (⟨(⟨D.R.k - 2, by omega⟩ : Fin (D.R.k - 1)).1 + 1, by simp only; omega⟩ : Fin D.R.k) = ⟨D.R.k - 1, by omega⟩ :=
    Fin.ext (by simp only; omega)
  rw [e] at a2
  rw [v_spec D C τ (by omega)] at a2
  have e0 : (D.hc τ).b ⟨0, by omega⟩ = ((num D C τ).b 1 : ℚ) := b_spec D C τ (by omega)
  rw [e0] at a1
  have e2 : D.R.k - 2 + 2 = D.R.k := by omega
  simp only [e2] at a2
  have a3 : ((num D C τ).v D.R.k : ℚ) ≤ (num D C τ).v i := by
    rcases hik.eq_or_lt with rfl | h
    · exact le_rfl
    · exact_mod_cast ((num D C τ).v_anti i D.R.k h1 h le_rfl).le
  linarith

theorem blockM_bound {a : ℕ} {x : ℚ} (h : x ∈ (num D C τ).blockM a) :
    -((num D C τ).e a : ℚ) - ((D.R.t : ℚ) - 1) / 2 ≤ x ∧ x ≤ -((num D C τ).e a : ℚ) + ((D.R.t : ℚ) - 1) / 2 := by
  have := abs_le.1 (abs_sub_le_of_mem_block (c := -((num D C τ).e a : ℚ)) (t := D.R.t) h)
  constructor <;> linarith [this.1, this.2]

variable {D} in

theorem blockC_gt {a : ℕ} (h1 : 1 ≤ a) (h2 : a ≤ D.R.m) {x : ℚ} (h : x ∈ (num D C τ).blockC a) :
    -((num D C τ).b 1 : ℚ) < x := by
  have hb := abs_le.1 (abs_sub_le_of_mem_block (c := ((num D C τ).cen a : ℚ)) (t := sLen D) h)
  have hn := abs_le.1 ((num_nearMid D C τ) a (Finset.mem_Icc.2 ⟨h1, h2⟩))
  rw [(num D C τ).mid_eq h1] at hn
  have hg : 2 * bigN D ^ 3 + 2 * sLen D + 2 < gap D C := (isLeast_gap D C).1.2.1
  have hg' : 2 * (sLen D : ℚ) + 2 ≤ (gap D C : ℚ) := by
    have : 2 * sLen D + 2 ≤ gap D C := by omega
    exact_mod_cast this
  have hs0 : (0 : ℚ) ≤ sLen D := by positivity
  have hga : ((num D C τ).ga : ℚ) = gap D C := rfl
  have ha : (num D C τ).a a = ((num D C τ).v 2 : ℚ) + 1 / 2 + (((num D C τ).m : ℚ) + 1 - a) * gap D C := by
    rw [GlobalTheory.SignedHC.GridData.a, hga]
  have hma : (a : ℚ) ≤ ((num D C τ).m : ℚ) := by exact_mod_cast h2
  have hmul : (gap D C : ℚ) ≤ (((num D C τ).m : ℚ) + 1 - a) * gap D C := by
    have : (0 : ℚ) ≤ gap D C := by positivity
    nlinarith
  have hv : -((num D C τ).b 1 : ℚ) < (num D C τ).v 2 := by
    have hk : D.R.m + 3 ≤ D.R.k := D.R.m_add_three_le_k
    exact cloud_gt D C τ (GlobalTheory.SignedHC.GridData.mem_cloud.2 ⟨2, le_rfl, by show 2 ≤ D.R.k; omega, rfl⟩)
  rw [ha, hga] at hn
  linarith [hb.1, hn.1]

variable {D C τ} in
theorem gapOver_shift {Q : SPar} {g : ℚ} (a : ℚ) (H : GapOver Q g) : GapOver (shift a Q) g := by
  intro x hx y hy hne
  have := H _ (mem_shift.1 hx) _ (mem_shift.1 hy) hne
  simpa using this

end Num

section Gap

open GlobalTheory.SignedHC GlobalTheory.PairLift

def LowsOver (D : D7) (g : ℚ) : Prop :=
  ∀ (τ : D.what₂.Tau) (j : ℕ) (hj : j + 1 < D.R.m), g < (D.hc τ).b ⟨j + 1, hj⟩ - (D.hc τ).b ⟨j, by omega⟩

variable {D : D7} {g : ℚ}

theorem b_gap (C : ℝ) (hS : LowsOver D g) (τ : D.what₂.Tau) {l l' : ℕ} (h1 : 1 ≤ l) (h2 : l < l') (h3 : l' ≤ D.R.m) :
    g < ((num D C τ).b l' : ℚ) - (num D C τ).b l := by
  obtain ⟨a, rfl⟩ : ∃ a, l' = a + 2 := ⟨l' - 2, by omega⟩
  have h := hS τ a (by omega)
  rw [b_spec D C τ (by omega), b_spec D C τ (by omega)] at h
  have := b_le D C τ h1 (show l ≤ a + 1 by omega) (by omega)
  linarith

theorem gap_true (C : ℝ) (hS : LowsOver D g) (τ : D.what₂.Tau) {i j l : ℕ} (hi : i ≤ D.R.m) (hl1 : j + 2 ≤ l)
    (hl2 : l ≤ D.R.m) (hodd : ¬ Even (l - j - 1)) {y : ℚ} (hy : (y, true) ∈ (num D C τ).parD i j) :
    g < |y - -((num D C τ).b l : ℚ)| := by
  have top : -((num D C τ).b 1 : ℚ) < y → g < |y - -((num D C τ).b l : ℚ)| := fun h => by
    have := b_gap C hS τ (show 1 ≤ 1 by omega) (show 1 < l by omega) hl2
    exact lt_abs.2 (Or.inl (by linarith))
  rw [GlobalTheory.SignedHC.GridData.mem_parD] at hy
  rcases hy with ⟨hc, -⟩ | ⟨l', h1, h2, e⟩ | ⟨a, h1, h2, hm, -⟩ | ⟨a, h1, h2, hc, -⟩
  · exact top (cloud_gt D C τ hc)
  · obtain ⟨rfl, es⟩ := Prod.mk.inj e
    have hne : l' ≠ l := by
      rintro rfl
      have : l' ≤ j + 1 ∨ Even (l' - j - 1) := by simpa using es
      rcases this with h | h
      · omega
      · exact hodd h
    rcases lt_or_gt_of_ne hne with h | h
    · have := b_gap C hS τ h1 h hl2
      refine lt_abs.2 (Or.inl (by linarith))
    · have := b_gap C hS τ (show 1 ≤ l by omega) h h2
      refine lt_abs.2 (Or.inr (by linarith))
  · have a0 := (blockM_bound D C τ hm).1
    have a1 := e_add_le_b D C τ h1 (show a + 1 ≤ D.R.m by omega)
    have a2 := b_gap C hS τ (show 1 ≤ a + 1 by omega) (show a + 1 < l by omega) hl2
    refine lt_abs.2 (Or.inl (by linarith))
  · have h0 : (num D C τ).m = D.R.m := rfl
    rw [h0] at h1 h2
    exact top (blockC_gt C τ (by omega) h2 hc)

theorem gapOver_parD (C : ℝ) (hS : LowsOver D g) (τ : D.what₂.Tau) {i : ℕ} (j : ℕ) (hi : i ≤ D.R.m) :
    GapOver ((num D C τ).parD i j) g := by
  have key : ∀ x y : ℚ, (x, false) ∈ (num D C τ).parD i j → (y, true) ∈ (num D C τ).parD i j →
      g < |y - x| := by
    intro x y hx hy
    rw [GlobalTheory.SignedHC.GridData.mem_parD] at hx
    rcases hx with ⟨-, h⟩ | ⟨l, h1, h2, e⟩ | ⟨a, -, -, -, h⟩ | ⟨a, -, -, -, h⟩
    · exact absurd h (by simp)
    · obtain ⟨rfl, es⟩ := Prod.mk.inj e
      have hn : ¬ (l ≤ j + 1 ∨ Even (l - j - 1)) := by simpa using es.symm
      push_neg at hn
      exact gap_true C hS τ hi (by omega) h2 (by simpa using hn.2) hy
    · exact absurd h (by simp)
    · exact absurd h (by simp)
  rintro ⟨x, s⟩ hx ⟨y, s'⟩ hy hne
  cases s <;> cases s'
  · exact absurd rfl hne
  · exact (abs_sub_comm x y) ▸ key x y hx hy
  · exact key y x hy hx
  · exact absurd rfl hne

theorem gapAtLeast_of_gapOver {n : ℕ} {P : SPar} {lam : Fin n → ℝ} {ε : Fin n → Bool}
    (hE : IsEnum (dualPar P) lam ε) (hG : GapOver P g) : Formalism.QuantumDeterminants.GapAtLeast ε lam (g : ℝ) := by
  intro a b hab
  obtain ⟨-, q, hq, hS⟩ := hE
  have mem : ∀ c, (-(q c), ε c) ∈ P := fun c => by
    have h1 : (q c, ε c) ∈ dualPar P := by
      rw [hS]
      exact Finset.mem_image_of_mem (fun a => (q a, ε a)) (Finset.mem_univ c)
    obtain ⟨x, hx, e⟩ := Finset.mem_image.1 h1
    obtain ⟨e1, e2⟩ := Prod.mk.inj e
    have e3 : x = (-(q c), ε c) := Prod.ext (by simp [← e1]) e2
    rw [e3] at hx; exact hx
  have h2 : g < |(-(q a)) - (-(q b))| := by
    have h0 := hG (-(q a), ε a) (mem a) (-(q b), ε b) (mem b) hab
    simpa only using h0
  have e : (-(q a)) - (-(q b)) = -(q a - q b) := by ring
  rw [e, abs_neg] at h2
  rw [hq, hq]
  have h3 : ((g : ℚ) : ℝ) ≤ ((|q a - q b| : ℚ) : ℝ) := by exact_mod_cast h2.le
  push_cast at h3
  exact h3

end Gap

theorem size_arith {k m r : ℕ} (hr : r + 1 = k + m) (hk : m + 3 ≤ k) (hm : 44 ≤ m) {Den Del : ℝ}
    (hDel : (k : ℝ) * (m : ℝ) ^ 10 ≤ Del) (hDen : (k : ℝ) * ((k : ℝ) * (4 * Del)) ≤ Den) :
    120 * ((r + m * (r + 6) : ℕ) : ℝ) ^ 3 ≤ 12 * Den / m := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  have hk0 : (0 : ℝ) ≤ k := by positivity
  have h1 : r + m * (r + 6) ≤ 6 * m * k := by
    have a1 : r + 6 ≤ 3 * k := by omega
    have a2 : m * (r + 6) ≤ m * (3 * k) := Nat.mul_le_mul_left _ a1
    have a3 : 3 * k ≤ m * (3 * k) := Nat.le_mul_of_pos_left _ (by omega)
    have e : 6 * m * k = m * (3 * k) + m * (3 * k) := by ring
    omega
  have h2 : ((r + m * (r + 6) : ℕ) : ℝ) ≤ 6 * m * k := by exact_mod_cast h1
  have h3 : ((r + m * (r + 6) : ℕ) : ℝ) ^ 3 ≤ (6 * m * k) ^ 3 := pow_le_pow_left₀ (by positivity) h2 3
  have h4 : (44 : ℝ) ≤ m := by exact_mod_cast hm
  have h5 : (44 : ℝ) ^ 6 ≤ (m : ℝ) ^ 6 := pow_le_pow_left₀ (by norm_num) h4 6
  rw [le_div_iff₀ hm0]
  have h6 : (k : ℝ) * ((k : ℝ) * (4 * ((k : ℝ) * (m : ℝ) ^ 10))) ≤ Den := by
    refine le_trans ?_ hDen
    have : (k : ℝ) * (k : ℝ) ≥ 0 := by positivity
    nlinarith
  have h7 : 0 ≤ (k : ℝ) ^ 3 * (m : ℝ) ^ 4 := by positivity
  have h8 : (0 : ℝ) ≤ ((m : ℝ) ^ 6 - 540) * ((k : ℝ) ^ 3 * (m : ℝ) ^ 4) :=
    mul_nonneg (by nlinarith) h7
  have h9 : 120 * ((r + m * (r + 6) : ℕ) : ℝ) ^ 3 * m ≤ 120 * (6 * m * k) ^ 3 * m := by
    exact mul_le_mul_of_nonneg_right (by linarith) hm0.le
  nlinarith

theorem lowsOver_of_sizeRows {D : D7} (large₂ : SizeData₂ D) (hs : SizeRows large₂) :
    LowsOver D (120 * (rankV D D.R.m 0 : ℚ) ^ 3) := by
  intro τ j hj
  obtain ⟨⟨Pm, _, _⟩, _, _, hm44, _⟩ := hs
  have hb : 0 < large₂.sc.b := Real.exp_pos _
  have hL : 0 < large₂.sc.L := Real.rpow_pos_of_pos (by linarith [large₂.sc.one_lt_alt]) _
  have hm0 : (0 : ℝ) < D.R.m := by exact_mod_cast (by omega : 0 < D.R.m)
  have hn : (1 : ℝ) ≤ D.R.n := by
    have : 1 ≤ D.R.n := by
      have h1 := D.R.m_le_f
      have h2 := D.R.two_le_m
      unfold Ranks.n
      omega
    exact_mod_cast this
  have hSc := large₂.Sc_pos
  have hkN : (D.R.k : ℝ) ≤ D.R.N D.R.m := by
    have : D.R.k ≤ D.R.N D.R.m := by unfold Ranks.N; omega
    exact_mod_cast this
  have hDel : (D.R.k : ℝ) * (D.R.m : ℝ) ^ 10 ≤ (D.s.Del : ℝ) :=
    le_trans (mul_le_mul_of_nonneg_right hkN (by positivity)) Pm.Del_ge.2.2.2
  have h1 := Pm.h0_ge.1
  have h2 := (Pm.nodes_gap τ j hj).1
  set Den : ℝ := (D.R.n : ℝ) * (D.R.t : ℝ) ^ 2 * ((D.R.N D.R.m : ℝ) + D.R.t) * large₂.sc.L ^ 2 +
    (D.R.k : ℝ) * (D.R.n : ℝ) ^ 2 * (large₂.Sc + D.R.t + large₂.sc.L) with hDen
  have hk0 : (0 : ℝ) ≤ D.R.k := by positivity
  have hDen1 : (D.R.k : ℝ) * ((D.R.k : ℝ) * (4 * (D.s.Del : ℝ))) ≤ Den := by
    rw [← large₂.Sc_eq, hDen]
    have a1 : 0 ≤ (D.R.n : ℝ) * (D.R.t : ℝ) ^ 2 * ((D.R.N D.R.m : ℝ) + D.R.t) * large₂.sc.L ^ 2 := by positivity
    have a2 : large₂.Sc ≤ (D.R.n : ℝ) ^ 2 * (large₂.Sc + D.R.t + large₂.sc.L) := by
      have : (1 : ℝ) ≤ (D.R.n : ℝ) ^ 2 := one_le_pow₀ hn
      have t0 : (0 : ℝ) ≤ D.R.t := by positivity
      nlinarith
    have a3 := mul_le_mul_of_nonneg_left a2 hk0
    nlinarith
  have hDenPos : 0 < Den := by
    rw [hDen]
    have hkp : (0 : ℝ) < D.R.k := by
      have := D.R.m_add_three_le_k
      exact_mod_cast (by omega : 0 < D.R.k)
    have : 0 < (D.R.k : ℝ) * (D.R.n : ℝ) ^ 2 * (large₂.Sc + D.R.t + large₂.sc.L) := by positivity
    have a1 : 0 ≤ (D.R.n : ℝ) * (D.R.t : ℝ) ^ 2 * ((D.R.N D.R.m : ℝ) + D.R.t) * large₂.sc.L ^ 2 := by positivity
    linarith
  have e : 12 * large₂.sc.b / LevelStarExponents.lStar large₂ = 12 * Den / D.R.m := by
    have : LevelStarExponents.lStar large₂ = (D.R.m : ℝ) * large₂.sc.b / Den := rfl
    rw [this]
    field_simp
  have hr : D.R.r + 1 = D.R.k + D.R.m := by
    have := D.R.m_add_three_le_k
    unfold Ranks.r; omega
  have key := size_arith hr D.R.m_add_three_le_k hm44 hDel hDen1
  have erank : rankV D D.R.m 0 = D.R.r + D.R.m * (D.R.r + 6) := by
    simp [rankV, sLen]
  have t0 : (0 : ℝ) ≤ D.R.t := by positivity
  have h3 : ((120 * (rankV D D.R.m 0 : ℚ) ^ 3 : ℚ) : ℝ) <
      (((D.hc τ).b ⟨j + 1, hj⟩ - (D.hc τ).b ⟨j, by omega⟩ : ℚ) : ℝ) := by
    rw [erank]
    push_cast at key ⊢
    rw [e] at h1
    push_cast at h2
    linarith
  exact_mod_cast h3

theorem fit_gap {D : D7} (large₂ : SizeData₂ D) (hs : SizeRows large₂) {T : Type} {L : LevCh D T} {μ0 : T} (hL : L.Is μ0) {sc : Consts}
    (hsc : sc.cGap = 1) (G : GridData L sc) (MB : DSModel (G.V (.grid D.R.m 0)) (GlobalTheory.SepRows.parRow D sc.cGap D.R.m))
    (τ : D.what₂.Tau) :
    Formalism.QuantumDeterminants.IsHCParam (MB.lam τ) ∧ ∃ h : ℝ, 120 * ((G.V (.grid D.R.m 0)).rank : ℝ) ^ 3 ≤ h ∧
      Formalism.QuantumDeterminants.GapAtLeast (MB.ε τ) (MB.lam τ) h := by
  have hX : (Node.grid D.R.m 0).InRange D.R.m := ⟨le_rfl, Nat.zero_le _⟩
  have hr : (G.V (.grid D.R.m 0)).rank = rankV D D.R.m 0 := (node_isV G hL hX).rank
  have hE : IsEnum (dualPar (parV D sc.cGap D.R.m 0 τ)) (MB.lam τ) (MB.ε τ) := MB.enum τ
  have hG : GlobalTheory.PairLift.GapOver (parV D sc.cGap D.R.m 0 τ) (120 * (rankV D D.R.m 0 : ℚ) ^ 3) := by
    unfold parV
    exact gapOver_shift _ (gapOver_parD sc.cGap (lowsOver_of_sizeRows large₂ hs) τ 0 le_rfl)
  have hE1 : IsEnum (dualPar (parV D 1 D.R.m 0 τ)) (MB.lam τ) (MB.ε τ) := by
    rw [← hsc]
    exact hE
  refine ⟨GlobalTheory.SepRows.isHCParam_dual_parV D D.R.m 0 τ _ _ hr hE1, _, ?_, gapAtLeast_of_gapOver hE hG⟩
  rw [hr]
  push_cast
  exact le_rfl

end UpperTheory.Lit.Bur.Gap

end
