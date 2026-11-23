import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.StandingNumericalData
import Formalism.HermitianCurvature.StatementJCT
import Formalism.SharpRestriction.CuspSpanNormBounds.LocalModelPeriodLattices
import Formalism.HermitianCurvature.HermitianCurvatureProofs.SupremumAIsMajorant

noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S

namespace Formalism.L2.SG.Pf.CarrierSz

theorem unram_host (D : D7) :
    haveI : IsCMField D.host.E := D.host.isCMField_hostE
    Formalism.FourierDecayAlt.S6.Unram D.host.E := by
  have : IsCMField D.host.E := D.host.isCMField_hostE
  exact Formalism.MainNotions.LocalModelPeriodLattices.unramE D

theorem g_pos (D : D7) : 0 < D.host.g 0 ∧ 0 < D.host.g 1 :=
  ⟨(D.host.g_prime 0).pos, (D.host.g_prime 1).pos⟩

section Cut

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
  [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
  [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)]

theorem cut_len (S : Formalism.FourierDecayAlt.C.HidaSetting E Wp Wq) (v : Fin S.f) :
    S.cutHi v - S.cutLo v = S.G.Del / 2 - 5 / 2 := by
  unfold Formalism.FourierDecayAlt.C.HidaSetting.cutHi Formalism.FourierDecayAlt.C.HidaSetting.cutLo
  simp only [Formalism.FourierDecayAlt.Sz.Glob.place]
  ring

theorem ntop_eq (S : Formalism.FourierDecayAlt.C.HidaSetting E Wp Wq) : (S.Ntop : ℝ) = 20 * ((S.G.r : ℝ) + 1) := by
  unfold Formalism.FourierDecayAlt.C.HidaSetting.Ntop Formalism.FourierDecayAlt.C.Kst
  push_cast
  ring

end Cut

theorem rpow_ge_mul {x t : ℝ} (hx : 3 ≤ x) (ht : 1 ≤ t) : t * x ≤ x ^ t := by
  have hx0 : 0 < x := by linarith
  have hlog : 1 ≤ Real.log x := by
    rw [Real.le_log_iff_exp_le hx0]
    have := Real.exp_one_lt_d9
    linarith
  have h1 : x ^ t = x * x ^ (t - 1) := by
    conv_lhs => rw [show t = 1 + (t - 1) by ring]
    rw [Real.rpow_add hx0, Real.rpow_one]
  have h2 : t ≤ x ^ (t - 1) := by
    rw [Real.rpow_def_of_pos hx0]
    have := Real.add_one_le_exp (Real.log x * (t - 1))
    nlinarith
  rw [h1]
  nlinarith

theorem del_ge (D : D7) (large₂ : SizeData₂ D) {C' Cl Cg cb Cu cT CT : ℝ} (h : StandingHypotheses D large₂ C' Cl Cg cb Cu cT CT)
    (hCl : 1 ≤ Cl) : Cl * ((D.R.k : ℝ) * D.R.f) ≤ (D.s.Del : ℝ) := by
  obtain ⟨-, -, hmf, hfk, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hDel, -, -, -, -, -⟩ := h
  have hm := D.R.two_le_m
  have hf16 : 16 ≤ D.R.f := le_trans (by have := Nat.pow_le_pow_left hm 4; norm_num at this ⊢; omega) hmf
  have hk16 : 16 ≤ D.R.k := le_trans hf16 hfk
  have hL : 1 < large₂.sc.L := Real.one_lt_rpow large₂.sc.one_lt_alt large₂.sc.eps_pos
  have hf : (16 : ℝ) ≤ D.R.f := by exact_mod_cast hf16
  have hk : (16 : ℝ) ≤ D.R.k := by exact_mod_cast hk16
  have hkf : (D.R.k : ℝ) * D.R.f ≤ (D.R.k : ℝ) * D.R.f * large₂.sc.L := by
    have : 0 ≤ (D.R.k : ℝ) * D.R.f := by positivity
    nlinarith
  have h3 : (3 : ℝ) ≤ (D.R.k : ℝ) * D.R.f * large₂.sc.L := by nlinarith
  have := rpow_ge_mul h3 hCl
  calc Cl * ((D.R.k : ℝ) * D.R.f) ≤ Cl * ((D.R.k : ℝ) * D.R.f * large₂.sc.L) :=
        mul_le_mul_of_nonneg_left hkf (by linarith)
    _ ≤ ((D.R.k : ℝ) * D.R.f * large₂.sc.L) ^ Cl := this
    _ ≤ (D.s.Del : ℝ) := hDel

def ClCut (C₆ : ℝ) : ℝ := max 1 ((420 * C₆ + 48125) / 8)

theorem long_cut_num (D : D7) (large₂ : SizeData₂ D) {C' Cl Cg cb Cu cT CT : ℝ} (h : StandingHypotheses D large₂ C' Cl Cg cb Cu cT CT)
    (C₆ : ℝ) (hC6 : 0 ≤ C₆) (hCl : ClCut C₆ ≤ Cl) :
    6 * (20 * ((D.R.rS : ℝ) + 1)) ^ 3 + 6 * (20 * ((D.R.rS : ℝ) + 1)) ≤ (D.s.Del : ℝ) / 2 - 5 / 2 ∧
    C₆ * ((D.R.k : ℝ) * (20 * ((D.R.rS : ℝ) + 1)) * ((D.R.rS : ℝ) + 1) ^ 2 +
      (20 * ((D.R.rS : ℝ) + 1)) ^ 2 * ((D.R.rS : ℝ) + 1) ^ 2) ≤ (D.s.Del : ℝ) / 2 - 5 / 2 := by
  have hCl1 : 1 ≤ Cl := le_trans (le_max_left _ _) hCl
  have hCl2 : (420 * C₆ + 48125) / 8 ≤ Cl := le_trans (le_max_right _ _) hCl
  have hD := del_ge D large₂ h hCl1
  obtain ⟨-, -, hmf, hfk, -⟩ := h
  have hmR : (D.R.m : ℝ) = 2 * ((D.R.rS : ℝ) + 1) := by
    have h2 : D.R.m = 2 * D.R.rS + 2 := by
      unfold Formalism.BasicNotions.Ranks.rS; obtain ⟨a, ha⟩ := D.R.m_even; have := D.R.two_le_m; omega
    have : (D.R.m : ℝ) = 2 * (D.R.rS : ℝ) + 2 := by exact_mod_cast h2
    linarith
  have hf : (D.R.m : ℝ) ^ 4 ≤ D.R.f := by exact_mod_cast hmf
  have hk1 : (D.R.f : ℝ) ≤ D.R.k := by exact_mod_cast hfk
  have hm2 : (2 : ℝ) ≤ D.R.m := by exact_mod_cast D.R.two_le_m
  generalize hR : (D.R.rS : ℝ) + 1 = R at hmR ⊢
  generalize hk : (D.R.k : ℝ) = k at hk1 hD ⊢
  have hR1 : 1 ≤ R := by nlinarith
  have hR3 : R ^ 3 ≤ R ^ 4 := pow_le_pow_right₀ hR1 (by norm_num)
  have hRR : R ≤ R ^ 4 := by
    calc R = R ^ 1 := (pow_one R).symm
      _ ≤ R ^ 4 := pow_le_pow_right₀ hR1 (by norm_num)
  have hR4 : 1 ≤ R ^ 4 := one_le_pow₀ hR1
  have hm4 : (16 : ℝ) ≤ (D.R.m : ℝ) ^ 4 := by
    have := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) hm2 4
    norm_num at this ⊢; linarith
  have hk1' : 1 ≤ k := by linarith
  have hP1 : R ^ 4 ≤ k * R ^ 4 := by nlinarith
  have hPk : k * R ^ 3 ≤ k * R ^ 4 := by nlinarith
  have hkf : 16 * (k * R ^ 4) ≤ k * (D.R.f : ℝ) := by
    have h16 : 16 * R ^ 4 = (D.R.m : ℝ) ^ 4 := by rw [hmR]; ring
    nlinarith
  have hDel : 16 * Cl * (k * R ^ 4) ≤ (D.s.Del : ℝ) := by
    have := mul_le_mul_of_nonneg_left hkf (by linarith : (0 : ℝ) ≤ Cl)
    linarith
  have hbig : (420 * C₆ + 48125) * (k * R ^ 4) ≤ 8 * Cl * (k * R ^ 4) := by
    have hP0 : 0 ≤ k * R ^ 4 := by nlinarith
    nlinarith
  refine ⟨?_, ?_⟩
  · nlinarith
  · have : C₆ * (k * (20 * R) * R ^ 2 + (20 * R) ^ 2 * R ^ 2) ≤ C₆ * (420 * (k * R ^ 4)) := by
      apply mul_le_mul_of_nonneg_left _ hC6
      nlinarith
    nlinarith

theorem long_cut (D : D7) (large₂ : SizeData₂ D) {C' Cl Cg cb Cu cT CT : ℝ} (h : StandingHypotheses D large₂ C' Cl Cg cb Cu cT CT)
    (C₆ : ℝ) (hC6 : 0 ≤ C₆) (hCl : ClCut C₆ ≤ Cl)
    [IsCMField D.host.E] {Wp Wq : InfinitePlace D.host.E → Type}
    [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
    [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)]
    (S : Formalism.FourierDecayAlt.C.HidaSetting D.host.E Wp Wq) (hk : S.G.k = D.R.k) (hr : S.G.r = D.R.rS)
    (hDel : S.G.Del = (D.s.Del : ℝ)) (v : Fin S.f) :
    6 * (S.Ntop : ℝ) ^ 3 + 6 * S.Ntop ≤ S.cutHi v - S.cutLo v ∧
    C₆ * ((S.G.k : ℝ) * S.Ntop * ((S.G.r : ℝ) + 1) ^ 2 + (S.Ntop : ℝ) ^ 2 * ((S.G.r : ℝ) + 1) ^ 2) ≤
      S.cutHi v - S.cutLo v := by
  rw [cut_len, ntop_eq, hk, hr, hDel]
  exact long_cut_num D large₂ h C₆ hC6 hCl

section Grids

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Sz

def GridsAt (c : Cfg) (l N : ℕ) (grid : ℕ → Finset ℝ) (grid1 : Finset ℝ) : Prop :=
  6 * (N : ℝ) ^ 3 + 6 * N ≤ (c.Del / 2 - c.v l) - (5 / 2 - c.v l) ∧
  (∀ a, ∀ y ∈ grid a, 1 ≤ a ∧ a ≤ N ∧ C.gridL (5 / 2 - c.v l) (c.Del / 2 - c.v l) N a ≤ y ∧
      y ≤ C.gridL (5 / 2 - c.v l) (c.Del / 2 - c.v l) N a +
        ((c.Del / 2 - c.v l) - (5 / 2 - c.v l)) / (6 * N) - 1) ∧
  (∀ y ∈ grid1, y ∈ c.cutIntervalLong l N ∧ y + 1 ∈ c.cutIntervalLong l N) ∧
  (∀ y ∈ grid1, ∀ y' ∈ grid1, y ≠ y' → ∀ e ∈ ({0, 1} : Finset ℝ), ∀ e' ∈ ({0, 1} : Finset ℝ),
      (N : ℝ) ^ 2 / 8 ≤ |(y + e) - (y' + e')|) ∧
  (∀ y ∈ grid1, ∀ a, ∀ y' ∈ grid a, ∀ e ∈ ({0, 1} : Finset ℝ), ∀ e' ∈ ({0, 1} : Finset ℝ),
      (N : ℝ) ^ 2 + 1 ≤ |(y + e) - (y' + e')|) ∧
  (∀ y, ((∃ a, y ∈ grid a) ∨ y ∈ grid1) →
      y ∈ c.cutI l ∧ y + 1 ∈ c.cutI l ∧ c.P y ≠ 0 ∧ c.P (y + 1) ≠ 0)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
  [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
  [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)]

theorem gridsOK_iff (S : C.HidaSetting E Wp Wq) :
    C.GridsOK S ↔ ∀ v, GridsAt (S.G.place (S.pl v)) S.l S.Ntop (S.grid v) (S.grid1 v) := Iff.rfl

theorem exists_good (c : Cfg) {A B : ℝ} (h : A < B) :
    ∃ y, A ≤ y ∧ y ≤ B ∧ c.P y ≠ 0 ∧ c.P (y + 1) ≠ 0 := by
  classical
  let bad : Finset ℝ := (Finset.Icc 1 (c.k + c.m - 1)).image (fun s => -c.lam s) ∪
    (Finset.Icc 1 (c.k + c.m - 1)).image (fun s => -c.lam s - 1)
  obtain ⟨y, hy, hyb⟩ := (Set.Icc_infinite h).exists_notMem_finset bad
  refine ⟨y, hy.1, hy.2, ?_, ?_⟩
  · intro h0
    unfold Cfg.P at h0
    obtain ⟨s, hs, hs0⟩ := Finset.prod_eq_zero_iff.mp h0
    exact hyb (Finset.mem_union_left _ (Finset.mem_image.mpr ⟨s, hs, by linarith⟩))
  · intro h0
    unfold Cfg.P at h0
    obtain ⟨s, hs, hs0⟩ := Finset.prod_eq_zero_iff.mp h0
    exact hyb (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨s, hs, by linarith⟩))

def pickIn (c : Cfg) (A B : ℝ) : ℝ :=
  Classical.epsilon (fun y => A ≤ y ∧ y ≤ B ∧ c.P y ≠ 0 ∧ c.P (y + 1) ≠ 0)

theorem pickIn_spec (c : Cfg) {A B : ℝ} (h : A < B) :
    A ≤ pickIn c A B ∧ pickIn c A B ≤ B ∧ c.P (pickIn c A B) ≠ 0 ∧ c.P (pickIn c A B + 1) ≠ 0 :=
  Classical.epsilon_spec (exists_good c h)

def gridOf (c : Cfg) (l N : ℕ) (a : ℕ) : Finset ℝ :=
  if 1 ≤ a ∧ a ≤ N then
    {pickIn c (C.gridL (5 / 2 - c.v l) (c.Del / 2 - c.v l) N a)
      (C.gridL (5 / 2 - c.v l) (c.Del / 2 - c.v l) N a + ((c.Del / 2 - c.v l) - (5 / 2 - c.v l)) / (6 * N) - 1)}
  else ∅

def node1 (c : Cfg) (l N j : ℕ) : ℝ :=
  pickIn c (5 / 2 - c.v l + (j : ℝ) * (N : ℝ) ^ 2) (5 / 2 - c.v l + (j : ℝ) * (N : ℝ) ^ 2 + 1 / 2)

def grid1Of (c : Cfg) (l N : ℕ) : Finset ℝ := (Finset.range N).image (node1 c l N)

theorem first_level_node_spec (c : Cfg) (l N j : ℕ) :
    5 / 2 - c.v l + (j : ℝ) * (N : ℝ) ^ 2 ≤ node1 c l N j ∧
      node1 c l N j ≤ 5 / 2 - c.v l + (j : ℝ) * (N : ℝ) ^ 2 + 1 / 2 ∧
      c.P (node1 c l N j) ≠ 0 ∧ c.P (node1 c l N j + 1) ≠ 0 :=
  pickIn_spec c (by linarith)

theorem first_level_nodes_separated (c : Cfg) (l N : ℕ) {j j' : ℕ} (h : j < j') :
    (N : ℝ) ^ 2 - 1 / 2 ≤ node1 c l N j' - node1 c l N j := by
  have h1 := first_level_node_spec c l N j
  have h2 := first_level_node_spec c l N j'
  have hj : (j : ℝ) + 1 ≤ j' := by exact_mod_cast h
  have hN : 0 ≤ (N : ℝ) ^ 2 := by positivity
  nlinarith [h1.2.1, h2.1]

theorem gridsAt_of (c : Cfg) (l N : ℕ) (hN : 2 ≤ N) (hlen : 6 * (N : ℝ) ^ 3 + 6 * N ≤ c.Del / 2 - 5 / 2) :
    GridsAt c l N (gridOf c l N) (grid1Of c l N) := by
  have hN' : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < N := by linarith
  set α : ℝ := 5 / 2 - c.v l with hα
  set β : ℝ := c.Del / 2 - c.v l with hβ
  have hlenab : β - α = c.Del / 2 - 5 / 2 := by rw [hα, hβ]; ring
  set q : ℝ := (β - α) / (6 * N) with hq
  have hq6 : β - α = 6 * N * q := by rw [hq]; field_simp
  have hq1 : (N : ℝ) ^ 2 + 1 ≤ q := by
    rw [hq, le_div_iff₀ (by positivity)]
    nlinarith
  have hq2 : (1 : ℝ) < q := by nlinarith
  have hgL : ∀ a : ℕ, C.gridL α β N a = α + 2 * N * q + (2 * (a : ℝ) - 2) * q := by
    intro a
    unfold C.gridL
    rw [← hq, hq6]
    field_simp
    ring

  have hgrid : ∀ a, ∀ y ∈ gridOf c l N a, 1 ≤ a ∧ a ≤ N ∧ C.gridL α β N a ≤ y ∧
      y ≤ C.gridL α β N a + q - 1 := by
    intro a y hy
    unfold gridOf at hy
    split_ifs at hy with ha
    · rw [Finset.mem_singleton] at hy
      subst hy
      have := pickIn_spec c (A := C.gridL α β N a) (B := C.gridL α β N a + q - 1) (by linarith [hq2])
      exact ⟨ha.1, ha.2, this.1, this.2.1⟩
    · simp at hy
  have hgridP : ∀ a, ∀ y ∈ gridOf c l N a, c.P y ≠ 0 ∧ c.P (y + 1) ≠ 0 := by
    intro a y hy
    unfold gridOf at hy
    split_ifs at hy with ha
    · rw [Finset.mem_singleton] at hy
      subst hy
      have := pickIn_spec c (A := C.gridL α β N a) (B := C.gridL α β N a + q - 1) (by linarith [hq2])
      exact ⟨this.2.2.1, this.2.2.2⟩
    · simp at hy

  have hgridB : ∀ a, ∀ y ∈ gridOf c l N a, α + 2 * N * q ≤ y ∧ y + 1 ≤ α + 4 * N * q := by
    intro a y hy
    obtain ⟨ha1, haN, hlo, hhi⟩ := hgrid a y hy
    rw [hgL] at hlo hhi
    have ha1' : (1 : ℝ) ≤ a := by exact_mod_cast ha1
    have haN' : (a : ℝ) ≤ N := by exact_mod_cast haN
    have hq0 : 0 ≤ q := by nlinarith
    constructor <;> nlinarith

  have hg1 : ∀ y ∈ grid1Of c l N, α ≤ y ∧ y + 1 ≤ α + (N : ℝ) ^ 3 - 5 / 2 ∧ c.P y ≠ 0 ∧ c.P (y + 1) ≠ 0 := by
    intro y hy
    unfold grid1Of at hy
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hy
    have hs := first_level_node_spec c l N j
    have hjN : (j : ℝ) + 1 ≤ N := by
      have := Finset.mem_range.mp hj
      exact_mod_cast this
    have hj0 : (0 : ℝ) ≤ j := by positivity
    refine ⟨by nlinarith [hs.1], ?_, hs.2.2.1, hs.2.2.2⟩
    have : (j : ℝ) * (N : ℝ) ^ 2 ≤ ((N : ℝ) - 1) * (N : ℝ) ^ 2 := by
      apply mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    nlinarith [hs.2.1]
  have hlen' : 6 * (N : ℝ) ^ 3 + 6 * N ≤ 6 * N * q := by rw [← hq6, hlenab]; exact hlen
  have hq3 : (N : ℝ) ^ 2 + 1 ≤ q := hq1
  have hqpos : 0 < q := by nlinarith
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hlenab]; exact hlen
  · intro a y hy
    exact hgrid a y hy
  · intro y hy
    obtain ⟨h1, h2, -, -⟩ := hg1 y hy
    simp only [Cfg.cutIntervalLong, Set.mem_ofPred_eq]
    rw [hα] at h1 h2
    refine ⟨⟨by linarith, by linarith⟩, by linarith, by linarith⟩
  · intro y hy y' hy' hne e he e' he'
    unfold grid1Of at hy hy'
    obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hy
    obtain ⟨j', -, rfl⟩ := Finset.mem_image.mp hy'
    have hjj : j ≠ j' := fun h => hne (by rw [h])
    have he1 : e = 0 ∨ e = 1 := by simpa using he
    have he1' : e' = 0 ∨ e' = 1 := by simpa using he'
    have hN8 : (N : ℝ) ^ 2 / 8 + 1 ≤ (N : ℝ) ^ 2 - 1 / 2 := by nlinarith
    rcases Nat.lt_or_gt_of_ne hjj with h | h
    · have := first_level_nodes_separated c l N h
      rw [abs_sub_comm]
      rcases he1 with rfl | rfl <;> rcases he1' with rfl | rfl <;>
        · rw [abs_of_nonneg (by linarith)]; linarith
    · have := first_level_nodes_separated c l N h
      rcases he1 with rfl | rfl <;> rcases he1' with rfl | rfl <;>
        · rw [abs_of_nonneg (by linarith)]; linarith
  · intro y hy a y' hy' e he e' he'
    obtain ⟨h1, h2, -, -⟩ := hg1 y hy
    obtain ⟨h3, -⟩ := hgridB a y' hy'
    have he1 : e = 0 ∨ e = 1 := by simpa using he
    have he1' : e' = 0 ∨ e' = 1 := by simpa using he'
    have hN3 : (N : ℝ) ^ 2 + 1 + 1 ≤ (N : ℝ) ^ 3 := by nlinarith
    have hgap : (N : ℝ) ^ 3 + 5 / 2 ≤ 2 * N * q - (N : ℝ) ^ 3 := by nlinarith
    rw [abs_sub_comm]
    rcases he1 with rfl | rfl <;> rcases he1' with rfl | rfl <;>
      · rw [abs_of_nonneg (by linarith)]; linarith
  · intro y hy
    have hβq : β = α + 6 * N * q := by linarith
    simp only [Cfg.cutI, Set.mem_ofPred_eq]
    rcases hy with ⟨a, ha⟩ | hy
    · obtain ⟨h1, h2⟩ := hgridB a y ha
      obtain ⟨hP1, hP2⟩ := hgridP a y ha
      rw [hα] at h1 h2
      rw [hβ] at hβq
      refine ⟨⟨by linarith, by nlinarith⟩, ⟨by linarith, by nlinarith⟩, hP1, hP2⟩
    · obtain ⟨h1, h2, hP1, hP2⟩ := hg1 y hy
      have hN6 : (N : ℝ) ^ 3 ≤ 6 * N * q := by nlinarith
      rw [hα] at h1 h2
      rw [hβ] at hβq
      refine ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩, hP1, hP2⟩

theorem grids_card (c : Cfg) (l N : ℕ) (hN : 1 ≤ N) :
    (grid1Of c l N).card = N ∧ ∀ a, 1 ≤ a → a ≤ N → (gridOf c l N a).card = 1 := by
  refine ⟨?_, fun a h1 h2 => by simp [gridOf, h1, h2]⟩
  unfold grid1Of
  rw [Finset.card_image_of_injective _ ?_, Finset.card_range]
  intro j j' h
  by_contra hne
  have hN' : (1 : ℝ) ≤ N := by exact_mod_cast hN
  rcases Nat.lt_or_gt_of_ne hne with hl | hl
  · have := first_level_nodes_separated c l N hl; rw [h] at this; nlinarith
  · have := first_level_nodes_separated c l N hl; rw [h] at this; nlinarith

theorem gridsOK_of (S : C.HidaSetting E Wp Wq) (hlen : 6 * (S.Ntop : ℝ) ^ 3 + 6 * S.Ntop ≤ S.G.Del / 2 - 5 / 2)
    (hg : ∀ v, S.grid v = gridOf (S.G.place (S.pl v)) S.l S.Ntop)
    (hg1 : ∀ v, S.grid1 v = grid1Of (S.G.place (S.pl v)) S.l S.Ntop) : C.GridsOK S := by
  rw [gridsOK_iff]
  intro v
  rw [hg, hg1]
  have hN : 2 ≤ S.Ntop := by unfold C.HidaSetting.Ntop C.Kst; omega
  exact gridsAt_of _ _ _ hN hlen

theorem gridsOK_hyp (D : D7) (large₂ : SizeData₂ D) {C' Cl Cg cb Cu cT CT : ℝ} (h : StandingHypotheses D large₂ C' Cl Cg cb Cu cT CT)
    (hCl : ClCut 0 ≤ Cl) [IsCMField D.host.E] {Wp Wq : InfinitePlace D.host.E → Type}
    [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
    [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)]
    (S : C.HidaSetting D.host.E Wp Wq) (hr : S.G.r = D.R.rS) (hDel : S.G.Del = (D.s.Del : ℝ))
    (hg : ∀ v, S.grid v = gridOf (S.G.place (S.pl v)) S.l S.Ntop)
    (hg1 : ∀ v, S.grid1 v = grid1Of (S.G.place (S.pl v)) S.l S.Ntop) : C.GridsOK S := by
  refine gridsOK_of S ?_ hg hg1
  rw [ntop_eq, hr, hDel]
  exact (long_cut_num D large₂ h 0 le_rfl hCl).1

end Grids

section TransportedAlt

open Formalism.FourierDecayAlt

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
  [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
  [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)]

theorem thr_nonneg (S : C.HidaSetting E Wp Wq) (hCA : 0 ≤ S.CA) (hg : 0 < S.G.g) (hv : 0 < S.G.v) (hI : 0 < S.G.lenI) :
    (∀ b v, 0 ≤ S.base.szD b v) ∧ (∀ b s v, 0 ≤ S.base.szL b s v) := by
  have hM := Formalism.FourierDecayAlt.P.threshold_mono
  refine ⟨fun b v => ?_, fun b s v => ?_⟩
  · change 0 ≤ J.thrS S.G S.CA S.de S.de' S.T S.T' S.l b 1 (S.pl v)
    exact (hM _ S.G S.CA S.CA S.de S.de' S.T S.T' S.l hCA le_rfl hg hv hI b 1 (S.pl v)).1
  · change 0 ≤ (if b + s ≤ S.G.r + 1 then J.thrS S.G S.CA S.de S.de' S.T S.T' S.l b (s + 1) (S.pl v)
      else 2 * J.thrP S.G S.CA S.de S.de' S.T S.T' S.l b (S.pl v))
    have h := hM _ S.G S.CA S.CA S.de S.de' S.T S.T' S.l hCA le_rfl hg hv hI b (s + 1) (S.pl v)
    split_ifs
    · exact h.1
    · linarith [h.2.2.1]

theorem thresholdsWave_self (S : C.HidaSetting E Wp Wq) (hCA : 0 ≤ S.CA) (hg : 0 < S.G.g) (hv : 0 < S.G.v)
    (hI : 0 < S.G.lenI) : JC.HidaCurvatureBarriers S (fun i v => S.base.szD i v) :=
  fun i _ _ v => ⟨(thr_nonneg S hCA hg hv hI).1 i v, le_rfl⟩

theorem thresholdsLift_self (S : C.HidaSetting E Wp Wq) (hCA : 0 ≤ S.CA) (hg : 0 < S.G.g) (hv : 0 < S.G.v)
    (hI : 0 < S.G.lenI) :
    JC.ThresholdsLift S (fun b s v => S.base.szL b s v) (fun b s v => S.base.szL b s v / 2) := by
  have h := (thr_nonneg S hCA hg hv hI).2
  refine ⟨fun b s _ _ _ v => ⟨h b s v, le_rfl⟩, fun s _ _ v => ⟨by linarith [h (S.G.r + 2 - s) s v], by ring_nf; rfl⟩⟩

theorem glob_pos (D : D7) (large₂ : SizeData₂ D) {C' Cl Cg cb Cu cT CT : ℝ} (h : StandingHypotheses D large₂ C' Cl Cg cb Cu cT CT)
    (hCl : ClCut 0 ≤ Cl) (S : C.HidaSetting E Wp Wq) (hr : S.G.r = D.R.rS) (hDel : S.G.Del = (D.s.Del : ℝ))
    (hv : S.G.v = D.host.v) (hg1 : S.G.g1 = D.host.g 0) (hg2 : S.G.g2 = D.host.g 1) :
    0 < S.G.g ∧ 0 < S.G.v ∧ 0 < S.G.lenI := by
  have hc := (long_cut_num D large₂ h 0 le_rfl hCl).1
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hv1, -⟩ := h
  have hp := g_pos D
  refine ⟨?_, ?_, ?_⟩
  · unfold Sz.Glob.g
    rw [hg1, hg2]
    exact mul_pos (by exact_mod_cast hp.1) (by exact_mod_cast hp.2)
  · rw [hv]; linarith
  · unfold Sz.Glob.lenI
    rw [hDel]
    have : (0 : ℝ) < 6 * (20 * ((D.R.rS : ℝ) + 1)) ^ 3 + 6 * (20 * ((D.R.rS : ℝ) + 1)) := by positivity
    linarith

theorem position_bounds {k l : ℕ} (h1 : 1 ≤ l) (h2 : l + 2 ≤ k) : 1 ≤ l ∧ l ≤ k := ⟨h1, by omega⟩

end TransportedAlt

end Formalism.L2.SG.Pf.CarrierSz
