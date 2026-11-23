import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.CarrierSizes
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ChebyshevExtremalPolynomials
import Formalism.HermitianCurvature.HermitianCurvatureProofs.GramProductIdentities

noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S

namespace Formalism.L2.SG.Pf.CarrierSz

section GridsCh

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Sz

theorem chebPt_mem (α β : ℝ) (h : α ≤ β) (n : ℕ) (j : Fin (n + 1)) :
    α ≤ Formalism.SA.C.chebPt α β n j ∧ Formalism.SA.C.chebPt α β n j ≤ β := by
  unfold Formalism.SA.C.chebPt
  have h1 := Real.neg_one_le_cos (Real.pi * (j : ℕ) / n)
  have h2 := Real.cos_le_one (Real.pi * (j : ℕ) / n)
  constructor <;> nlinarith

def gridCh (c : Cfg) (l N R : ℕ) (a : ℕ) : Finset ℝ :=
  if 1 ≤ a ∧ a ≤ N then
    (Finset.Icc 1 (max 1 R)).biUnion fun n => Finset.univ.image
      (Formalism.SA.C.chebPt (C.gridL (5 / 2 - c.v l) (c.Del / 2 - c.v l) N a)
        (C.gridL (5 / 2 - c.v l) (c.Del / 2 - c.v l) N a + ((c.Del / 2 - c.v l) - (5 / 2 - c.v l)) / (6 * N) - 1) n)
  else ∅

theorem P_ne_cut (c : Cfg) (hDel : 0 < c.Del) (hv0 : 0 ≤ c.vlast) (hb : ∀ j, 1 ≤ j → j ≤ c.m → 1 ≤ c.b j)
    (l : ℕ) (hl : l + 2 ≤ c.k) (Y : ℝ) (hY : Y ∈ c.cutI l) : c.P Y ≠ 0 := by
  obtain ⟨hY1, hY2⟩ := hY
  unfold Cfg.P
  rw [Finset.prod_ne_zero_iff]
  intro s hs h0
  obtain ⟨hs1, hs2⟩ := Finset.mem_Icc.mp hs
  have hkl : (l : ℝ) + 2 ≤ c.k := by exact_mod_cast hl
  unfold Cfg.lam at h0
  split_ifs at h0 with hsk
  · unfold Cfg.v at h0 hY1 hY2
    by_cases hsl : s ≤ l
    · have : (s : ℝ) ≤ l := by exact_mod_cast hsl
      nlinarith
    · have : (l : ℝ) + 1 ≤ s := by exact_mod_cast (by omega : l + 1 ≤ s)
      nlinarith
  · have hbj := hb (s + 1 - c.k) (by omega) (by omega)
    unfold Cfg.v at hY2
    nlinarith

theorem gridCh_len (c : Cfg) (l N : ℕ) (hN : 3 ≤ N) (hlen : 6 * (N : ℝ) ^ 3 + 6 * N ≤ c.Del / 2 - 5 / 2) :
    ((c.Del / 2 - c.v l) - (5 / 2 - c.v l)) / (7 * N) ≤ ((c.Del / 2 - c.v l) - (5 / 2 - c.v l)) / (6 * N) - 1 := by
  have hN' : (3 : ℝ) ≤ N := by exact_mod_cast hN
  have hI : (c.Del / 2 - c.v l) - (5 / 2 - c.v l) = c.Del / 2 - 5 / 2 := by ring
  rw [hI]
  have h9 : (9 : ℝ) ≤ (N : ℝ) ^ 2 := by nlinarith
  have h42 : 42 * (N : ℝ) ≤ c.Del / 2 - 5 / 2 := by
    nlinarith [mul_le_mul_of_nonneg_left h9 (by positivity : (0 : ℝ) ≤ 6 * (N : ℝ))]
  rw [div_le_iff₀ (by positivity)]
  have : (c.Del / 2 - 5 / 2) / (6 * N) * (7 * N) = (7 / 6) * (c.Del / 2 - 5 / 2) := by field_simp
  rw [sub_mul, this]
  nlinarith

def RichAt (c : Cfg) (l N R : ℕ) (grid : ℕ → Finset ℝ) (grid1 : Finset ℝ) : Prop :=
  N ≤ grid1.card ∧ ∀ a, 1 ≤ a → a ≤ N → ∀ n ≤ R, ∃ y : Fin (n + 1) → ℝ, Function.Injective y ∧
    (∀ j, y j ∈ grid a) ∧
    ∑ j, |Formalism.FourierDecayAlt.F7.lagCo y j| ≤ (28 * N / ((c.Del / 2 - c.v l) - (5 / 2 - c.v l))) ^ n

theorem richAt_ch (c : Cfg) (l N R : ℕ) (hN : 3 ≤ N) (hlen : 6 * (N : ℝ) ^ 3 + 6 * N ≤ c.Del / 2 - 5 / 2) :
    RichAt c l N R (gridCh c l N R) (grid1Of c l N) := by
  have hN' : (3 : ℝ) ≤ N := by exact_mod_cast hN
  have hI : (c.Del / 2 - c.v l) - (5 / 2 - c.v l) = c.Del / 2 - 5 / 2 := by ring
  have hIpos : 0 < c.Del / 2 - 5 / 2 := by
    have : 0 < 6 * (N : ℝ) ^ 3 + 6 * N := by positivity
    linarith
  refine ⟨(grids_card c l N (by omega)).1.ge, fun a ha1 haN n hn => ?_⟩
  set α := C.gridL (5 / 2 - c.v l) (c.Del / 2 - c.v l) N a
  set ℓ := ((c.Del / 2 - c.v l) - (5 / 2 - c.v l)) / (6 * N) - 1 with hℓ
  have hℓ7 := gridCh_len c l N hN hlen
  have hℓpos : 0 < ℓ := lt_of_lt_of_le (by rw [hI]; positivity) hℓ7
  have hmem : ∀ m, 1 ≤ m → m ≤ max 1 R → ∀ j : Fin (m + 1), Formalism.SA.C.chebPt α (α + ℓ) m j ∈ gridCh c l N R a := by
    intro m hm1 hm2 j
    unfold gridCh
    rw [if_pos ⟨ha1, haN⟩]
    refine Finset.mem_biUnion.mpr ⟨m, Finset.mem_Icc.mpr ⟨hm1, hm2⟩, Finset.mem_image.mpr ⟨j, Finset.mem_univ _, ?_⟩⟩
    rw [show α + ℓ = α + ((c.Del / 2 - c.v l) - (5 / 2 - c.v l)) / (6 * N) - 1 by rw [hℓ]; ring]
  rcases Nat.eq_zero_or_pos n with rfl | hn0
  · refine ⟨fun _ => Formalism.SA.C.chebPt α (α + ℓ) 1 0, fun i j _ => Fin.ext (by have := i.2; have := j.2; omega), fun j => hmem 1 le_rfl
      (le_max_left _ _) 0, ?_⟩
    simp [Formalism.FourierDecayAlt.F7.lagCo]
  · have hsharp := Formalism.FourierDecayAlt.P.chebyshev_bound_sharp α (α + ℓ) n (by linarith) hn0
    refine ⟨Formalism.SA.C.chebPt α (α + ℓ) n, hsharp.1, fun j => hmem n hn0 (le_trans hn (le_max_right _ _)) j, ?_⟩
    rw [hsharp.2, show α + ℓ - α = ℓ by ring]
    have h4 : 4 / ℓ ≤ 28 * N / ((c.Del / 2 - c.v l) - (5 / 2 - c.v l)) := by
      rw [hI] at hℓ7 ⊢
      rw [div_le_div_iff₀ hℓpos hIpos]
      have := mul_le_mul_of_nonneg_left hℓ7 (by positivity : (0 : ℝ) ≤ 28 * N)
      rw [mul_div_assoc'] at this
      have e : 28 * (N : ℝ) * (c.Del / 2 - 5 / 2) / (7 * N) = 4 * (c.Del / 2 - 5 / 2) := by field_simp; ring
      rw [e] at this
      rw [hℓ, hI]
      linarith
    calc (1 / 2 : ℝ) * (4 / ℓ) ^ n ≤ 1 * (4 / ℓ) ^ n := by
          apply mul_le_mul_of_nonneg_right (by norm_num) (by positivity)
      _ = (4 / ℓ) ^ n := one_mul _
      _ ≤ _ := pow_le_pow_left₀ (by positivity) h4 n

theorem gridsAtCh (c : Cfg) (l N R : ℕ) (hN : 2 ≤ N) (hlen : 6 * (N : ℝ) ^ 3 + 6 * N ≤ c.Del / 2 - 5 / 2)
    (hP : ∀ Y ∈ c.cutI l, c.P Y ≠ 0) :
    GridsAt c l N (gridCh c l N R) (grid1Of c l N) := by
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

  have hgrid : ∀ a, ∀ y ∈ gridCh c l N R a, 1 ≤ a ∧ a ≤ N ∧ C.gridL α β N a ≤ y ∧
      y ≤ C.gridL α β N a + q - 1 := by
    intro a y hy
    unfold gridCh at hy
    split_ifs at hy with ha
    · obtain ⟨n, -, hyn⟩ := Finset.mem_biUnion.mp hy
      obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hyn
      have hm := chebPt_mem (C.gridL α β N a) (C.gridL α β N a + q - 1) (by linarith [hq2]) n j
      exact ⟨ha.1, ha.2, hm.1, hm.2⟩
    · simp at hy

  have hgridB : ∀ a, ∀ y ∈ gridCh c l N R a, α + 2 * N * q ≤ y ∧ y + 1 ≤ α + 4 * N * q := by
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
      rw [hα] at h1 h2
      rw [hβ] at hβq
      have hc1 : y ∈ c.cutI l := ⟨by linarith, by nlinarith⟩
      have hc2 : y + 1 ∈ c.cutI l := ⟨by linarith, by nlinarith⟩
      exact ⟨hc1, hc2, hP _ hc1, hP _ hc2⟩
    · obtain ⟨h1, h2, hP1, hP2⟩ := hg1 y hy
      have hN6 : (N : ℝ) ^ 3 ≤ 6 * N * q := by nlinarith
      rw [hα] at h1 h2
      rw [hβ] at hβq
      refine ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩, hP1, hP2⟩

end GridsCh

section GridsChS

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Sz

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
  [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
  [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)]

theorem gridsOK_ch (S : C.HidaSetting E Wp Wq) (hlen : 6 * (S.Ntop : ℝ) ^ 3 + 6 * S.Ntop ≤ S.G.Del / 2 - 5 / 2)
    (hg : ∀ v, S.grid v = gridCh (S.G.place (S.pl v)) S.l S.Ntop (2 * S.G.r))
    (hg1 : ∀ v, S.grid1 v = grid1Of (S.G.place (S.pl v)) S.l S.Ntop)
    (hP : ∀ v, ∀ Y ∈ (S.G.place (S.pl v)).cutI S.l, (S.G.place (S.pl v)).P Y ≠ 0) : C.GridsOK S := by
  rw [gridsOK_iff]
  intro v
  rw [hg, hg1]
  have hN : 2 ≤ S.Ntop := by unfold C.HidaSetting.Ntop C.Kst; omega
  exact gridsAtCh _ _ _ _ hN hlen (hP v)

theorem gridsRich_ch (S : C.HidaSetting E Wp Wq) (hlen : 6 * (S.Ntop : ℝ) ^ 3 + 6 * S.Ntop ≤ S.G.Del / 2 - 5 / 2)
    (hg : ∀ v, S.grid v = gridCh (S.G.place (S.pl v)) S.l S.Ntop (2 * S.G.r))
    (hg1 : ∀ v, S.grid1 v = grid1Of (S.G.place (S.pl v)) S.l S.Ntop) :
    ∀ v, S.Ntop ≤ (S.grid1 v).card ∧ ∀ a, 1 ≤ a → a ≤ S.Ntop → ∀ n ≤ 2 * S.G.r,
      ∃ y : Fin (n + 1) → ℝ, Function.Injective y ∧ (∀ j, y j ∈ S.grid v a) ∧
        ∑ j, |Formalism.FourierDecayAlt.F7.lagCo y j| ≤ (28 * S.Ntop / (S.cutHi v - S.cutLo v)) ^ n := by
  intro v
  rw [hg, hg1]
  have hN : 3 ≤ S.Ntop := by unfold C.HidaSetting.Ntop C.Kst; omega
  exact richAt_ch _ _ _ _ hN hlen

theorem pNe_of (S : C.HidaSetting E Wp Wq) (hDel : 0 < S.G.Del) (hv0 : ∀ x, 0 ≤ S.G.vlast x)
    (hb : ∀ x j, 1 ≤ j → j ≤ 2 * S.G.r + 2 → 1 ≤ S.G.b x j) (hl : S.l + 2 ≤ S.G.k) :
    ∀ v, ∀ Y ∈ (S.G.place (S.pl v)).cutI S.l, (S.G.place (S.pl v)).P Y ≠ 0 :=
  fun v Y hY => P_ne_cut (S.G.place (S.pl v)) hDel (hv0 _) (fun j h1 h2 => hb _ j h1 h2) S.l hl Y hY

end GridsChS

end Formalism.L2.SG.Pf.CarrierSz
