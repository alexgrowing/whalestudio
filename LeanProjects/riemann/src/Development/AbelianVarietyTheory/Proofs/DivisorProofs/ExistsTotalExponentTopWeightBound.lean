import Mathlib
import Formalism.PieriBlockIdeals.PieriColumnMinors.RecursionInclusionExceptional
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeylLatticeExactExponentBlockCut
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BrPairFApply
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.InfClassAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueIsFunForm
import Formalism.SharpRestriction.Divisibility.PrimeDegreeVariant
import Formalism.PieriBlockIdeals.StatementLA
import Formalism.MirabolicMackeyTheory.MirabolicMackeyProofs.RamBasic
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAt

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim GlobalTheory.TestLat GlobalTheory.SumSize
open Formalism.DivisionValues (vw lw)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.FinSize

open Finset

private def extN {n : ℕ} (ν : Fin n → ℕ) : ℕ → ℕ := fun i => if h : i < n then ν ⟨i, h⟩ else 0

private theorem res_extN {n : ℕ} (ν : Fin n → ℕ) : Formalism.CohomologicalDescent.LD.res n (extN ν) = ν := by
  funext i
  simp [Formalism.CohomologicalDescent.LD.res, extN, i.2]

private theorem exZ_le_of_width {n : ℕ} (ν : Fin n → ℕ) (hν : Antitone ν) (w : ℕ)
    (hw : ∀ a : Fin n, ν a + (n - 1 - a) ≤ w) (l : ℕ) (hl : l.Prime) :
    Formalism.CohomologicalDescent.LA.exZ n n le_rfl ν l ≤ n.choose 2 * Nat.log l w ∧
      (w < l → Formalism.CohomologicalDescent.LA.exZ n n le_rfl ν l = 0) := by
  have hanti : Antitone (Formalism.CohomologicalDescent.LD.res n (extN ν)) := by rw [res_extN]; exact hν
  have hI : ∀ a < n, (0 : ℤ) ≤ Formalism.CohomologicalDescent.UnitNormBounds.UN n (extN ν) a ∧
      Formalism.CohomologicalDescent.UnitNormBounds.UN n (extN ν) a ≤ 0 + (w : ℤ) := by
    intro a ha
    have h := hw ⟨a, ha⟩
    simp only [Formalism.CohomologicalDescent.UnitNormBounds.UN, extN, ha, dif_pos]
    simp only at h
    constructor <;> omega
  have h := Formalism.CohomologicalDescent.E.exIntervalLt_of_exCut GlobalTheory.LeviCut.exCut n (extN ν) hanti l hl 0 w hI
  rwa [res_extN] at h

private theorem natW_wtOf_add_le (n : ℕ) (E : Finset ℚ) (lo hi : ℝ) (hE : ∀ x ∈ E, lo ≤ (x : ℝ) ∧ (x : ℝ) ≤ hi) (w : ℕ)
    (hw : hi - lo ≤ w) (hn : n - 1 ≤ w) (a : Fin n) :
    (GlobalTheory.FunObj.wtOf n E).natW a + (n - 1 - a) ≤ w := by
  have hpos : 0 < n := lt_of_le_of_lt (Nat.zero_le _) a.2
  have ha := a.2
  unfold GlobalTheory.FunObj.wtOf
  split_ifs with h
  · obtain ⟨z, hz⟩ := GlobalTheory.SignedHC.highestWeight_int h.1 h.2 a
    obtain ⟨z', hz'⟩ := GlobalTheory.SignedHC.highestWeight_int h.1 h.2 ⟨n - 1, by omega⟩
    simp only [Formalism.BasicNotions.DomWeight.natW, Formalism.BasicNotions.DomWeight.detShift, dif_pos hpos, hz, hz', Int.floor_intCast]
    have e1 : (z : ℚ) = GlobalTheory.SignedHC.descEnum E h.1 a - (((n : ℚ) - 1) / 2 - ((a : ℕ) : ℚ)) := hz.symm
    have e2 : (z' : ℚ) = GlobalTheory.SignedHC.descEnum E h.1 ⟨n - 1, by omega⟩ -
        (((n : ℚ) - 1) / 2 - ((n - 1 : ℕ) : ℚ)) := hz'.symm
    have e1R : (z : ℝ) = (GlobalTheory.SignedHC.descEnum E h.1 a : ℝ) - (((n : ℝ) - 1) / 2 - ((a : ℕ) : ℝ)) := by
      have := congrArg (fun q : ℚ => (q : ℝ)) e1
      push_cast at this
      exact this
    have e2R : (z' : ℝ) = (GlobalTheory.SignedHC.descEnum E h.1 ⟨n - 1, by omega⟩ : ℝ) -
        (((n : ℝ) - 1) / 2 - ((n - 1 : ℕ) : ℝ)) := by
      have := congrArg (fun q : ℚ => (q : ℝ)) e2
      push_cast at this
      exact this
    have m1 := hE _ (GlobalTheory.SignedHC.descEnum_mem E h.1 a)
    have m2 := hE _ (GlobalTheory.SignedHC.descEnum_mem E h.1 ⟨n - 1, by omega⟩)
    have c1 : ((n - 1 - (a : ℕ) : ℕ) : ℝ) + 1 + ((a : ℕ) : ℝ) = n := by
      have : n - 1 - (a : ℕ) + 1 + (a : ℕ) = n := by omega
      exact_mod_cast this
    have c2 : ((n - 1 : ℕ) : ℝ) + 1 = n := by
      have : n - 1 + 1 = n := by omega
      exact_mod_cast this
    have key : (((z - z' : ℤ) : ℝ)) + ((n - 1 - (a : ℕ) : ℕ) : ℝ) ≤ w := by
      push_cast
      linarith [m1.1, m1.2, m2.1, m2.2]
    have key' : (z - z') + ((n - 1 - (a : ℕ) : ℕ) : ℤ) ≤ w := by exact_mod_cast key
    omega
  · simp only [Formalism.BasicNotions.DomWeight.natW, Formalism.BasicNotions.DomWeight.detShift, Pi.zero_apply, dite_eq_ite, ite_self,
      sub_zero, Int.toNat_zero, zero_add]
    omega

private theorem exists_prod_bound (w A : ℕ) (e : ℕ → ℕ)
    (he : ∀ p : ℕ, p.Prime → e p ≤ A * Nat.log p w ∧ (w < p → e p = 0)) :
    ∃ Dn : ℕ, 0 < Dn ∧ (∀ p : ℕ, p.Prime → p ^ e p ∣ Dn) ∧
      Real.log Dn ≤ (A : ℝ) * w * Real.log w := by
  classical
  set S := (Finset.range (w + 1)).filter Nat.Prime with hS
  refine ⟨∏ p ∈ S, p ^ e p, ?_, ?_, ?_⟩
  · exact Finset.prod_pos fun p hp => pow_pos (Finset.mem_filter.1 hp).2.pos _
  · intro p hp
    by_cases hpw : p ≤ w
    · exact Finset.dvd_prod_of_mem _ (Finset.mem_filter.2 ⟨Finset.mem_range.2 (by omega), hp⟩)
    · rw [(he p hp).2 (by omega), pow_zero]
      exact one_dvd _
  · rw [Nat.cast_prod, Real.log_prod (fun p hp => by
        have := (Finset.mem_filter.1 hp).2.pos
        exact_mod_cast (pow_pos this (e p)).ne')]
    have hterm : ∀ p ∈ S, Real.log ((p ^ e p : ℕ) : ℝ) ≤ A * Real.log w := by
      intro p hp
      have hp' := (Finset.mem_filter.1 hp).2
      have hpw : p ≤ w := Nat.lt_succ_iff.1 (Finset.mem_range.1 (Finset.mem_filter.1 hp).1)
      have hw0 : w ≠ 0 := by have := hp'.two_le; omega
      rw [Nat.cast_pow, Real.log_pow]
      have h1 : (e p : ℝ) ≤ A * Nat.log p w := by exact_mod_cast (he p hp').1
      have h2 : (Nat.log p w : ℝ) * Real.log p ≤ Real.log w := by
        have h3 := Nat.pow_log_le_self p hw0
        rw [← Real.log_pow]
        have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp'.pos
        apply Real.log_le_log (by positivity)
        exact_mod_cast h3
      have hlogp : 0 ≤ Real.log p := Real.log_nonneg (by exact_mod_cast hp'.one_lt.le)
      calc (e p : ℝ) * Real.log p ≤ (A * Nat.log p w) * Real.log p := mul_le_mul_of_nonneg_right h1 hlogp
        _ = A * ((Nat.log p w : ℝ) * Real.log p) := by ring
        _ ≤ A * Real.log w := mul_le_mul_of_nonneg_left h2 (by positivity)
    have hcard : S.card ≤ w := by
      calc S.card ≤ (Finset.Icc 1 w).card := Finset.card_le_card (fun p hp => by
              have h1 := Finset.mem_filter.1 hp
              have h2 := h1.2.one_lt
              have h3 := Finset.mem_range.1 h1.1
              rw [Finset.mem_Icc]
              omega)
        _ = w := by simp
    have hlw : 0 ≤ Real.log w := Real.log_natCast_nonneg w
    calc ∑ p ∈ S, Real.log ((p ^ e p : ℕ) : ℝ) ≤ ∑ p ∈ S, (A : ℝ) * Real.log w := Finset.sum_le_sum hterm
      _ = S.card * (A * Real.log w) := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ w * (A * Real.log w) := by
          apply mul_le_mul_of_nonneg_right _ (mul_nonneg (by positivity) hlw)
          exact_mod_cast hcard
      _ = A * w * Real.log w := by ring

end GlobalTheory.FinSize

namespace GlobalTheory.FinSize

open Finset GlobalTheory.SignedHC

private theorem entries_top_bound (D : D7) (large₂ : SizeData₂ D) (hS : GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup.SizeRows large₂) (τ : D.what₂.Tau)
    (C : ℝ) (hC : C = 1) :
    ∀ x ∈ GlobalTheory.SignedHC.entries (Node.par D C (.top D.R.m) τ),
      -(6 * large₂.sc.b) ≤ (x : ℝ) ∧ (x : ℝ) ≤ 2 * large₂.sc.b := by
  subst hC
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hSc, hbe, -⟩ := hS
  have hk := D.R.m_add_three_le_k
  have hm2 := D.R.two_le_m
  have hga : 2 * bigN D ^ 3 + 2 * sLen D + 3 ≤ gap D 1 := le_trans (le_max_right _ _) (le_max_left _ _)
  have hN3 : bigN D ≤ bigN D ^ 3 := Nat.le_self_pow (by norm_num) _
  have htN : D.R.t ≤ bigN D := by
    unfold bigN
    have h1 : D.R.t ≤ D.R.m * (D.R.t + sLen D + 1) :=
      le_trans (le_trans (Nat.le_add_right _ _) (Nat.le_add_right _ _)) (Nat.le_mul_of_pos_left _ (by omega))
    exact le_trans h1 (Nat.le_add_left _ _)
  have hScpos := large₂.Sc_pos
  have htga : (D.R.t : ℝ) + 3 ≤ (gap D 1 : ℝ) := by exact_mod_cast (by omega : D.R.t + 3 ≤ gap D 1)
  have hm1 : (3 : ℝ) ≤ (D.R.m : ℝ) + 1 := by
    have : (2 : ℝ) ≤ D.R.m := by exact_mod_cast hm2
    linarith
  have hga0 : (0 : ℝ) ≤ (gap D 1 : ℝ) := Nat.cast_nonneg _
  have hmγ : (gap D 1 : ℝ) ≤ ((D.R.m : ℝ) + 1) * (gap D 1 : ℝ) := by nlinarith
  have htb : (D.R.t : ℝ) ≤ large₂.sc.b := by linarith
  have hb1 : 3 ≤ large₂.sc.b := by linarith
  set G := num D 1 τ with hG
  have hGm : G.m = D.R.m := rfl
  have hGga : G.ga = gap D 1 := rfl
  have hGt : G.t = D.R.t := rfl
  have hSc' : large₂.Sc + ((G.m : ℝ) + 1) * (G.ga : ℝ) + 1 / 2 ≤ large₂.sc.b := hSc
  have hmγ' : (0 : ℝ) ≤ ((G.m : ℝ) + 1) * (G.ga : ℝ) := by positivity
  have hv : ∀ i, 2 ≤ i → i ≤ D.R.k → (-1 : ℝ) ≤ ((G.v i : ℤ) : ℝ) ∧ ((G.v i : ℤ) : ℝ) ≤ large₂.Sc := by
    intro i h1 h2
    have hi : i - 2 < D.R.k - 1 := by omega
    have hc := large₂.cloud_v τ ⟨i - 2, hi⟩
    have e : G.v i = ⌊(D.hc τ).v ⟨i - 2, hi⟩⌋ := by
      show GlobalTheory.SignedHC.GridData.extend 2 (D.hc τ).v i = _
      unfold GlobalTheory.SignedHC.GridData.extend
      rw [dif_pos hi]
    rw [e]
    have f1 : ((⌊(D.hc τ).v ⟨i - 2, hi⟩⌋ : ℤ) : ℚ) ≤ (D.hc τ).v ⟨i - 2, hi⟩ := Int.floor_le _
    have f2 : (D.hc τ).v ⟨i - 2, hi⟩ < ((⌊(D.hc τ).v ⟨i - 2, hi⟩⌋ : ℤ) : ℚ) + 1 := Int.lt_floor_add_one _
    have g1 : ((⌊(D.hc τ).v ⟨i - 2, hi⟩⌋ : ℤ) : ℝ) ≤ (((D.hc τ).v ⟨i - 2, hi⟩ : ℚ) : ℝ) := by exact_mod_cast f1
    have g2 : (((D.hc τ).v ⟨i - 2, hi⟩ : ℚ) : ℝ) < ((⌊(D.hc τ).v ⟨i - 2, hi⟩⌋ : ℤ) : ℝ) + 1 := by exact_mod_cast f2
    constructor <;> linarith [hc.1, hc.2]
  have he : ∀ l, 1 ≤ l → l ≤ D.R.m → (-1 : ℝ) ≤ ((G.e l : ℤ) : ℝ) ∧ ((G.e l : ℤ) : ℝ) ≤ 4 * large₂.sc.b := by
    intro l h1 h2
    have hl : l - 1 < D.R.m := by omega
    have hc := hbe τ ⟨l - 1, hl⟩
    have hgap := (D.hc τ).gap_be ⟨l - 1, hl⟩
    have e : G.e l = ⌊(D.hc τ).e ⟨l - 1, hl⟩⌋ := by
      show GlobalTheory.SignedHC.GridData.extend 1 (D.hc τ).e l = _
      unfold GlobalTheory.SignedHC.GridData.extend
      rw [dif_pos hl]
    rw [e]
    have hpos : (0 : ℚ) < (D.hc τ).e ⟨l - 1, hl⟩ := by
      have h0 : (0 : ℚ) < (D.hc τ).b ⟨l - 1, hl⟩ := by exact_mod_cast hc.1
      have h3 : (0 : ℚ) ≤ (D.R.t : ℚ) := Nat.cast_nonneg _
      linarith
    have f1 : ((⌊(D.hc τ).e ⟨l - 1, hl⟩⌋ : ℤ) : ℚ) ≤ (D.hc τ).e ⟨l - 1, hl⟩ := Int.floor_le _
    have f2 : (D.hc τ).e ⟨l - 1, hl⟩ < ((⌊(D.hc τ).e ⟨l - 1, hl⟩⌋ : ℤ) : ℚ) + 1 := Int.lt_floor_add_one _
    have g1 : ((⌊(D.hc τ).e ⟨l - 1, hl⟩⌋ : ℤ) : ℝ) ≤ (((D.hc τ).e ⟨l - 1, hl⟩ : ℚ) : ℝ) := by exact_mod_cast f1
    have g2 : (((D.hc τ).e ⟨l - 1, hl⟩ : ℚ) : ℝ) < ((⌊(D.hc τ).e ⟨l - 1, hl⟩⌋ : ℤ) : ℝ) + 1 := by exact_mod_cast f2
    have g3 : (0 : ℝ) < (((D.hc τ).e ⟨l - 1, hl⟩ : ℚ) : ℝ) := by exact_mod_cast hpos
    have g4 : (((D.hc τ).e ⟨l - 1, hl⟩ : ℚ) : ℝ) ≤ 4 * large₂.sc.b := hc.2
    constructor <;> linarith
  have hv2 := hv 2 le_rfl (by omega)
  intro x hx
  have hx' : x ∈ G.weightX D.R.m := by
    rw [show Node.par D 1 (.top D.R.m) τ = GlobalTheory.SignedHC.plus (G.weightX D.R.m) from rfl,
      GlobalTheory.SignedHC.entries_plus] at hx
    exact hx
  rcases GlobalTheory.SignedHC.GridData.mem_weightX.1 hx' with h | h | ⟨i, h1, h2, h⟩ | ⟨l, h1, h2, h⟩
  · obtain ⟨i, hi, rfl⟩ := GlobalTheory.SignedHC.GridData.mem_tops.1 h
    have hiR : (i : ℝ) ≤ (G.m : ℝ) := by exact_mod_cast hi
    have hi0 : (0 : ℝ) ≤ (i : ℝ) := Nat.cast_nonneg _
    have p1 : 0 ≤ ((G.m : ℝ) + 1 - i) * (G.ga : ℝ) := mul_nonneg (by linarith) (Nat.cast_nonneg _)
    have p2 : ((G.m : ℝ) + 1 - i) * (G.ga : ℝ) ≤ ((G.m : ℝ) + 1) * (G.ga : ℝ) :=
      mul_le_mul_of_nonneg_right (by linarith) (Nat.cast_nonneg _)
    simp only [GlobalTheory.SignedHC.GridData.a]
    push_cast
    constructor <;> linarith
  · obtain ⟨i, h1, h2, rfl⟩ := GlobalTheory.SignedHC.GridData.mem_cloudHalf.1 h
    have hvi := hv i h1 h2
    simp only [GlobalTheory.SignedHC.GridData.vHalf]
    push_cast
    constructor <;> linarith
  · have hb := GlobalTheory.ChiGrid.blockC'_between (num_nearMid D 1 τ) (odd_sLen D).pos (sLen_lt_gap D 1) h1 h2 h
    have c1 : ((G.a i : ℚ) : ℝ) < (x : ℝ) := by exact_mod_cast hb.1
    have c2 : (x : ℝ) < ((G.a i + G.ga : ℚ) : ℝ) := by exact_mod_cast hb.2
    simp only [GlobalTheory.SignedHC.GridData.a] at c1 c2
    push_cast at c1 c2
    have hiR : (i : ℝ) ≤ (G.m : ℝ) := by exact_mod_cast h2
    have hi1 : (1 : ℝ) ≤ (i : ℝ) := by exact_mod_cast h1
    have p1 : 0 ≤ ((G.m : ℝ) + 1 - i) * (G.ga : ℝ) := mul_nonneg (by linarith) (Nat.cast_nonneg _)
    have p2 : ((G.m : ℝ) + 1 - i) * (G.ga : ℝ) + (G.ga : ℝ) ≤ ((G.m : ℝ) + 1) * (G.ga : ℝ) := by
      have : ((G.m : ℝ) + 1 - i) * (G.ga : ℝ) + (G.ga : ℝ) = ((G.m : ℝ) + 1) * (G.ga : ℝ) - (i - 1) * (G.ga : ℝ) := by
        ring
      rw [this]
      have : 0 ≤ ((i : ℝ) - 1) * (G.ga : ℝ) := mul_nonneg (by linarith) (Nat.cast_nonneg _)
      linarith
    constructor <;> linarith
  · have hab := abs_le.1 (GlobalTheory.SignedHC.abs_sub_le_of_mem_block h)
    have hel := he l h1 h2
    have c1 : (x : ℝ) ≤ -((G.e l : ℤ) : ℝ) + (G.t : ℝ) / 2 := by
      have h' : x ≤ -((G.e l : ℤ) : ℚ) + (G.t : ℚ) / 2 := by push_cast at hab; linarith [hab.2]
      have h'' : (x : ℝ) ≤ ((-((G.e l : ℤ) : ℚ) + (G.t : ℚ) / 2 : ℚ) : ℝ) := Rat.cast_le.2 h'
      push_cast at h''
      linarith
    have c2 : -((G.e l : ℤ) : ℝ) - (G.t : ℝ) / 2 ≤ (x : ℝ) := by
      have h' : -((G.e l : ℤ) : ℚ) - (G.t : ℚ) / 2 ≤ x := by push_cast at hab; linarith [hab.1]
      have h'' : ((-((G.e l : ℤ) : ℚ) - (G.t : ℚ) / 2 : ℚ) : ℝ) ≤ (x : ℝ) := Rat.cast_le.2 h'
      push_cast at h''
      linarith
    have htb' : (G.t : ℝ) ≤ large₂.sc.b := htb
    have ht0 : (0 : ℝ) ≤ (G.t : ℝ) := Nat.cast_nonneg _
    constructor <;> linarith

private theorem rank_top {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) :
    (G.V (.top D.R.m)).rank = bigN D := by
  have hm := D.R.two_le_m
  have key : ∀ j, 1 ≤ j → j ≤ D.R.m → (G.V (.top j)).rank = rankX D j := by
    intro j h1 h2
    cases j with
    | zero => omega
    | succ j => exact (G.sp.X_is (j + 1) h1 h2).rank
  rw [key D.R.m (by omega) le_rfl]
  have hk := D.R.m_add_three_le_k
  have hr : D.R.r + 1 = D.R.k + D.R.m := by unfold Ranks.r; omega
  simp only [rankX, rankP, nRk, bigN, sLen]
  rw [show D.R.r + 6 - 1 = D.R.r + 5 by omega, hr]
  ring

end GlobalTheory.FinSize

namespace GlobalTheory.FinSize

private theorem natW_anti' {n : ℕ} (l : Formalism.BasicNotions.DomWeight n) : Antitone l.natW := fun i j hij => by
  unfold Formalism.BasicNotions.DomWeight.natW
  exact Int.toNat_le_toNat (by have := l.anti hij; omega)

private theorem exponent_bound : ∃ CF0 : ℝ, ∀ CF : ℝ, CF0 ≤ CF → ∃ K0 : ℝ, ∀ ε : ℝ, ∃ x₀ : ℝ, ∀ (D : D7) (large₂ : SizeData₂ D), large₂.sc.eps = ε → x₀ ≤ large₂.sc.x →
    ∀ (Γ : Type) [Group Γ] [Fintype Γ] (Pl0 T : Type) (A : FamIn D.what₂.LL Γ Pl0 T D.R.m)
      (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), HidaSetting large₂ R F →
      ∀ ch : Choice R, ch.Is → ch.AtScale CF large₂.sc.b →
        1 ≤ large₂.sc.b ∧ ∃ Dn : ℕ, 0 < Dn ∧
          (∀ p : ℕ, p.Prime → p ^ (∑ τ, Formalism.CohomologicalDescent.LA.exZ _ _ le_rfl (wt ch.G (.top D.R.m) τ).natW p) ∣ Dn) ∧
          Real.log Dn ≤ K0 * D.R.f * (bigN D : ℝ) ^ 2 * large₂.sc.b * Real.log large₂.sc.b := by
  refine ⟨0, fun CF _ => ⟨100, fun ε => ⟨0, ?_⟩⟩⟩
  intro D large₂ _ _ Γ _ _ Pl0 T A Ks _ _ _ R F hS ch _ hch
  have hch' : ch.sc = ⟨1, CF, large₂.sc.b⟩ := hch
  have hsc : ch.sc.cGap = 1 := by rw [hch']
  have hsize := hS.size
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hSc, -, -⟩ := hS.size
  have hm2 := D.R.two_le_m
  have hga : 2 * bigN D ^ 3 + 2 * sLen D + 3 ≤ gap D 1 := le_trans (le_max_right _ _) (le_max_left _ _)
  have hN3 : bigN D ≤ bigN D ^ 3 := Nat.le_self_pow (by norm_num) _
  have hNga : (bigN D : ℝ) + 3 ≤ (gap D 1 : ℝ) := by exact_mod_cast (by omega : bigN D + 3 ≤ gap D 1)
  have hm1 : (3 : ℝ) ≤ (D.R.m : ℝ) + 1 := by
    have : (2 : ℝ) ≤ D.R.m := by exact_mod_cast hm2
    linarith
  have hN0 : (0 : ℝ) ≤ (bigN D : ℝ) := Nat.cast_nonneg _
  have hγ3 : (3 : ℝ) ≤ (gap D 1 : ℝ) := by linarith
  have hmγ : (gap D 1 : ℝ) ≤ ((D.R.m : ℝ) + 1) * (gap D 1 : ℝ) := le_mul_of_one_le_left (by linarith) (by linarith)
  have h9 : (3 : ℝ) * 3 ≤ ((D.R.m : ℝ) + 1) * (gap D 1 : ℝ) := mul_le_mul hm1 hγ3 (by norm_num) (by linarith)
  have hScpos := large₂.Sc_pos
  have hb9 : 9 ≤ large₂.sc.b := by linarith
  have hbN : (bigN D : ℝ) ≤ large₂.sc.b := by linarith
  set b := large₂.sc.b with hb
  have hn : (ch.G.V (.top D.R.m)).rank = bigN D := rank_top ch.G
  set W : ℕ := ⌈8 * b⌉₊ with hW
  have hW1 : 8 * b ≤ (W : ℝ) := Nat.le_ceil _
  have hW2 : (W : ℝ) < 8 * b + 1 := Nat.ceil_lt_add_one (by linarith)
  have hnW : (ch.G.V (.top D.R.m)).rank - 1 ≤ W := by
    have h1 : ((ch.G.V (.top D.R.m)).rank : ℝ) ≤ W := by rw [hn]; linarith
    have h2 : (ch.G.V (.top D.R.m)).rank ≤ W := by exact_mod_cast h1
    omega
  have hwidth : ∀ (τ : D.what₂.Tau) (a : Fin (ch.G.V (.top D.R.m)).rank),
      (wt ch.G (.top D.R.m) τ).natW a + ((ch.G.V (.top D.R.m)).rank - 1 - a) ≤ W := by
    intro τ a
    exact natW_wtOf_add_le (ch.G.V (.top D.R.m)).rank
      (GlobalTheory.SignedHC.entries (Node.par D ch.sc.cGap (.top D.R.m) τ)) (-(6 * b)) (2 * b)
      (entries_top_bound D large₂ hsize τ _ hsc) W (by linarith) hnW a
  have hex : ∀ p : ℕ, p.Prime →
      (∑ τ, Formalism.CohomologicalDescent.LA.exZ _ _ le_rfl (wt ch.G (.top D.R.m) τ).natW p) ≤
        (Fintype.card D.what₂.Tau * ((ch.G.V (.top D.R.m)).rank).choose 2) * Nat.log p W ∧
      (W < p → (∑ τ, Formalism.CohomologicalDescent.LA.exZ _ _ le_rfl (wt ch.G (.top D.R.m) τ).natW p) = 0) := by
    intro p hp
    have hτ := fun τ => exZ_le_of_width _ (natW_anti' (wt ch.G (.top D.R.m) τ)) W (hwidth τ) p hp
    constructor
    · calc (∑ τ, Formalism.CohomologicalDescent.LA.exZ _ _ le_rfl (wt ch.G (.top D.R.m) τ).natW p)
          ≤ ∑ _τ : D.what₂.Tau, ((ch.G.V (.top D.R.m)).rank).choose 2 * Nat.log p W :=
            Finset.sum_le_sum fun τ _ => (hτ τ).1
        _ = _ := by rw [Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_assoc]
    · intro hWp
      exact Finset.sum_eq_zero fun τ _ => (hτ τ).2 hWp
  obtain ⟨Dn, h0, hdvd, hlog⟩ := exists_prod_bound W _
    (fun p => ∑ τ, Formalism.CohomologicalDescent.LA.exZ _ _ le_rfl (wt ch.G (.top D.R.m) τ).natW p) hex
  refine ⟨by linarith, Dn, h0, hdvd, ?_⟩
  have hA : ((Fintype.card D.what₂.Tau * ((ch.G.V (.top D.R.m)).rank).choose 2 : ℕ) : ℝ) ≤
      (D.R.f : ℝ) * (bigN D : ℝ) ^ 2 := by
    have h1 : ((ch.G.V (.top D.R.m)).rank).choose 2 ≤ (ch.G.V (.top D.R.m)).rank ^ 2 := by
      rw [Nat.choose_two_right, sq]
      exact le_trans (Nat.div_le_self _ _) (Nat.mul_le_mul_left _ (Nat.sub_le _ _))
    have h2 : Fintype.card D.what₂.Tau * ((ch.G.V (.top D.R.m)).rank).choose 2 ≤ D.R.f * bigN D ^ 2 := by
      rw [D.what₂.card_Tau, ← hn]
      exact Nat.mul_le_mul_left _ h1
    exact_mod_cast h2
  have hWb : (W : ℝ) ≤ 9 * b := by linarith
  have hW0 : (0 : ℝ) < W := by linarith
  have hlogW : Real.log W ≤ 2 * Real.log b := by
    have h1 : Real.log W ≤ Real.log (9 * b) := Real.log_le_log hW0 hWb
    have h2 : Real.log (9 * b) = Real.log 9 + Real.log b := Real.log_mul (by norm_num) (by linarith)
    have h3 : Real.log 9 ≤ Real.log b := Real.log_le_log (by norm_num) hb9
    linarith
  have hlogW0 : 0 ≤ Real.log W := Real.log_natCast_nonneg W
  have hlogb : 0 ≤ Real.log b := Real.log_nonneg (by linarith)
  have hP : 0 ≤ (D.R.f : ℝ) * (bigN D : ℝ) ^ 2 := by positivity
  have s1 : ((Fintype.card D.what₂.Tau * ((ch.G.V (.top D.R.m)).rank).choose 2 : ℕ) : ℝ) * W ≤
      ((D.R.f : ℝ) * (bigN D : ℝ) ^ 2) * (9 * b) :=
    mul_le_mul hA hWb (Nat.cast_nonneg _) hP
  have s2 := mul_le_mul s1 hlogW hlogW0 (mul_nonneg hP (by linarith))
  have hQ : 0 ≤ (D.R.f : ℝ) * (bigN D : ℝ) ^ 2 * b * Real.log b := mul_nonneg (mul_nonneg hP (by linarith)) hlogb
  calc Real.log Dn ≤ _ := hlog
    _ ≤ _ := s2
    _ = 18 * ((D.R.f : ℝ) * (bigN D : ℝ) ^ 2 * b * Real.log b) := by ring
    _ ≤ 100 * ((D.R.f : ℝ) * (bigN D : ℝ) ^ 2 * b * Real.log b) := by linarith
    _ = 100 * (D.R.f : ℝ) * (bigN D : ℝ) ^ 2 * b * Real.log b := by ring

end GlobalTheory.FinSize

end

theorem _root_.GlobalTheory.T.exists_totalExponent_topWeight_bound : ∃ CF0 : ℝ, ∀ CF : ℝ, CF0 ≤ CF → ∃ K0 : ℝ, ∀ ε : ℝ, ∃ x₀ : ℝ, ∀ (D : D7) (large₂ : SizeData₂ D), large₂.sc.eps = ε → x₀ ≤ large₂.sc.x →
    ∀ (Γ : Type) [Group Γ] [Fintype Γ] (Pl0 T : Type) (A : FamIn D.what₂.LL Γ Pl0 T D.R.m)
      (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), HidaSetting large₂ R F →
      ∀ ch : Choice R, ch.Is → ch.AtScale CF large₂.sc.b →
        1 ≤ large₂.sc.b ∧ ∃ Dn : ℕ, 0 < Dn ∧
          (∀ p : ℕ, p.Prime → p ^ (∑ τ, Formalism.CohomologicalDescent.LA.exZ _ _ le_rfl (wt ch.G (.top D.R.m) τ).natW p) ∣ Dn) ∧
          Real.log Dn ≤ K0 * D.R.f * (bigN D : ℝ) ^ 2 * large₂.sc.b * Real.log large₂.sc.b :=
  GlobalTheory.FinSize.exponent_bound
