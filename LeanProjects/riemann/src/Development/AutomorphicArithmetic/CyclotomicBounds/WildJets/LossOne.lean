import Mathlib
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.InfClassAt
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.DictAt
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Development.AbelianVarietyTheory.Statements.CuspidalUnitaryTwists.ExistsSmallSpherical
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicValuationThetaKernelJetBound
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HighestWeightBelow
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VwNatCastNonneg
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.JetKapIff
import Development.AutomorphicArithmetic.CyclotomicBounds.WildJets.KerLe
import Development.AutomorphicArithmetic.CyclotomicBounds.WildJets.DepSum
import Development.AutomorphicArithmetic.CyclotomicBounds.WildJets.LogSum
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim GlobalTheory.TestLat GlobalTheory.SumSize
open Formalism.DivisionValues (vw lw)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

private theorem expAdd {S S' : Finset ℕ} {f g : ℕ → ℝ} {a b : ℝ} (h : GlobalTheory.NormSum.Exponents S f a)
    (h' : GlobalTheory.NormSum.Exponents S' g b) : GlobalTheory.NormSum.Exponents (S ∪ S') (fun l => f l + g l) (a + b) := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  obtain ⟨g1, g2, g3, g4⟩ := h'
  refine ⟨fun l hl => (Finset.mem_union.1 hl).elim (h1 l) (g1 l), fun l => add_nonneg (h2 l) (g2 l), fun l hl => ?_, ?_⟩
  · rw [Finset.mem_union, not_or] at hl
    dsimp only
    rw [h3 l hl.1, g3 l hl.2, add_zero]
  · simp only [add_mul, Finset.sum_add_distrib]
    rw [← Finset.sum_subset (Finset.subset_union_left (s₁ := S) (s₂ := S')) (fun l _ hl => by rw [h3 l hl, zero_mul]),
      ← Finset.sum_subset (Finset.subset_union_right (s₁ := S) (s₂ := S')) (fun l _ hl => by rw [g3 l hl, zero_mul])]
    exact add_le_add h4 g4

private theorem expMul {S : Finset ℕ} {f : ℕ → ℝ} {a c : ℝ} (hc : 0 ≤ c) (h : GlobalTheory.NormSum.Exponents S f a) :
    GlobalTheory.NormSum.Exponents S (fun l => c * f l) (c * a) := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨h1, fun l => mul_nonneg hc (h2 l), fun l hl => ?_, ?_⟩
  · dsimp only
    rw [h3 l hl, mul_zero]
  · simp only [mul_assoc, ← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left h4 hc

private theorem expMono {S : Finset ℕ} {f : ℕ → ℝ} {a b : ℝ} (h : GlobalTheory.NormSum.Exponents S f a) (hab : a ≤ b) :
    GlobalTheory.NormSum.Exponents S f b := ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.trans hab⟩

private theorem expOne (d : ℕ) : GlobalTheory.NormSum.Exponents (({d} : Finset ℕ).filter Nat.Prime)
    (fun l => if l.Prime ∧ l = d then 1 else 0) (Real.log d) := by
  refine ⟨fun l hl => (Finset.mem_filter.1 hl).2, fun l => by dsimp only; split_ifs <;> norm_num, fun l hl => ?_, ?_⟩
  · exact if_neg fun h => hl (Finset.mem_filter.2 ⟨Finset.mem_singleton.2 h.2, h.1⟩)
  · rw [Finset.filter_singleton]
    split_ifs with h
    · simp [h]
    · simpa using Real.log_natCast_nonneg d

private theorem expLog {y c : ℝ} (hy : 0 ≤ y) (hc : 0 ≤ c) (hyc : Real.log y ≤ c) :
    GlobalTheory.NormSum.Exponents ((Finset.range (⌊y⌋₊ + 1)).filter Nat.Prime)
    (fun l => if l.Prime ∧ (l : ℝ) ≤ y then Real.logb l y else 0) (y * c) := by
  have hm : ∀ l : ℕ, l ∈ (Finset.range (⌊y⌋₊ + 1)).filter Nat.Prime ↔ l.Prime ∧ (l : ℝ) ≤ y := fun l => by
    rw [Finset.mem_filter, Finset.mem_range, Nat.lt_succ_iff, Nat.le_floor_iff hy, and_comm]
  refine ⟨fun l hl => (Finset.mem_filter.1 hl).2, fun l => ?_, fun l hl => if_neg fun h => hl ((hm l).2 h), ?_⟩
  · dsimp only
    split_ifs with h
    · exact Real.logb_nonneg (by exact_mod_cast h.1.one_lt) (le_trans (by exact_mod_cast h.1.one_lt.le) h.2)
    · exact le_rfl
  · dsimp only
    rw [Finset.sum_congr (g := fun l : ℕ => Real.logb l y * Real.log l) rfl fun l hl => by rw [if_pos ((hm l).1 hl)]]
    rcases le_or_gt 1 y with h | h
    · exact (UpperTheory.WildA.logSum y h).trans (mul_le_mul_of_nonneg_left hyc hy)
    · rw [Nat.floor_eq_zero.2 h]
      have e : (Finset.range (0 + 1)).filter Nat.Prime = ∅ := by decide
      rw [e, Finset.sum_empty]
      exact mul_nonneg hy hc

theorem UpperTheory.WildA.lossOne :
    ∀ C1 : ℝ, 0 < C1 → ∃ C0 : ℝ, 0 < C0 ∧ ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} {G : GlobalTheory.ChiGrid.GridData L sc} (large₂ : SizeData₂ D), GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup.SizeRows large₂ → HostHyp D → sc.cGap = 1 →
      ∀ (S : Finset ℕ) (δ : ℕ → ℝ), GlobalTheory.NormSum.Letters D S δ → ∃ (S' : Finset ℕ) (h : ℕ → ℝ),
        GlobalTheory.NormSum.Exponents S' h (C0 * D.R.f * (bigN D : ℝ) ^ 2 * (Real.log large₂.sc.b + sig G) * large₂.sc.b) ∧
        ∀ p : GlobalTheory.ChiGrid.Pair T, DefPair D.R.m p → ∀ l : ℕ, l.Prime →
          C1 * GlobalTheory.SumSize.TopInt.kerLoss G δ C1 large₂.sc.b p.small p.big l (depL G l) ≤ h l := by
  intro C1 hC1
  refine ⟨C1 * (26 + C1 * (|Real.log C1| + 1)), by positivity, ?_⟩
  intro D T L sc G large₂ hS hH hc S δ hδ
  obtain ⟨-, -, hN, hf, hm, -, hrd, h12⟩ := GlobalTheory.SizesOfRows.sizes_of_sizeRows large₂ hS
  have hNR : (1 : ℝ) ≤ bigN D := by exact_mod_cast hN
  have hfR : (1 : ℝ) ≤ D.R.f := by exact_mod_cast hf
  have hmR : (2 : ℝ) ≤ D.R.m := by exact_mod_cast hm
  have hb0 : 0 < large₂.sc.b := by linarith
  have hL : 1 ≤ Real.log large₂.sc.b := by
    rw [Real.le_log_iff_exp_le hb0]
    linarith [Real.exp_one_lt_d9]
  have hd : Real.log D.host.d ≤ Real.log large₂.sc.b := by
    have hb := hS.2.2.2.2.2.1
    have hk : D.R.m + 3 ≤ D.R.k := D.R.m_add_three_le_k
    have hN1 : 1 ≤ D.R.N D.R.m := by simp only [Formalism.BasicNotions.Ranks.N]; omega
    have hN1R : (1 : ℝ) ≤ D.R.N D.R.m := by exact_mod_cast hN1
    have h1 : (1 : ℝ) ≤ (D.R.m : ℝ) * D.R.f * (D.R.N D.R.m : ℝ) ^ 2 :=
      one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le (by linarith) hfR) (one_le_pow₀ hN1R)
    have h2 : (D.host.d : ℝ) ≤ large₂.sc.b := (le_mul_of_one_le_left (Nat.cast_nonneg _) h1).trans hb
    rcases Nat.eq_zero_or_pos D.host.d with h | h
    · rw [h, Nat.cast_zero, Real.log_zero]
      linarith
    · exact Real.log_le_log (by exact_mod_cast h) h2
  have hsig : 0 ≤ sig G := Finset.sum_nonneg fun v _ => mul_nonneg (Nat.cast_nonneg _) (Real.log_natCast_nonneg _)
  have hy : Real.log (C1 * large₂.sc.b) ≤ (|Real.log C1| + 1) * Real.log large₂.sc.b := by
    rw [Real.log_mul hC1.ne' hb0.ne']
    nlinarith [le_abs_self (Real.log C1), abs_nonneg (Real.log C1)]
  obtain ⟨S2, h2⟩ := UpperTheory.WildA.depSum (G := G)
  have h0 : GlobalTheory.NormSum.Exponents S δ (Real.log D.host.rdE) := ⟨hδ.1, hδ.2.1, hδ.2.2.1, hδ.2.2.2.1⟩
  have h3 := expLog (y := C1 * large₂.sc.b) (by positivity) (by positivity) hy
  have h4 := expMul hC1.le (expAdd
    (expMul (c := 13 * D.R.f * bigN D * large₂.sc.b) (by positivity) (expAdd (expAdd h0 (expOne D.host.d)) h2))
    (expMul (c := (D.R.f : ℝ) * (bigN D : ℝ) ^ 2) (by positivity) h3))
  refine ⟨_, _, expMono h4 ?_, fun p hp l hl => ?_⟩
  · set Lb := Real.log large₂.sc.b
    set K := |Real.log C1| + 1 with hK
    have hK0 : 0 ≤ K := by positivity
    have e1 : (13 * D.R.f * bigN D * large₂.sc.b : ℝ) * (Real.log D.host.rdE + Real.log D.host.d + sig G) ≤
        (13 * D.R.f * (bigN D : ℝ) ^ 2 * large₂.sc.b) * (2 * (Lb + sig G)) := by
      refine (mul_le_mul_of_nonneg_left (b := _) (c := 2 * (Lb + sig G)) (by linarith) (by positivity)).trans ?_
      have : (bigN D : ℝ) ≤ (bigN D : ℝ) ^ 2 := by nlinarith
      gcongr
    have e2 : (D.R.f : ℝ) * (bigN D : ℝ) ^ 2 * (C1 * large₂.sc.b * (K * Lb)) ≤
        (D.R.f : ℝ) * (bigN D : ℝ) ^ 2 * (C1 * large₂.sc.b * (K * (Lb + sig G))) := by
      gcongr
      linarith
    refine (mul_le_mul_of_nonneg_left (add_le_add e1 e2) hC1.le).trans (le_of_eq ?_)
    ring
  · refine mul_le_mul_of_nonneg_left ?_ hC1.le
    unfold GlobalTheory.SumSize.TopInt.kerLoss
    simp only [hl, true_and, if_true]
    refine add_le_add (mul_le_mul_of_nonneg_right (UpperTheory.WildA.kerLe (G := G) large₂ hS hH hc p hp) ?_) le_rfl
    have := hδ.2.1 l
    split_ifs <;> positivity
