import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BrPairFApply
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.InfClassAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueIsFunForm
import Formalism.SharpRestriction.Divisibility.PrimeDegreeVariant
import Formalism.PieriBlockIdeals.StatementLA
import Formalism.MirabolicMackeyTheory.MirabolicMackeyProofs.RamBasic
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DefiniteKernelNodeRankLeTotalRank
import Development.AbelianVarietyTheory.PublishedTheorems.GlobalTheta.FiniteDimensionalNablaSq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogBranchingConstantSqLeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TopNodeFormWeightAbsLeLinearStatement

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim GlobalTheory.TestLat GlobalTheory.SumSize
open Formalism.DivisionValues (vw lw)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.InfSize

theorem bigN_le {D : D7} {large₂ : SizeData₂ D} (hs : GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup.SizeRows large₂) : (bigN D : ℝ) ≤ 10 * large₂.sc.b := by
  obtain ⟨-, -, hf, hm, -, hb, -⟩ := hs
  have hd : 1 ≤ D.host.d := D.host.hyp.2.1.one_lt.le
  have hm1 : 1 ≤ D.R.m := by omega
  have hf1 : 1 ≤ D.R.f := le_trans (Nat.one_le_pow _ _ (by omega)) hf
  have hN1 : 1 ≤ D.R.N D.R.m := by unfold Ranks.N; have := D.R.m_add_three_le_k; omega
  have key : bigN D ≤ 10 * (D.R.m * D.R.f * D.R.N D.R.m ^ 2 * D.host.d) := by
    have e1 : D.R.N D.R.m ≤ D.R.N D.R.m ^ 2 := Nat.le_self_pow (by norm_num) _
    have e2 : D.R.m * D.R.N D.R.m ≤ D.R.m * D.R.f * D.R.N D.R.m ^ 2 * D.host.d := by
      calc D.R.m * D.R.N D.R.m = D.R.m * 1 * D.R.N D.R.m * 1 := by ring
        _ ≤ D.R.m * D.R.f * D.R.N D.R.m ^ 2 * D.host.d := by gcongr
    have e3 : bigN D ≤ 10 * (D.R.m * D.R.N D.R.m) := by
      have hk := D.R.m_add_three_le_k
      have s1 : bigN D ≤ D.R.k + D.R.m * (D.R.t + (D.R.k + D.R.m + 6) + 1) := by
        simp only [bigN, sLen, Ranks.r]; gcongr; omega
      have a1 : D.R.k ≤ D.R.m * D.R.k := Nat.le_mul_of_pos_left _ (by omega)
      have a2 : D.R.m * D.R.t ≤ D.R.m * (D.R.m * D.R.t) := Nat.le_mul_of_pos_left _ (by omega)
      have a3 : D.R.m ≤ D.R.m * D.R.m := Nat.le_mul_of_pos_left _ (by omega)
      refine s1.trans ?_
      simp only [Ranks.N]
      nlinarith
    omega
  have : (bigN D : ℝ) ≤ 10 * ((D.R.m * D.R.f * D.R.N D.R.m ^ 2 * D.host.d : ℕ) : ℝ) := by exact_mod_cast key
  push_cast at this
  linarith

theorem log_prod_le {ι : Type} [Fintype ι] (a : ι → ℝ) (c : ℝ) (h0 : ∀ i, 0 ≤ a i) (hc : 0 ≤ c)
    (h : ∀ i, Real.log (a i) ≤ c) : Real.log (∏ i, a i) ≤ Fintype.card ι * c := by
  by_cases hz : ∃ i, a i = 0
  · obtain ⟨i, hi⟩ := hz
    rw [Finset.prod_eq_zero (Finset.mem_univ i) hi, Real.log_zero]
    positivity
  · push_neg at hz
    rw [Real.log_prod (fun i _ => hz i)]
    calc ∑ i, Real.log (a i) ≤ ∑ _i : ι, c := Finset.sum_le_sum fun i _ => h i
      _ = Fintype.card ι * c := by simp

end GlobalTheory.InfSize

open GlobalTheory.InfSize in

theorem GlobalTheory.InfSize.main : ∃ CF0 : ℝ, ∀ CF : ℝ, CF0 ≤ CF → ∃ K0 : ℝ, ∀ ε : ℝ, ∃ x₀ : ℝ, ∀ (D : D7) (large₂ : SizeData₂ D), large₂.sc.eps = ε → x₀ ≤ large₂.sc.x →
    ∀ (Γ : Type) [Group Γ] [Fintype Γ] (Pl0 T : Type) (A : FamIn D.what₂.LL Γ Pl0 T D.R.m)
      (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), HidaSetting large₂ R F →
      ∀ ch : Choice R, ch.Is → ch.AtScale CF large₂.sc.b →
        1 ≤ large₂.sc.b ∧ Real.log (∏ τ, Formalism.MainNotions.PrimeDegreeVariant.brBd ch.G.sp.topDec.rank (wt ch.G (.top D.R.m) τ)
          (listedWt ch.G (.grid D.R.m D.R.m) τ) ^ 2) ≤ K0 * D.R.f * (bigN D : ℝ) * large₂.sc.b * Real.log large₂.sc.b := by
  obtain ⟨K1, hK1⟩ := GlobalTheory.T.topNodeFormWeight_abs_le_linear
  set c : ℝ := |K1| + 10 with hc
  set c2 : ℝ := Real.log (6 * c) + 1 with hc2
  refine ⟨0, fun CF _ => ⟨5 * c * c2, fun ε => ⟨0, fun D large₂ _ _ Γ _ _ Pl0 T A Ks _ _ _ R F hS ch _ hAt => ?_⟩⟩⟩
  have hc10 : 10 ≤ c := by rw [hc]; linarith [abs_nonneg K1]
  have hc2p : 1 ≤ c2 := by
    rw [hc2]; have : 0 ≤ Real.log (6 * c) := Real.log_nonneg (by linarith)
    linarith

  have hL : 1 ≤ large₂.sc.L := by
    unfold Scale.L
    exact Real.one_le_rpow large₂.sc.one_lt_alt.le large₂.sc.eps_pos.le
  have hlb : Real.log large₂.sc.b = large₂.sc.L := Real.log_exp _
  have hb1 : 1 ≤ large₂.sc.b := Real.one_le_exp (by linarith)
  refine ⟨hb1, ?_⟩
  have hlog1 : 1 ≤ Real.log large₂.sc.b := hlb ▸ hL

  have hcg : ch.sc.cGap = 1 := by rw [hAt]
  have hw := hK1 D large₂ hS.size ch.G hcg
  have hNb := bigN_le hS.size
  have hrk : (ch.G.V (.top D.R.m)).rank ≤ bigN D := GlobalTheory.DefRank.rank_le_bigN ch.G (.top D.R.m) (le_refl D.R.m)
  have hrkR : ((ch.G.V (.top D.R.m)).rank : ℝ) ≤ bigN D := by exact_mod_cast hrk
  set B : ℝ := c * large₂.sc.b with hB
  have hB1 : 1 ≤ B := by rw [hB]; nlinarith
  have hlogB : Real.log (6 * B) ≤ c2 * Real.log large₂.sc.b := by
    rw [hB, ← mul_assoc, Real.log_mul (by positivity) (by positivity), hc2]
    have : 0 ≤ Real.log (6 * c) := Real.log_nonneg (by linarith)
    nlinarith
  have hNB : ((ch.G.V (.top D.R.m)).rank : ℝ) ≤ B := by
    rw [hB]; nlinarith
  have hwB : ∀ τ i, |(((wt ch.G (.top D.R.m) τ).w i : ℤ) : ℝ)| ≤ B := fun τ i => by
    refine (hw τ i).trans ?_
    rw [hB]; exact mul_le_mul_of_nonneg_right (by rw [hc]; linarith [le_abs_self K1]) (by linarith)
  have hτ : ∀ τ, Real.log (Formalism.MainNotions.PrimeDegreeVariant.brBd ch.G.sp.topDec.rank (wt ch.G (.top D.R.m) τ)
      (listedWt ch.G (.grid D.R.m D.R.m) τ) ^ 2) ≤ 5 * c * c2 * (bigN D : ℝ) * large₂.sc.b * Real.log large₂.sc.b := by
    intro τ
    refine (GlobalTheory.T.log_branching_constant_sq_le _ _ _ B hB1 hNB (hwB τ)).trans ?_
    have hl6 : 0 ≤ Real.log (6 * B) := Real.log_nonneg (by linarith)
    calc 5 * ((ch.G.V (.top D.R.m)).rank : ℝ) * B * Real.log (6 * B) ≤ 5 * (bigN D : ℝ) * B * Real.log (6 * B) := by
          gcongr
      _ ≤ 5 * (bigN D : ℝ) * B * (c2 * Real.log large₂.sc.b) := by gcongr
      _ = 5 * c * c2 * (bigN D : ℝ) * large₂.sc.b * Real.log large₂.sc.b := by rw [hB]; ring
  have h0 : 0 ≤ 5 * c * c2 * (bigN D : ℝ) * large₂.sc.b * Real.log large₂.sc.b := by positivity
  refine (log_prod_le _ _ (fun τ => sq_nonneg _) h0 hτ).trans (le_of_eq ?_)
  rw [D.what₂.card_Tau]
  ring
