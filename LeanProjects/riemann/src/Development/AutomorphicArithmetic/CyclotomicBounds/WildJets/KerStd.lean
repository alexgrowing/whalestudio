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
import Development.AutomorphicArithmetic.CyclotomicBounds.WildJets.TabBd
import Development.AutomorphicArithmetic.CyclotomicBounds.WildJets.JetOpMulTab
import Development.AutomorphicArithmetic.CyclotomicBounds.WildJets.JetInt
import Development.AutomorphicArithmetic.CyclotomicBounds.WildJets.BdLoss
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim GlobalTheory.TestLat GlobalTheory.SumSize
open Formalism.DivisionValues (vw lw)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem UpperTheory.WildA.kerStd :
    ∀ (D : D7) (large₂ : SizeData₂ D) (Γ : Type) [Group Γ] [Fintype Γ] (Pl0 T : Type) (A : FamIn D.what₂.LL Γ Pl0 T D.R.m)
      (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), HidaSetting large₂ R F →
      ∀ (ch : Choice R), GlobalTheory.NormSum.Inp D → DictAt ch → ∀ (S : Finset ℕ) (δ : ℕ → ℝ), GlobalTheory.NormSum.Letters D S δ →
      ∀ (t : T) (p : GlobalTheory.ChiGrid.Pair T), DefPair D.R.m p → ∀ (k : ℕ) (d : FinDatum ch.G t p), 0 < k → IsCosetDatum k d → d.z = 1 →
      d.P = locPl ch.G t → ∀ (x : FinPt ch.G p.small) (y : FinPt ch.G p.big), ch.S.Z.IsRatAt d x y →
      ∀ (w : PlL D) (l : ℕ), l.Prime → (l : 𝓞 D.what₂.LL) ∈ w.asIdeal → (l ∣ k → GlobalTheory.NormSum.SplitIn D l) →
      Formalism.MainNotions.TaylorLogMetric.EqAt D l (latAt ch.S.toGridChoice p.small x) (Formalism.MainNotions.StandardLatticesGL3.stdL D _) →
      Formalism.MainNotions.TaylorLogMetric.EqAt D l (latAt ch.S.toGridChoice p.big y) (Formalism.MainNotions.StandardLatticesGL3.stdL D _) → ∀ (b : ℝ) i j,
        LossLe w ((bVV ℂ (wt ch.G p.big)).repr (ch.S.Z.kkMap 1 d x y (bVV ℂ (wt ch.G p.small) j)) i)
          ((vw w ((l : ℕ) : D.what₂.LL) : ℝ) * GlobalTheory.SumSize.TopInt.kerLoss ch.G δ 1 b p.small p.big l (padicValNat l k)) := by
  intro D large₂ Γ _ _ Pl0 T A Ks _ _ _ R F hS ch hI hD S δ hL t p hp k d hk hc hz hP x y hR w l hl hw hsp hx hy b i j
  classical
  haveI : Fact l.Prime := ⟨hl⟩
  obtain ⟨Ls, Lt, κ, n, r, s, hLs, hLt, hκ, hs, hr, -, hq, htab⟩ := hD t p hp k d hk hc hz hP x y
  obtain ⟨hEs, hEt, hκ1⟩ := hq l hx hy
  have hcc : D.host.ccK = ⊤ := hS.size.2.2.2.2.2.2.2.2.2.2.2.2.2
  have hkk := UpperTheory.WildA.kkTab ch.S.Z hp d x y _ htab
  obtain ⟨c, hcJ⟩ := UpperTheory.WildA.jetInt _ _ _ (wtOK_of_defPair ch.G p hp).2 j i
  have hB := UpperTheory.WildA.tabBd D hI S δ hL D.host.ccK hcc ch.S.Z.δ ch.S.Z.t0 ch.S.Z.crv ch.S.Z.4 _ _ (ch.S.Z.e0 p)
    (ch.S.Z.e0_is p hp) Ls Lt hLs hLt l hEs hEt k hk hsp κ n _ r s hκ hκ1 hs hr
  have hl1 : (1 : ℝ) ≤ l := by exact_mod_cast hl.one_le
  have hopp : ∀ (z : ℂ) (C : ℝ), (∀ lam : Formalism.MainNotions.TaylorLogMetric.Qbar →+* ℂ_[l], GlobalTheory.NormSum.Term.Bd lam C z) →
      ∀ lam : Formalism.MainNotions.TaylorLogMetric.Qbar →+* ℂ_[l], GlobalTheory.NormSum.Term.Bd lam C (opp p z) := by
    intro z C h lam
    have hcj : GlobalTheory.NormSum.Term.Bd lam C ((starRingEnd ℂ) z) :=
      ⟨(GlobalTheory.NormSum.conjQbar ⟨z, (h lam).1⟩).2, GlobalTheory.NormSum.conj_bound (h lam).1 (fun lam => (h lam).2) lam⟩
    cases p
    all_goals first | exact h lam | exact hcj
  have hrk : ((ch.G.pS p).rank : ℝ) * (ch.G.pT p).rank = ((ch.G.V p.small).rank : ℝ) * (ch.G.V p.big).rank := by
    cases p
    all_goals first | rfl | exact mul_comm _ _
  refine UpperTheory.WildA.bdLoss D w l hw _ _ ?_ fun lam => ?_
  · have := hR i j
    rwa [Normal.kkIn, LinearMap.toMatrix_apply] at this
  · rw [hkk, hcJ, Finsupp.sum]
    refine GlobalTheory.NormSum.Term.Bd.sum (by positivity) _ _ fun m _ => ?_
    rw [← one_mul ((l : ℝ) ^ _)]
    refine (GlobalTheory.NormSum.Term.Bd.intCast _).mul ?_
    split_ifs with hm
    · refine (hopp _ _ (fun lam => hB lam _) lam).mono (Real.rpow_le_rpow_of_exponent_le hl1 ?_)
      rw [Finsupp.degree_mapDomain, hm]
      unfold GlobalTheory.SumSize.TopInt.kerLoss
      have h0 := hL.2.1 l
      have h2 : 0 ≤ (if (l : ℝ) ≤ 1 * b then Real.logb l (1 * b) else 0) := by
        split_ifs with h
        · exact Real.logb_nonneg (by exact_mod_cast hl.one_lt) (hl1.trans h)
        · exact le_rfl
      have h3 : (0 : ℝ) ≤ (if l = D.host.d then 1 else 0) := by split_ifs <;> norm_num
      have h4 : (if l = D.host.d then (1 : ℝ) / 4 else 0) ≤ (if l = D.host.d then 1 else 0) := by split_ifs <;> norm_num
      have h5 : ((D.R.f * (ch.G.pS p).rank * (ch.G.pT p).rank : ℕ) : ℝ) =
          (D.R.f : ℝ) * (ch.G.V p.small).rank * (ch.G.V p.big).rank := by
        push_cast
        rw [mul_assoc, mul_assoc, hrk]
      rw [h5, add_mul]
      refine le_add_of_le_of_nonneg (add_le_add ?_ ?_) (by positivity)
      · exact mul_le_mul_of_nonneg_left (by linarith) (Nat.cast_nonneg _)
      · exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    · exact GlobalTheory.NormSum.Term.Bd.zero (by positivity)
