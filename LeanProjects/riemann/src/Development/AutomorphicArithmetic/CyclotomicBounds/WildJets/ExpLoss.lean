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
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim GlobalTheory.TestLat GlobalTheory.SumSize
open Formalism.DivisionValues (vw lw)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem UpperTheory.WildA.expLoss :
    ∀ (D : D7) (S : Finset ℕ) (h : ℕ → ℝ) (B : ℝ), GlobalTheory.NormSum.Exponents S h B →
      Loss (fun w : PlL D => (vw w ((GlobalTheory.SumSize.TopInt.primeUnder w : ℕ) : D.what₂.LL) : ℝ) * h (GlobalTheory.SumSize.TopInt.primeUnder w)) B := by
  intro D S h B hE
  have e : (fun w : PlL D => (vw w ((GlobalTheory.SumSize.TopInt.primeUnder w : ℕ) : D.what₂.LL) : ℝ) *
      h (GlobalTheory.SumSize.TopInt.primeUnder w)) = Formalism.PairingDivisionLocalBalance.wt (K := D.what₂.LL) S h := by
    funext w
    rw [hE.wt_eq (TopInt.primeUnder_prime w) w (TopInt.primeUnder_mem w), mul_comm]
  rw [e]
  refine ⟨hE.wt_size.1, ?_, hE.wt_size.2⟩
  have hf : ∀ l : ℕ, {w : PlL D | vw w (l : D.what₂.LL) ≠ 0}.Finite := fun l => by
    have hf := FractionalIdeal.finite_factors (K := D.what₂.LL)
      (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 D.what₂.LL)) (l : D.what₂.LL))
    rw [Filter.eventually_cofinite] at hf
    exact hf
  refine (S.finite_toSet.biUnion fun l _ => hf l).subset fun w hw => ?_
  obtain ⟨l, hl, h0⟩ := Finset.exists_ne_zero_of_sum_ne_zero hw
  refine Set.mem_biUnion (Finset.mem_coe.2 hl) fun h1 => h0 ?_
  rw [h1]; simp
