import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PlaceValuationLocalDegreeArithmetic
import Mathlib
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

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.placeValuation_localDegree_arithmetic : ∀ {K : Type} [Field K] [NumberField K] [StarRing K],
    (∀ (w : HeightOneSpectrum (𝓞 K)) (a b : K), a ≠ 0 → b ≠ 0 → Formalism.DivisionValues.vw w (a * b) = Formalism.DivisionValues.vw w a + Formalism.DivisionValues.vw w b) ∧
    (∀ (w : HeightOneSpectrum (𝓞 K)) (m d : ℕ), 0 < d → m ∣ d →
      0 ≤ Formalism.DivisionValues.vw w (m : K) ∧ Formalism.DivisionValues.vw w (m : K) ≤ Formalism.DivisionValues.vw w (d : K)) ∧
    (∀ d : ℕ, 0 < d → {w : HeightOneSpectrum (𝓞 K) | Formalism.DivisionValues.vw w (d : K) ≠ 0}.Finite) ∧
    (∀ d : ℕ, 0 < d → ∀ s : Finset (HeightOneSpectrum (𝓞 K)),
      ∑ w ∈ s, Formalism.DivisionValues.lw w * (Formalism.DivisionValues.vw w (d : K) : ℝ) ≤ Real.log d) := by
  first | exact @GlobalTheory.vw_lw_arith | exact GlobalTheory.vw_lw_arith | (intros; apply GlobalTheory.vw_lw_arith <;> assumption)
