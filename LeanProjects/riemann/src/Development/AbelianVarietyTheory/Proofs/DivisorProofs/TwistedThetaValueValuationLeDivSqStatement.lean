import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedThetaValueValuationLeDivSq
import Mathlib
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.SizeAt
import Development.AbelianVarietyTheory.Definitions.Divisors.TieTest
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ToricSymbols
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NuHTwisted
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.BigTop GlobalTheory.BigTop.Fun GlobalTheory.SqTop NumberField IsDedekindDomain
open GlobalTheory.FunObj.SqNum (nuH halfRank IsTor)
open GlobalTheory.CMVal GlobalTheory.HeckeGal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twistedThetaValue_valuation_le_div_sq : ∀ {D : D7} (nch : NChoice D) (w : D.what₂.places.Pl) (N0 : D.ntw.Tw → ℕ) (lam : D.ntw.abelian₂ (nch.twI w)) (a : ℤ)
    (u : (nch.Oe w)ˣ) (z : D.what₂.LL),
    BlochKatoReduction.Gen.partC N0 (nch.twI w) (nch.Q w) (nch.k' w) (nch.psi' w ^ a) (twEps D (nch.twI w)) →
    nch.embW w z * nch.kMapE w (BlochKatoReduction.Gen.kMap D.ntw (nch.twI w) (nch.k' w) (∑ δ, D.ntw.th (nch.twI w) ∅ lam δ)) =
      algebraMap (nch.Oe w) (FractionRing (nch.Oe w)) (u : nch.Oe w) *
        nch.kMapE w (BlochKatoReduction.Gen.thEval D.ntw (nch.twI w) (nch.Q w) lam (nch.k' w)
          (BlochKatoReduction.Gen.psiAt (D.ntw.sideL (nch.twI w) lam) (nch.psi' w ^ a))) →
    (Formalism.DivisionValues.vw (D.plEq w) z : ℝ) ≤ (Formalism.DivisionValues.vw (D.plEq w) ((D.what₂.places.resChar w : ℕ) : D.what₂.LL) : ℝ) / ((D.what₂.places.resChar w : ℕ) : ℝ) ^ 2 := by
  first | exact @GlobalTheory.TwistValBound.vw_le_of_bound | exact GlobalTheory.TwistValBound.vw_le_of_bound | (intros; apply GlobalTheory.TwistValBound.vw_le_of_bound <;> assumption)
