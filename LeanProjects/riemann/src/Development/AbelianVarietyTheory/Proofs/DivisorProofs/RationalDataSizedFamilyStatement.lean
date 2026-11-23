import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalDataSizedFamily
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.LatticeFramesOfHyps
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RegularisedSiegelWeilFirstTerm
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NonzeroPlacesOverPrimes
import Development.AbelianVarietyTheory.Definitions.Divisors.Hypotheses2
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FieldValuesMemFixedField
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsWeilDatumOOneOfRankZero
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.L2.Pj Formalism.IndefR.FWT
open scoped TensorProduct InnerProductSpace Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.PrimIn
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rational_data_sized_family : Hypotheses3 → GlobalTheory.Published.RegularisedSiegelWeilFirstTerm → GlobalTheory.Published.HeckeLPartialContinuation → ∀ eps : ℝ, 0 < eps → ∃ x₀ : ℝ, ∀ (X : GlobalTheory.Mem.Stages) (px : GlobalTheory.Mem.PreX X.B.toPre) (I : GlobalTheory.Mem.Col2.ColIn X.B px) (hX : X.B.fields.Ok) (Tw : GlobalTheory.Mem.Top.TwDat X.B) (Wt : Set X.B.places.Pl) (z : GlobalTheory.Mem.R3.Dat X I hX Tw Wt) (L : SizeData₂ X.toD7), L.sc.eps = eps → x₀ ≤ L.sc.x → Formalism.MainNotions.SizesAt L → Nonempty (ParameterChoice' X.toD7 L) → TiesB z.R z.F → TiesG z.core z.R z.geo.κ z.geo.v₀ z.geo.O → GlobalTheory.CuspMult.MultEq z.R.toRealDat → Formalism.IndefR.Rat.RowTest (z.R.toCx3 z.F) → z.R.toRealDat.LIntegral → GlobalTheory.Mem.R3.Holds z.R z.F := by
  first | exact @GlobalTheory.PrimIn.holds_of_ties | exact GlobalTheory.PrimIn.holds_of_ties | (intros; apply GlobalTheory.PrimIn.holds_of_ties <;> assumption)
