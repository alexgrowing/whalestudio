import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasInfinityExponentOfFinitePartPower
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormPeriodSq

open NumberField MeasureTheory
open scoped Classical
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum
open Formalism.MainNotions.TaylorLogMetric (VC embT tor0 Hf lamOf area Th U)
open Formalism.MainNotions.StandardLatticesGL3 (WeilO HeckeU TT stdL pt oddE0)
open GlobalTheory.NormSum (Pair Tup minorPol ratG intG Cls gam)
open GlobalTheory.NormDict GlobalTheory.NormExact
open GlobalTheory.BotFormula (IsFinPt)
open GlobalTheory.IndefiniteRowSideFullHecke.ClassFunctionSumIntegral (IsDefiniteSpace IsOpenCompactLevel)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hasInfinityExponent_of_finitePartPower : ∀ {D : D7} {N : ℕ} (c : HeckeU D N) (e : ℤ) (χ : (AE D)ˣ →* Circle), IsHeckeChar D χ → HasFinPart χ c e →
  ∀ τ, HasInfExp D χ τ ((e : ℚ) * (c.n τ : ℚ) / 2) := by
  first | exact @GlobalTheory.NormExact.InfExp.hasInfExp_of_hasFinPart | exact GlobalTheory.NormExact.InfExp.hasInfExp_of_hasFinPart | (intros; apply GlobalTheory.NormExact.InfExp.hasInfExp_of_hasFinPart <;> assumption)
