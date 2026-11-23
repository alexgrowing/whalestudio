import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormPeriodSq
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FiniteRealPointsCommute

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

namespace GlobalTheory.FinPtUnique

theorem eq_of_isFinPt : ∀ {D : D7} (V : HSp D) {n : ℕ} (g g' : GA D V) (x : Formalism.MainNotions.StandardLatticesGL3.GA D n),
    IsFinPt V g x → IsFinPt V g' x → g = g' := by
  intro D V n g g' x ⟨hg, e, he⟩ ⟨hg', e', he'⟩
  apply GlobalTheory.FinRealComm.GA_ext_inf_fin V
  · have h1 : infHom V g = 1 := hg
    have h2 : infHom V g' = 1 := hg'
    rw [h1, h2]
  · apply Units.ext
    apply Matrix.ext
    intro i j
    apply (GlobalTheory.LFun.finAdEquiv D.host.F D.host.E).injective
    rw [he i j, he' i j]

end GlobalTheory.FinPtUnique
