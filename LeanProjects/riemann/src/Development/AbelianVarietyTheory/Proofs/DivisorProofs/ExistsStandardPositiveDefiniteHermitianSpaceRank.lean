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

noncomputable section

namespace GlobalTheory.StdDefSpace

theorem exists_std_definite : ∀ (D : D7) (n : ℕ), ∃ V : HSp D, V.rank = n ∧ V.gram = 1 ∧ IsDefiniteSpace V := by
  intro D n
  refine ⟨Formalism.BasicNotions.Examples₂.posSpace Formalism.BasicNotions.Examples₂.star_isIntegral n, rfl, ?_, ?_, ?_⟩
  · refine Matrix.ext fun i j => ?_
    refine (Formalism.BasicNotions.Examples₂.stdSpace_gram_apply (E := D.host.E) Formalism.BasicNotions.Examples₂.star_isIntegral n (fun _ => false) n 0 i j).trans ?_
    rw [Matrix.one_apply]
    by_cases h : i = j <;> simp [h, Formalism.BasicNotions.Examples₂.sgn] <;> first | rfl | exact h
  · exact Formalism.BasicNotions.Examples₂.posSpace_sigOK _ n
  · exact fun _ => Or.inl rfl

end GlobalTheory.StdDefSpace
