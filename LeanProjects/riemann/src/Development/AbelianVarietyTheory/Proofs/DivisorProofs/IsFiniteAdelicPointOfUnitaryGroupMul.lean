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

namespace GlobalTheory.FinPtMul

theorem isFinPt_mul : ∀ {D : D7} (V : HSp D) {n : ℕ} (g g' : GA D V) (x x' : Formalism.MainNotions.StandardLatticesGL3.GA D n),
  IsFinPt V g x → IsFinPt V g' x' → IsFinPt V (g * g') (x * x') := by
  intro D V n g g' x x' hx hx'
  obtain ⟨hg, e, h⟩ := hx
  obtain ⟨hg', e', h'⟩ := hx'
  subst e
  refine ⟨mul_mem hg hg', rfl, fun i j => ?_⟩
  simp only [map_mul, Units.val_mul, Subgroup.coe_mul, Matrix.mul_apply, map_sum, Fin.cast_eq_self]
  refine Finset.sum_congr rfl fun k _ => ?_
  have a := h i k
  have b := h' k j
  simp only [Fin.cast_eq_self] at a b
  rw [a, b]

end GlobalTheory.FinPtMul
