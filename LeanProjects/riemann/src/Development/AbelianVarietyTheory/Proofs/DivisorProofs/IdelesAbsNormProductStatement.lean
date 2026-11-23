import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdelesAbsNormProduct
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsCompactIsOpenUnitsAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocCharEqValZpow
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TmulMemLocId
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValuedCompW
open scoped TensorProduct NNReal Matrix nonZeroDivisors
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.UnrEuler GlobalTheory.LocIdeal
open GlobalTheory.Doubling (absE)
open Formalism.L2.Host (aboveF)
open GlobalTheory.TateUnr

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ideles_abs_norm_product : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (v : Pl F)
    (l : idelesAt E (evFin F v)),
    ((absE F E l.1 : ℝ≥0) : ℝ) = ∏ w : aboveF (L := E) F v, ((Ideal.absNorm w.1.asIdeal : ℕ) : ℝ) ^ (-ordV v l w) := by
  first | exact @GlobalTheory.TateUnr.absE_idelesAt | exact GlobalTheory.TateUnr.absE_idelesAt | (intros; apply GlobalTheory.TateUnr.absE_idelesAt <;> assumption)
