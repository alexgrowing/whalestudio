import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnramifiedCharValueProduct
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
theorem _root_.GlobalTheory.T.unramified_char_value_product : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (ν : Chr F E) (v : Pl F),
    (∀ w ∈ aboveF (L := E) F v, UnrAt ν w) → ∀ l : idelesAt E (evFin F v),
    ((ν l.1 : Circle) : ℂ) = ∏ w : aboveF (L := E) F v, ((val ν w.1 ^ ordV v l w : ℂˣ) : ℂ) := by
  first | exact @GlobalTheory.TateUnr.chr_eq_prod_val_zpow | exact GlobalTheory.TateUnr.chr_eq_prod_val_zpow | (intros; apply GlobalTheory.TateUnr.chr_eq_prod_val_zpow <;> assumption)
