import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VacuumProductExistsNonzero
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EvFinMkPt

open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.FinComm GlobalTheory.VacLine

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.vacuum_product_exists_nonzero : ∀ {F : Type} [Field F] [NumberField F] {κ : Type} (vac : ∀ v : Pl F, (κ → Fv F v) → ℂ), (∀ v, vac v ≠ 0) →
    (∀ᶠ v in cofinite, vac v = indO v) → ∃ y : κ → Af F, vacProd vac y ≠ 0 := by
  first | exact @GlobalTheory.VacLine.vacProd_ne_zero_somewhere | exact GlobalTheory.VacLine.vacProd_ne_zero_somewhere | (intros; apply GlobalTheory.VacLine.vacProd_ne_zero_somewhere <;> assumption)
