import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdelicRepExtendingArchimedeanSchwartzRep
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFockMap
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_adelicRep_extending_archimedeanSchwartzRep : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] (G : Type) [Group G]
    (ρ : G →* (SInf F κ →L[ℂ] SInf F κ)),
    ∃ ω₀ : G →* Module.End ℂ ((κ → AF F) → ℂ), ∀ (g : G) (f : SInf F κ) (h : (κ → Af F) → ℂ),
      ω₀ g (pureA F f h) = pureA F (ρ g f) h := by
  first | exact @GlobalTheory.SliceExt.exists_rep_pure | exact GlobalTheory.SliceExt.exists_rep_pure | (intros; apply GlobalTheory.SliceExt.exists_rep_pure <;> assumption)
