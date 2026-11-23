import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TracePairingNondegenerate
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinRel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TrPApply
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ArchSch

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.trace_pairing_nondegenerate : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ], (trP F κ).Nondegenerate := by
  first | exact @GlobalTheory.ArchSch.mixedTracePairing_nondegenerate | exact GlobalTheory.ArchSch.mixedTracePairing_nondegenerate | (intros; apply GlobalTheory.ArchSch.mixedTracePairing_nondegenerate <;> assumption)
