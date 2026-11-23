import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchimedeanTracePairingBilinearNondegenerate
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFockMap
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TrPairApply
open scoped TensorProduct Matrix GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Classical
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift GlobalTheory.VacLn
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.archimedeanTracePairingBilinear_nondegenerate : ∀ {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] (y : κ → mixedEmbedding.mixedSpace F),
    (∀ x, trPair F κ x y = 0) → y = 0 := by
  first | exact @GlobalTheory.VacLn.trPair_nondeg | exact GlobalTheory.VacLn.trPair_nondeg | (intros; apply GlobalTheory.VacLn.trPair_nondeg <;> assumption)
