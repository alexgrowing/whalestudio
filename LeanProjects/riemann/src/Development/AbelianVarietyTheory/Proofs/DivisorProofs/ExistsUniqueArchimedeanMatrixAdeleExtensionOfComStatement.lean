import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueArchimedeanMatrixAdeleExtensionOfCom
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFockMap
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
open scoped TensorProduct Matrix Classical GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.existsUnique_archimedeanMatrix_adeleExtension_of_components : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) {α β : Type}
    [Fintype α] [Fintype β] (τ : ∀ w : InfinitePlace F, EmbOver E w), IsCMExt F E σ →
    ∀ M : InfinitePlace F → Matrix α β ℂ, ∃! u : Matrix α β (AE F E), At (evI F) u ∧ ∀ w, u.map (piInf (τ w)) = M w := by
  first | exact @GlobalTheory.ArchMatCoords.existsUnique_at_map_piInf | exact GlobalTheory.ArchMatCoords.existsUnique_at_map_piInf | (intros; apply GlobalTheory.ArchMatCoords.existsUnique_at_map_piInf <;> assumption)
