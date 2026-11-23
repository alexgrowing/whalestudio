import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchimedeanUnitaryApproximation
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiffsZeroOfLev
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RealPlaceComponentAdeleConjugationEqComplexConj
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DarbouxAdaptedPlaneEvaluation
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.StabiliserEqCentraliserCartan
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IwasawaIsotropicColumnsRingIsoComplex
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueArchimedeanMatrixAdeleExtensionOfCom
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfAtOfPiInf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAtEvIPiInfEq
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.DescB
open GlobalTheory.Doubling (absE)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.archimedean_unitary_approximation : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (τ : ∀ w : InfinitePlace F, EmbOver E w) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (k k' : InfinitePlace F → Matrix (Fin n) (Fin n) ℂ), IsCMExt F E σ → (∀ w, k w * k' w = 1) → (∀ w, (k w)ᵀ * J.map (τ w).1 * (k w).map star = J.map (τ w).1) → ∃ K : UA σ J, At (evI F) (mat K - 1) ∧ ∀ w, (mat K).map (piInf (τ w)) = k w := by
  first | exact @GlobalTheory.ArchGlueMat.exists_unitary_glue | exact GlobalTheory.ArchGlueMat.exists_unitary_glue | (intros; apply GlobalTheory.ArchGlueMat.exists_unitary_glue <;> assumption)
