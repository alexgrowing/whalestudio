import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianIsotropicVectorCartan
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
theorem _root_.GlobalTheory.T.hermitian_isotropic_vector_cartan : ∀ {n : ℕ} (M θ g g' : Matrix (Fin n) (Fin n) ℂ) (x : Fin n → ℂ), Mᴴ = M → IsCartan M θ → g * g' = 1 → gᵀ * M * g.map star = M → x ≠ 0 → x ⬝ᵥ M *ᵥ star x = 0 → ∃ k k' : Matrix (Fin n) (Fin n) ℂ, k * k' = 1 ∧ kᵀ * M * k.map star = M ∧ Commute k θ ∧ ∃ β : ℂ, β ≠ 0 ∧ (g * k') *ᵥ x = β • x := by
  first | exact @GlobalTheory.IwArchLocal.iwasawa_arch_isotropic_line | exact GlobalTheory.IwArchLocal.iwasawa_arch_isotropic_line | (intros; apply GlobalTheory.IwArchLocal.iwasawa_arch_isotropic_line <;> assumption)
