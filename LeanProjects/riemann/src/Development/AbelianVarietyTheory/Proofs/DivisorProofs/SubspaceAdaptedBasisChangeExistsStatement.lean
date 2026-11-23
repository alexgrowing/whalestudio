import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SubspaceAdaptedBasisChangeExists
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigenIntertwinerGoodModels
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepresentationPreservesSchwartz
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaTransformRationalTranslateQuasiInvariant
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharacterInvariantAdelicFormEqMulEvalZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TranslationInvariantFunctionalRestrict
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsRealisedOnAdelicSchwartzLeviInverseTranspose

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

open scoped Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.subspace_adapted_basis_change_exists : ∀ (F : Type) [Field F] (κ : Type) [Fintype κ] [DecidableEq κ] (Y₀ : Submodule F (κ → F)),
    ∃ P : Matrix κ κ F, IsUnit P.det ∧ ∃ s : Set κ, (∀ i ∈ s, P i ∈ Y₀) ∧
      ∀ y ∈ Y₀, ∃ c : κ → F, (∀ i ∉ s, c i = 0) ∧ y = Matrix.vecMul c P := by
  first | exact @GlobalTheory.exists_invertible_matrix_rows_span | exact GlobalTheory.exists_invertible_matrix_rows_span | (intros; apply GlobalTheory.exists_invertible_matrix_rows_span <;> assumption)
