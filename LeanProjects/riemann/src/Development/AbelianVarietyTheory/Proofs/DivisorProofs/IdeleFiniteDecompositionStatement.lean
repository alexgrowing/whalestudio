import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdeleFiniteDecomposition
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToGAdMat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLeviLeviElt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdelesInf
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)
open GlobalTheory.UAut GlobalTheory.SiegelSet GlobalTheory.ThK.SquareIntegrability GlobalTheory.ThKCtFin
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.idele_finite_decomposition : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (U : Subgroup (AE F E)ˣ), IsOpen (U : Set (AE F E)ˣ) → ∃ C : Finset (AE F E)ˣ, ∀ t : (AE F E)ˣ, ∃ γ : Eˣ, ∃ c ∈ C, ∃ a ∈ idelesInf F E, ∃ u ∈ U, u ∈ idelesFin F E ∧ t = Units.map (inclR (F := F) (AF F)).toMonoidHom γ * c * a * u := by
  first | exact @GlobalTheory.ThKCtFin.idele_classes_finite | exact GlobalTheory.ThKCtFin.idele_classes_finite | (intros; apply GlobalTheory.ThKCtFin.idele_classes_finite <;> assumption)
