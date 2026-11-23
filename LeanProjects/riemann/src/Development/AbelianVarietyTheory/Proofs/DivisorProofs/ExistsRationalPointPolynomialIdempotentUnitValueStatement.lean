import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRationalPointPolynomialIdempotentUnitValue
import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryAdelicCharacterTrivialOfLocal
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Matrix TensorProduct
open Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_rationalPoint_polynomial_idempotentUnit_value : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (S : Finset (HeightOneSpectrum (𝓞 F))) (ψ : Polynomial (AE F E)), (∀ (Ω : Type) [Field Ω] (φ : AE F E →+* Ω), φ (algebraMap (AF F) (AE F E) (GlobalTheory.LocalGlobalChar.eps S)) = 1 → ψ.map φ ≠ 0) → ∃ t : F, IsUnit (algebraMap (AF F) (AE F E) (GlobalTheory.LocalGlobalChar.eps S) * ψ.eval (algebraMap F (AE F E) t) + (1 - algebraMap (AF F) (AE F E) (GlobalTheory.LocalGlobalChar.eps S))) := by
  first | exact @GlobalTheory.DenseAvoid.exists_unit_eval | exact GlobalTheory.DenseAvoid.exists_unit_eval | (intros; apply GlobalTheory.DenseAvoid.exists_unit_eval <;> assumption)
