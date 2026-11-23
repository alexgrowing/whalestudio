import Mathlib
import Formalism.UnipotentAdelicQuotients.ThmBInHecke
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.CmLocalCharacterValueBounded
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.CmCharacterConjugateInverse

open NumberField IsDedekindDomain NumberField.mixedEmbedding Complex Classical HeckeCharacterZeroLocus.ThmBIn
open scoped TensorProduct ContDiff nonZeroDivisors

namespace GlobalTheory

open NumberField IsDedekindDomain NumberField.mixedEmbedding Complex Classical in
open scoped TensorProduct ContDiff nonZeroDivisors in

theorem _root_.GlobalTheory.cA_incA_apply {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] (σ : E →ₐ[F] E) (x : E) :
    _root_.HeckeCharacterZeroLocus.ThmBIn.cA σ (_root_.HeckeCharacterZeroLocus.ThmBIn.incA F E x) = _root_.HeckeCharacterZeroLocus.ThmBIn.incA F E (σ x) := by
  unfold _root_.HeckeCharacterZeroLocus.ThmBIn.cA _root_.HeckeCharacterZeroLocus.ThmBIn.incA _root_.HeckeCharacterZeroLocus.ThmBIn.AE
  exact rfl

end GlobalTheory
