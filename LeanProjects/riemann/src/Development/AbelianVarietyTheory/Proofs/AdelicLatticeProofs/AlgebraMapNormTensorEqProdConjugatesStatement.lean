import Mathlib
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.AlgebraMapNormTensorEqProdConjugates
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.MemPowSub
open NumberField IsDedekindDomain Polynomial GlobalTheory.QNorm GlobalTheory.CNorm
open scoped WithZero TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.algebraMap_norm_tensor_eq_prod_galois_conjugates : ∀ (F E K : Type) [Field F] [Field E] [Algebra F E] [FiniteDimensional F E] [IsGalois F E] [CommRing K] [Algebra F K] (y : K ⊗[F] E), algebraMap K (K ⊗[F] E) (Algebra.norm K y) = ∏ g : E ≃ₐ[F] E, Algebra.TensorProduct.map (AlgHom.id K K) (g : E →ₐ[F] E) y := by
  first | exact @GlobalTheory.CNorm.algebraMap_norm_tensor_eq_prod_conjugates | exact GlobalTheory.CNorm.algebraMap_norm_tensor_eq_prod_conjugates | (intros; apply GlobalTheory.CNorm.algebraMap_norm_tensor_eq_prod_conjugates <;> assumption)
