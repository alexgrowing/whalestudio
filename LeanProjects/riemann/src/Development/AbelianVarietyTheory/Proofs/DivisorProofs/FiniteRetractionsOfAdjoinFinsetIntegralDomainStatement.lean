import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteRetractionsOfAdjoinFinsetIntegralDomain
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HInv
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RingKrullDimLtTopOfEssFiniteType
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_retractions_of_adjoin_finset_integral_domain : ∀ (D T E : Type) [CommRing D] [IsDomain D] [CommRing T] [IsDomain T] [Algebra D T] [CommRing E] [Algebra D E] [Algebra.IsIntegral D E] (ι : T →ₐ[D] E) (F : Finset E), Algebra.adjoin D (Set.range ι ∪ (F : Set E)) = ⊤ → {χ : E →ₐ[D] T | χ.comp ι = AlgHom.id D T}.Finite := by
  first | (exact @GlobalTheory.finite_retractions_of_adjoin_finset_integral') | (exact GlobalTheory.finite_retractions_of_adjoin_finset_integral') | (intros; apply GlobalTheory.finite_retractions_of_adjoin_finset_integral'  <;> assumption)
