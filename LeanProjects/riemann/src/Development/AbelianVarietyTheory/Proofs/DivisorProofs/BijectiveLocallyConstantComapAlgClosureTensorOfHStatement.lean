import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BijectiveLocallyConstantComapAlgClosureTensorOfH
import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.bijective_locallyConstant_comap_algClosure_tensor_of_henselian : ∀ (Λ : Type) (A : Type) [CommRing A] [IsLocalRing A] [HenselianLocalRing A] [IsSepClosed (IsLocalRing.ResidueField A)] (B : Type) [CommRing B] [Algebra A B] [Algebra.IsIntegral A B], Function.Bijective (fun φ : LocallyConstant (PrimeSpectrum B) Λ => φ.comap ⟨PrimeSpectrum.comap (Algebra.TensorProduct.includeRight : B →ₐ[A] AlgebraicClosure (IsLocalRing.ResidueField A) ⊗[A] B).toRingHom, PrimeSpectrum.continuous_comap _⟩) := by
  first | exact @GlobalTheory.bijective_locallyConstant_comap_algebraicClosure_tensor | exact GlobalTheory.bijective_locallyConstant_comap_algebraicClosure_tensor | (intros; apply GlobalTheory.bijective_locallyConstant_comap_algebraicClosure_tensor <;> assumption)
