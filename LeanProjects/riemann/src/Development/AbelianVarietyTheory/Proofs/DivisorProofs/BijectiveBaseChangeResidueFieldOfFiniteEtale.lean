import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsEquivalenceFiniteEtaleBaseChangeResidueField

open IsLocalRing

namespace GlobalTheory

theorem bijective_baseChange_residueField_of_finiteEtale :
    ∀ (R A B : Type) [CommRing R] [HenselianLocalRing R] [CommRing A] [CommRing B] [Algebra R A]
      [Algebra R B] [Algebra.Etale R A] [Module.Finite R A] [Algebra.Etale R B]
      [Module.Finite R B],
      Function.Bijective (fun φ : A →ₐ[R] B =>
        Algebra.TensorProduct.map (AlgHom.id (ResidueField R) (ResidueField R)) φ) :=
  fun R A B _ _ _ _ _ _ _ _ _ _ => bijective_baseChange_residueField_of_etale R A B

end GlobalTheory
