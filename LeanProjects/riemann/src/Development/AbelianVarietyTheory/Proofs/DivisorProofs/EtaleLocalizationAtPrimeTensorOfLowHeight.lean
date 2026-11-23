import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionFreeOver
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GalMapGalElt

open scoped TensorProduct

namespace GlobalTheory.GoodEtale

theorem etale_localization_of_etaleLow : ∀ (A R C O : Type) [CommRing A] [CommRing R] [Algebra A R] [CommRing C] [Algebra R C]
    [CommRing O] [Algebra R O] (Q : Ideal O) [Q.IsPrime],
    GlobalTheory.GoodEtale.EtaleLow A R C → ((Q.comap (algebraMap R O)).comap (algebraMap A R)).height ≤ 1 →
    Algebra.Etale (Localization.AtPrime Q) (Localization.AtPrime Q ⊗[R] C) := by
  intro A R C O _ _ _ _ _ _ _ Q _ hE hh
  have h := hE (Q.comap (algebraMap R O)) hh
  letI : Algebra (Localization.AtPrime (Q.comap (algebraMap R O))) (Localization.AtPrime Q) :=
    (Localization.localRingHom _ Q (algebraMap R O) rfl).toAlgebra
  haveI : IsScalarTower R (Localization.AtPrime (Q.comap (algebraMap R O))) (Localization.AtPrime Q) := by
    refine IsScalarTower.of_algebraMap_eq (fun a => ?_)
    simp [RingHom.algebraMap_toAlgebra, Localization.localRingHom_to_map,
      IsScalarTower.algebraMap_apply R O (Localization.AtPrime Q)]
  haveI := Algebra.Etale.baseChange (R := Localization.AtPrime (Q.comap (algebraMap R O)))
    (B := Localization.AtPrime Q) (A := Localization.AtPrime (Q.comap (algebraMap R O)) ⊗[R] C)
  exact Algebra.Etale.of_equiv (Algebra.TensorProduct.cancelBaseChange R
    (Localization.AtPrime (Q.comap (algebraMap R O))) (Localization.AtPrime Q) (Localization.AtPrime Q) C)

example : ∀ (A R C O : Type) [CommRing A] [CommRing R] [Algebra A R] [CommRing C] [Algebra R C]
    [CommRing O] [Algebra R O] (Q : Ideal O) [Q.IsPrime],
    GlobalTheory.GoodEtale.EtaleLow A R C → ((Q.comap (algebraMap R O)).comap (algebraMap A R)).height ≤ 1 →
    Algebra.Etale (Localization.AtPrime Q) (Localization.AtPrime Q ⊗[R] C) := etale_localization_of_etaleLow

end GlobalTheory.GoodEtale
