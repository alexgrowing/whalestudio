import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InstPreorder
open IsLocalRing GlobalTheory.Henselisation

namespace GlobalTheory.Henselisation

theorem EtNbhd.base_le_all {R : Type} [CommRing R] [IsLocalRing R] (i : EtNbhd R) :
    EtNbhd.base ≤ i := by
  refine ⟨Ideal.Quotient.liftₐ _ (MvPolynomial.aeval (R := R) (S₁ := i.A) Fin.elim0) ?_, ?_⟩
  · intro a ha
    have hcomp : (MvPolynomial.aeval (R := R) (S₁ := i.A) Fin.elim0) =
        (Algebra.ofId R i.A).comp (MvPolynomial.isEmptyAlgEquiv R (Fin 0)).toAlgHom :=
      MvPolynomial.algHom_ext fun x => x.elim0
    have ha' : (MvPolynomial.isEmptyAlgEquiv R (Fin 0)).toAlgHom a = 0 := ha
    exact (DFunLike.congr_fun hcomp a).trans ((congrArg (Algebra.ofId R i.A) ha').trans (map_zero _))
  · exact Ideal.Quotient.algHom_ext R (MvPolynomial.algHom_ext fun x => x.elim0)

theorem Hens.of_algebraMap (R : Type) [CommRing R] [IsLocalRing R] (i : EtNbhd R) (r : R) :
    Hens.of i (algebraMap R i.B r) = algebraMap R (Hens R) r := by
  have h := EtNbhd.base_le_all i
  change Hens.of i (algebraMap R i.B r) = Hens.of EtNbhd.base (algebraMap R EtNbhd.base.B r)
  have e : Hens.of EtNbhd.base (algebraMap R EtNbhd.base.B r) =
      Hens.of i (EtNbhd.trans h (algebraMap R EtNbhd.base.B r)) :=
    (Ring.DirectLimit.of_f (G := fun i : EtNbhd R => i.B) (f := fun _ _ h => ⇑(EtNbhd.trans h)) h _).symm
  rw [e]
  congr 1
  rw [IsScalarTower.algebraMap_apply R (EtNbhd.base (R := R)).A (EtNbhd.base (R := R)).B r, EtNbhd.trans,
    Localization.localRingHom_to_map, RingHom.coe_coe, AlgHom.commutes,
    ← IsScalarTower.algebraMap_apply R i.A i.B r]

end GlobalTheory.Henselisation
