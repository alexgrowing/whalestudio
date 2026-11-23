import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InstPreorder
open IsLocalRing GlobalTheory.Henselisation

namespace GlobalTheory.Henselisation.EtNbhd

instance isLocalHom_algebraMap_B {R : Type} [CommRing R] [IsLocalRing R] (i : EtNbhd R) :
    IsLocalHom (algebraMap R i.B) := by
  refine ⟨fun a ha => ?_⟩
  by_contra hna
  have hm : a ∈ maximalIdeal R := hna
  have hq : algebraMap R i.A a ∈ i.q := by
    show i.pt (algebraMap R i.A a) = 0
    rw [AlgHom.commutes]
    exact (residue_eq_zero_iff a).2 hm
  have : algebraMap R i.B a ∈ maximalIdeal i.B := by
    rw [IsScalarTower.algebraMap_apply R i.A i.B]
    exact (IsLocalization.AtPrime.to_map_mem_maximal_iff i.B i.q _).2 hq
  exact this ha

theorem maximalIdeal_B_eq_map (R : Type) [CommRing R] [IsLocalRing R] (i : EtNbhd R) :
    maximalIdeal i.B = (maximalIdeal R).map (algebraMap R i.B) :=
  Algebra.FormallyUnramified.map_maximalIdeal.symm

end GlobalTheory.Henselisation.EtNbhd
