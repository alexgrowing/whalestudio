import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InstPreorder
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PointedEtaleNbhdTransitionMapDirectedSystemStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PointedEtaleNeighbourhoodLocalRingIsDirectedStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleNbhdLocalRingTransitionMapIsLocalHomInjectiStatement

open IsLocalRing GlobalTheory.Henselisation

namespace GlobalTheory.Henselisation

theorem Hens.of_injective_of_nbhd (R : Type) [CommRing R] [IsLocalRing R] (i : EtNbhd R) :
    Function.Injective (Hens.of i) := by
  have : IsDirected (EtNbhd R) (· ≤ ·) := GlobalTheory.T.pointedEtaleNeighbourhoodLocalRing_isDirected R
  have : DirectedSystem (fun j : EtNbhd R => j.B) (fun _ _ h => ⇑(EtNbhd.trans h)) :=
    ⟨fun j x => (GlobalTheory.T.pointedEtaleNbhd_transitionMap_directedSystem R).1 j x,
      fun k j l hlj hjk x => (GlobalTheory.T.pointedEtaleNbhd_transitionMap_directedSystem R).2 l j k hlj hjk x⟩
  exact Ring.DirectLimit.of_injective (G := fun j : EtNbhd R => j.B) (fun _ _ h => EtNbhd.trans h)
    (fun _ _ h => (GlobalTheory.T.etaleNbhdLocalRingTransitionMap_isLocalHom_injective R _ _ h).2) i

end GlobalTheory.Henselisation
