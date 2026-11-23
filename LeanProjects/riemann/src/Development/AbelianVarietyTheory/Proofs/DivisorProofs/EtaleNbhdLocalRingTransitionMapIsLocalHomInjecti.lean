import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InstPreorder
open IsLocalRing GlobalTheory.Henselisation

namespace GlobalTheory.Henselisation

theorem EtNbhd.trans_isLocalHom_injective (R : Type) [CommRing R] [IsLocalRing R] (i j : EtNbhd R)
    (h : i ≤ j) : IsLocalHom (EtNbhd.trans h) ∧ Function.Injective (EtNbhd.trans h) := by
  have hloc : IsLocalHom (EtNbhd.trans h) := by
    unfold EtNbhd.trans
    exact Localization.isLocalHom_localRingHom _ _ _ _
  refine ⟨hloc, ?_⟩
  set f : i.A →ₐ[R] j.A := h.choose with hfdef
  letI : Algebra i.A j.A := (f : i.A →+* j.A).toAlgebra
  haveI : IsScalarTower R i.A j.A := IsScalarTower.of_algebraMap_eq (fun r => (f.commutes r).symm)
  haveI : Algebra.Etale i.A j.A := Algebra.Etale.of_restrictScalars R i.A j.A
  have hflat : (f : i.A →+* j.A).Flat := RingHom.flat_algebraMap_iff.mpr inferInstance
  have hB : (EtNbhd.trans h).Flat := RingHom.Flat.localRingHom hflat j.q i.q _
  letI : Algebra i.B j.B := (EtNbhd.trans h).toAlgebra
  haveI : Module.Flat i.B j.B := RingHom.flat_algebraMap_iff.mp hB
  haveI : IsLocalHom (algebraMap i.B j.B) := hloc
  haveI hff : Module.FaithfullyFlat i.B j.B := Module.FaithfullyFlat.of_flat_of_isLocalHom
  exact RingHom.FaithfullyFlat.injective hff

end GlobalTheory.Henselisation
