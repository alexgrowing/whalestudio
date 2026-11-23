import Mathlib

open Matrix
open scoped Kronecker

namespace PositivityTheory.KB.LargePrimeDiscriminant

variable {R S : Type} [CommRing R] [CommRing S]

noncomputable def resRing (d n : ℕ) (ρ : S →+* Matrix (Fin d) (Fin d) R) :
    Matrix (Fin n) (Fin n) S →+* Matrix (Fin (d * n)) (Fin (d * n)) R :=
  ((Matrix.reindexAlgEquiv R R ((Equiv.prodComm (Fin n) (Fin d)).trans finProdFinEquiv)).toRingEquiv.toRingHom.comp
    (Matrix.compRingEquiv (Fin n) (Fin d) R).toRingHom).comp ρ.mapMatrix

noncomputable def res (d n : ℕ) (ρ : S →+* Matrix (Fin d) (Fin d) R) :
    GL (Fin n) S →* GL (Fin (d * n)) R :=
  Units.map (resRing d n ρ).toMonoidHom

end PositivityTheory.KB.LargePrimeDiscriminant
