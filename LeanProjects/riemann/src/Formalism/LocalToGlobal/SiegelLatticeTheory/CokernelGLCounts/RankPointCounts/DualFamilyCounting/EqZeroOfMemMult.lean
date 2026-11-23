import Mathlib
import Formalism.FlagUnipotentLattices.MinkowskiFactorialBounds.LatticeSumBounds

noncomputable section

namespace Formalism.L2.SG.Pf.Lem3Mass

open Matrix Formalism.HermitianLatticeCounting.LatticeSumBounds Filter Topology

section Alg

variable {R : Type} [CommRing R] [StarRing R] {m : ℕ}

def Mult (c : R) (N : ℕ) : Set (Matrix (Fin m) (Fin m) R) := {X | ∃ W, X = c ^ N • W}

variable {c : R}

end Alg

section Top

variable {R : Type} [CommRing R] [StarRing R] [TopologicalSpace R] [IsTopologicalRing R] [ContinuousStar R]
  [CompactSpace R] [T2Space R] {m : ℕ}

instance compactSpace_matR : CompactSpace (Matrix (Fin m) (Fin m) R) :=
  inferInstanceAs (CompactSpace (Fin m → Fin m → R))

instance t2SpaceMatrix : T2Space (Matrix (Fin m) (Fin m) R) := inferInstanceAs (T2Space (Fin m → Fin m → R))

end Top

end Formalism.L2.SG.Pf.Lem3Mass
