import ReciprocityTheory.DualLattices.TensorSpan

noncomputable section

namespace ReciprocityTheory.PGsh.L2

variable {C : Type} [Field C] {R : Type} [CommRing R] [Algebra R C]

def SubgroupQuotientStatement : Prop :=
  ∀ (v : Valuation C NNReal), v.Integers R →
  ∀ (N : Type) [AddCommGroup N] [Fintype N] [DecidableEq N] (K : AddSubgroup N)
    [DecidablePred (· ∈ K)] [DecidableEq (N ⧸ K)] [Fintype (N ⧸ K)]
    (AA : HopfOrder (C := C) R N),
    (∃ AK : HopfOrder (C := C) R K, AK.carrier = AA.carrier.map (resK K)) ∧
    (∃ AQ : HopfOrder (C := C) R (N ⧸ K), AQ.carrier = AA.carrier.comap (pullQ K)) ∧
    dualLat (AA.carrier.map (resK (R := R) K)) = (dualLat AA.carrier).comap (extK K) ∧
    dualLat (AA.carrier.comap (pullQ (R := R) K)) = (dualLat AA.carrier).map (pushQ K)

end ReciprocityTheory.PGsh.L2
