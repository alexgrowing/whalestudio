import Mathlib

open MeasureTheory Pointwise

namespace GlobalTheory.SupMeas

noncomputable def supMeas {G : Type} [Group G] [MeasurableSpace G] (N Q : Subgroup G) (νN : Measure N) :
    Measure ↥(Q ⊔ N) :=
  Measure.sum fun k : ↥(Q ⊔ N) ⧸ N.subgroupOf (Q ⊔ N) =>
    νN.map fun n => Subgroup.inclusion (le_sup_right : N ≤ Q ⊔ N) n * Quotient.out k

end GlobalTheory.SupMeas
