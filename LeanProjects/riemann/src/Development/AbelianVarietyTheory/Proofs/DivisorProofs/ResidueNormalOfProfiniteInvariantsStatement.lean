import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ResidueNormalOfProfiniteInvariants
import Mathlib
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.residue_normal_of_profinite_invariants : ∀ {A B : Type} [CommRing A] [CommRing B] [Algebra A B] (G : Type) [Group G] [MulSemiringAction G B] [SMulCommClass G A B] [TopologicalSpace G] [CompactSpace G] [TotallyDisconnectedSpace G] [IsTopologicalGroup G] [TopologicalSpace B] [DiscreteTopology B] [ContinuousSMul G B] [Algebra.IsInvariant A B G] (P : Ideal A) (Q : Ideal B) [Q.LiesOver P] [P.IsMaximal] [Q.IsMaximal], letI := Ideal.Quotient.field P; letI := Ideal.Quotient.field Q; Normal (A ⧸ P) (B ⧸ Q) := by
  first | exact @GlobalTheory.Ideal.Quotient.normal_of_profinite | exact GlobalTheory.Ideal.Quotient.normal_of_profinite | (intros; apply GlobalTheory.Ideal.Quotient.normal_of_profinite <;> assumption)
