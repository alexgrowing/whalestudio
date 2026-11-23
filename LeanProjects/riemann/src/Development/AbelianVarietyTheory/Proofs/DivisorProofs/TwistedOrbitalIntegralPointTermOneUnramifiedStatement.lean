import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedOrbitalIntegralPointTermOneUnramified
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.T2SpaceFiniteAdeleRing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwOrbEqFinsumTwTerm
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twistedOrbitalIntegralPointTerm_one_unramified : ∀ {G : Type} [Group G] [TopologicalSpace G] (θ : G →* G) (K : Subgroup G) (δ : G), (∀ k ∈ K, θ k ∈ K) → δ ∈ K → cptPart (twCent θ δ) ≤ K → GlobalTheory.EulerAbs.twTerm θ K δ ((K : Set G).indicator 1) 1 = 1 := by
  first | exact @GlobalTheory.EulerAbs.twTerm_one_eq_one | exact GlobalTheory.EulerAbs.twTerm_one_eq_one | (intros; apply GlobalTheory.EulerAbs.twTerm_one_eq_one <;> assumption)
