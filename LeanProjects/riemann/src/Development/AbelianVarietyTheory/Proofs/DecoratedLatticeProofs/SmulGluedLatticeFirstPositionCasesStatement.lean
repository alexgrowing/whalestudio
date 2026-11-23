import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SmulGluedLatticeFirstPositionCases
import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DiesOnRamOfInvariant
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.DualLiftInvariance
open GlobalTheory.LatPair ValuativeRel
open scoped Pointwise
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer lastPair)
open GlobalTheory.RootEx (embX)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.smul_gluedLatticeFirstPosition_cases : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : Type) [Fintype n] [DecidableEq n] (q : Unif k) (P : Pair k n) (h : GL (n ⊕ Fin 1) k), (Pi.single (Sum.inr 0) 1 : n ⊕ Fin 1 → k) ∈ h • gluedS q 1 P.ker P.vec → (∀ x ∈ h • gluedS q 1 P.ker P.vec, (q.1 : k) * x (Sum.inr 0) ∈ 𝒪[k]) → (∃ (Λ : Submodule 𝒪[k] (n → k)) (_ : Λ.IsLattice k), h • gluedS q 1 P.ker P.vec = lastKer Λ ∨ h • gluedS q 1 P.ker P.vec = (lastPair q Λ).lat) ∨ ∃ g : GL n k, h • gluedS q 1 P.ker P.vec = embX 1 g • gluedS q 1 P.ker P.vec := by
  first | exact @GlobalTheory.GluedOrbit.smul_gluedS_cases | exact GlobalTheory.GluedOrbit.smul_gluedS_cases | (intros; apply GlobalTheory.GluedOrbit.smul_gluedS_cases <;> assumption)
