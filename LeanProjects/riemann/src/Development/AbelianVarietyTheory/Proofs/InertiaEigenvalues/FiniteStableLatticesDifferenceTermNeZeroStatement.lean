import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteStableLatticesDifferenceTermNeZero
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitLemmaGroup
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LinearDescent
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DltEqZero
open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Desc Polynomial Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_stableLattices_differenceTerm_ne_zero : ∀ (K : UQ) (B : InvAlg K) (ι : Type) [Fintype ι] (e π : ι → B.A) (S : Finset ι), B.P.Separable → IsFrame B e π S → ∀ (I I' : Finset ι), I ⊆ S → I' ⊆ S → ∀ u s : B.A, IsUnit u → IsUnit s → {M ∈ B.Lin | term B π I I' u s M ≠ 0}.Finite := by
  first | exact @GlobalTheory.UnitLemma.Desc.finite_term_ne_zero | exact GlobalTheory.UnitLemma.Desc.finite_term_ne_zero | (intros; apply GlobalTheory.UnitLemma.Desc.finite_term_ne_zero <;> assumption)
