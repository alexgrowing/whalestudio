import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EtaGramDetEqOneOfSelfDualLattice
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitLemmaGroup
open GlobalTheory.UnitLemma Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eta_gramDet_eq_one_of_selfDual_lattice : ∀ (K : UQ) (B : InvAlg K) (x : B.A), B.σ x = x → (B.X x).Nonempty → K.eta (B.gramDet x) = 1 := by
  first | exact @GlobalTheory.UnitLemma.Unimod.eta_gramDet_eq_one | exact GlobalTheory.UnitLemma.Unimod.eta_gramDet_eq_one | (intros; apply GlobalTheory.UnitLemma.Unimod.eta_gramDet_eq_one <;> assumption)
