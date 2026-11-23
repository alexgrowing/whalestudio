import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ThetaOfTiltCompatibleSequence
import Mathlib
import Development.AbelianVarietyTheory.Statements.WeilDeligneCrystalline.ColmezLT
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormLtOneOfNotIsUnit
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsKerPowDvd
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AwayOfInjective
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NonemptyLocalPeriodRingsData
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.PZ GlobalTheory.BKReal GlobalTheory.Prism Formalism.BasicNotions.Examples₂.LB GlobalTheory.MemLoc GlobalTheory.AinfK GlobalTheory.AcrisK GlobalTheory.DiscEval GroundTheory.LocalField.FormalGroup
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_of_tilt_compatible_sequence : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (π : ↥(OL K)), Irreducible π → ∀ (v : ℕ → OC l) (ω : ℕ → AK K),
    (∀ n, intToOC K π * v (n + 1) + v (n + 1) ^ l ^ fK K = v n) →
    GlobalTheory.LTTilt.IsTiltOf (fK K) (intToOC K π) (red K (ω 0)) v → (∀ n, frobq K (ω (n + 1)) = ω n) →
    frobq K (ω 0) = inO K π * ω 0 + ω 0 ^ l ^ fK K → ∀ n, thetaK K (ω n) = v n := by
  first | exact @GlobalTheory.FrobRoots.thetaK_eq | exact GlobalTheory.FrobRoots.thetaK_eq | (intros; apply GlobalTheory.FrobRoots.thetaK_eq <;> assumption)
