import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PartialFourierPsiKPreservesTestFunctions
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WHyp
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SelfDualMeasureExistsUniqueFourierInversionStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EtaleHermitianPairStructureFactsStatement
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.partialFourier_psiK_preserves_testFunctions : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (ψ : AddChar F ℂ), IsStdChar ψ → ∀ (x : A.Kˣ) (ν : Measure A.K), ν.IsAddHaarMeasure → ∀ Φ : A.K × A.K → ℂ, IsTest Φ → IsTest (Hyp.pt A ν ψ x Φ) := by
  first | exact @GlobalTheory.JR.Hyp.pt_isTest | exact GlobalTheory.JR.Hyp.pt_isTest | (intros; apply GlobalTheory.JR.Hyp.pt_isTest <;> assumption)
