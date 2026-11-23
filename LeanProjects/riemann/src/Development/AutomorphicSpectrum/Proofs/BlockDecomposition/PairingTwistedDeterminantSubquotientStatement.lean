import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PairingTwistedDeterminantSubquotient
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.SegmentCuspLines.CuspLinesIrr
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.UnipotentDerivatives.DerUnipLeUnipB
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.TwistedKernels.ExPhiPlusOnto
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.GeometricLemmaFiltration
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZSeg GlobalTheory.BZMir Zc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pairing_twisted_determinant_subquotient : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (n s : ℕ) (V' : Type) [AddCommGroup V'] [Module ℂ V'] (S : IrrRep (GL (Fin n) k))
    (A' : Representation ℂ (GL (Fin n) k) V'), IsSmooth A' → ∀ B : S.V →ₗ[ℂ] V' →ₗ[ℂ] ℂ,
    (∀ g w w', B (S.ρ g w) (A' g w') = ((detChar (Fin n) (absPow k (s : ℂ)) g : ℂˣ) : ℂ) * B w w') → B ≠ 0 →
    ∃ Q : IrrRep (GL (Fin n) k), IsSubquotient Q.ρ A' ∧
      IrrGL.of Q.ρ Q.smooth Q.irr = (dualCl (IrrGL.of S.ρ S.smooth S.irr)).nu (s : ℂ) := by
  first | exact @GlobalTheory.CompanionTheory.DualQuot.exists_subquotient_dual_nu | exact GlobalTheory.CompanionTheory.DualQuot.exists_subquotient_dual_nu | (intros; apply GlobalTheory.CompanionTheory.DualQuot.exists_subquotient_dual_nu <;> assumption)
