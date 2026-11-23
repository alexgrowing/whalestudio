import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.SegmentCuspLines.CuspLinesIrr
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.UnipotentDerivatives.DerUnipLeUnipB
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.TwistedKernels.ExPhiPlusOnto
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.GeometricLemmaFiltration
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MirabolicPhiMinusExact
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MirabolicPsiMinusExact
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SmoothPhiMinus
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SmoothPsiMinus
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZSeg GlobalTheory.BZMir Zc

namespace GlobalTheory.CompanionTheory.BZMirSub

section Tw

variable {G V W : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

end Tw

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem isSmooth_resM {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL (Fin (n + 1)) k) V) (h : IsSmooth π) : IsSmooth (resM k π).ρ := fun v =>
  (h v).preimage continuous_subtype_val

end GlobalTheory.CompanionTheory.BZMirSub
