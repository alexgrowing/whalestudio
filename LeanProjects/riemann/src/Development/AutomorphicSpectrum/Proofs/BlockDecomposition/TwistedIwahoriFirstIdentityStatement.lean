import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TwistedIwahoriFirstIdentity
import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.LocalBaseChange.ElementaryCosets.JPred
open GlobalTheory.PRep GlobalTheory.SmGL ValuativeRel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twisted_iwahori_first_identity : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], PositivityTheory.Lbc.E1 k := by
  first | exact @GlobalTheory.CompanionTheory.Lbc.Contraction.e1 | exact GlobalTheory.CompanionTheory.Lbc.Contraction.e1 | (intros; apply GlobalTheory.CompanionTheory.Lbc.Contraction.e1 <;> assumption)
