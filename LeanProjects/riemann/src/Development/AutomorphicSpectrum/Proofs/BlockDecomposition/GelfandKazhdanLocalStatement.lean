import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GelfandKazhdanLocal
import Mathlib
import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.GenericUnlinkedGL.UnlinkedRealize
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.RgGu
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gelfand_kazhdan_local : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], GlobalTheory.Published.IrreducibleAdmissibleGL → Zc.Cos.GKLocal k := by
  first | exact @GlobalTheory.CompanionTheory.GenGK.gkLocal_gen | exact GlobalTheory.CompanionTheory.GenGK.gkLocal_gen | (intros; apply GlobalTheory.CompanionTheory.GenGK.gkLocal_gen <;> assumption)
