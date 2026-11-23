import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryLieOneParameterIsRealOneParamSubgroupAdel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemSupportWordMul
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th GlobalTheory.UAut
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitary_lie_one_parameter_isRealOneParamSubgroupAdelic : ∀ (D : D7) (θ : InfF D), IsInfFam θ → ∀ (V : HSp D) (τ : D.what₂.Tau) (X : Matrix (Fin V.rank) (Fin V.rank) ℂ), X ∈ lieAt V τ → GlobalTheory.SiegelSet.IsRealLine D.sp.cm.sig V.gram (oneP θ V τ X) := by
  first | exact @GlobalTheory.UAut.isRealLine_oneP | exact GlobalTheory.UAut.isRealLine_oneP | (intros; apply GlobalTheory.UAut.isRealLine_oneP <;> assumption)
