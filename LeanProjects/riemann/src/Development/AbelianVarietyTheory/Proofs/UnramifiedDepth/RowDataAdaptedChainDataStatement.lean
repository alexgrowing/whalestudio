import Mathlib
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.RowDataAdaptedChainData
import Formalism.LocalToGlobal.CharacterGerms.LatticeInclusionFormsInjective
import Formalism.LocalToGlobal.CharacterGerms.CartesianBoundOnCurves
import Formalism.LocalToGlobal.CharacterGerms.CoeffIterateZero
import Formalism.LocalToGlobal.CharacterGerms.ScaledSecondIntegral
open Formalism.L2.FormalSeriesBounds
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rowData_adaptedChainData : ∀ (C : Type) [Field C] (V : VF C) (d : ℕ) [NeZero d] (I J : Fin 2 → Type) [∀ g, Fintype (I g)] [∀ g, Fintype (J g)] (X : RowData C V d I J), X.AdaptedChainData := by
  first | exact @GlobalTheory.AdaptedChain.adaptedChainData | exact GlobalTheory.AdaptedChain.adaptedChainData | (intros; apply GlobalTheory.AdaptedChain.adaptedChainData <;> assumption)
