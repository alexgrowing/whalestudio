import Mathlib
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.SubDegreeBotAndMaxExists
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsSplitGaussChars
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.GapCondExample
open GlobalTheory.CompanionTheory.Ar.Crv
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sub_degree_bot_and_max_exists : ∀ (K : Type) [Field K] (C : ACurve K) (V : Type) [AddCommGroup V] [Module K V] [FiniteDimensional K V] (L : C.I → AddSubgroup V), IsBun C L → subDeg C L ⊥ = 0 ∧ ∃ W₀ : Submodule K V, ∀ W : Submodule K V, subDeg C L W ≤ subDeg C L W₀ := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Crv.SubdegMax.subDeg_max | exact GlobalTheory.CompanionTheory.Ar.Crv.SubdegMax.subDeg_max | (intros; apply GlobalTheory.CompanionTheory.Ar.Crv.SubdegMax.subDeg_max <;> assumption)
