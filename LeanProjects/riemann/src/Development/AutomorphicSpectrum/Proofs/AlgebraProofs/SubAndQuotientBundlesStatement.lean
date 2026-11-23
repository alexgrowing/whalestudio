import Mathlib
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.SubAndQuotientBundles
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsSplitGaussChars
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.GapCondExample
open GlobalTheory.CompanionTheory.Ar.Crv
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sub_and_quotient_bundles : ∀ (K : Type) [Field K] (C : ACurve K) (V : Type) [AddCommGroup V] [Module K V] [FiniteDimensional K V] (L : C.I → AddSubgroup V) (W : Submodule K V), IsBun C L → IsBun C (sub C L W) ∧ IsBun C (quot C L W) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Crv.SubQuot.isBun_sub_quot | exact GlobalTheory.CompanionTheory.Ar.Crv.SubQuot.isBun_sub_quot | (intros; apply GlobalTheory.CompanionTheory.Ar.Crv.SubQuot.isBun_sub_quot <;> assumption)
