import Mathlib
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.SubDegreeMonoInjectiveHom
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsSplitGaussChars
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.GapCondExample
open GlobalTheory.CompanionTheory.Ar.Crv
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sub_degree_mono_injective_hom : ∀ (K : Type) [Field K] (C : ACurve K) (V : Type) [AddCommGroup V] [Module K V] [FiniteDimensional K V] (V' : Type) [AddCommGroup V'] [Module K V'] [FiniteDimensional K V'] (L : C.I → AddSubgroup V) (L' : C.I → AddSubgroup V') (f : V →ₗ[K] V') (W : Submodule K V), IsBun C L → IsBun C L' → Function.Injective f → IsHom C L L' f → subDeg C L W ≤ subDeg C L' (W.map f) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Crv.subDeg_le_map_of_injective | exact GlobalTheory.CompanionTheory.Ar.Crv.subDeg_le_map_of_injective | (intros; apply GlobalTheory.CompanionTheory.Ar.Crv.subDeg_le_map_of_injective <;> assumption)
