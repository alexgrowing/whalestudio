import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelProjectiveGenericFibre
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsSubFibreSubFib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsExcisionNbhdAway
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lie_model_projective_generic_fibre : ∀ (X : Scheme.{0}) (G : Over X) [GrpObj G] (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X) (Li : Type) [AddCommGroup Li] [Module Ω Li] (M : LieModel G ξ Li) (L : Type) [Field L] [NumberField L] (z : Sp (𝓞 L) ⟶ X) (V : Type) [AddCommGroup V] [Module (𝓞 L) V] [Module.Finite (𝓞 L) V] [Module.Projective (𝓞 L) V] (MB : LieModel G z V) (T : Type) [AddCommGroup T] [Module L T] [Module (𝓞 L) T] [IsScalarTower (𝓞 L) L T] (TL : LieModel G (spMap (algebraMap (𝓞 L) L) ≫ z) T) (j : V →ₗ[𝓞 L] T) (U : Submodule Ω Li), IsCptGen ξ → (∀ x, MB.Lifts (algebraMap (𝓞 L) L) (𝟙 G.left) x (TL.pt (j x))) → IsBaseChange L j → Module.finrank (𝓞 L) V = Module.finrank L T ∧ Module.finrank (𝓞 L) (FlagFib.subFib M U z MB) = Module.finrank L (Submodule.span L {w | ∃ e ∈ U, M.ValAt (spMap (algebraMap (𝓞 L) L) ≫ z) e (TL.pt w)}) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.FlagFib.Bridge.finrank_subFib | exact GlobalTheory.CompanionTheory.Ar.FlagFib.Bridge.finrank_subFib | (intros; apply GlobalTheory.CompanionTheory.Ar.FlagFib.Bridge.finrank_subFib <;> assumption)
