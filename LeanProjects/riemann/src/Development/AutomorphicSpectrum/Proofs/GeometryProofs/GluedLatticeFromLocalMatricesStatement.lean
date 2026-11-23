import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GluedLatticeFromLocalMatrices
import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.PotentialsBoundedRegSettingEqReference
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LocRatio
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsValues
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GlobalTheory.CompanionTheory.Ar.Cusp.PtHt
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.glued_lattice_from_local_matrices : ∀ (L : Type) [Field L] [NumberField L] (V : Type) [AddCommGroup V] [Module L V] [Module (𝓞 L) V] [IsScalarTower (𝓞 L) L V] (n : ℕ) (g : Fin n → V) (F : Submodule (𝓞 L) V) (T : FinitePlace L → Matrix (Fin n) (Fin n) L) (C : Matrix (Fin n) (Fin n) L), LinearIndependent L g → (∀ v, (T v).det ≠ 0) → C.det ≠ 0 → {v : FinitePlace L | ¬ ((∀ i j, v (T v i j) ≤ 1) ∧ v (T v).det = 1)}.Finite → (∀ x, x ∈ F ↔ x ∈ Submodule.span L (Set.range g) ∧ ∀ v : FinitePlace L, ∃ t : 𝓞 L, t ∉ v.maximalIdeal.asIdeal ∧ t • x ∈ Submodule.span (𝓞 L) (Set.range fun k => ∑ j, T v j k • g j)) → logIdx F (fun k => ∑ j, C j k • g j) = (∑ᶠ v : FinitePlace L, Real.log (v (T v).det)) + ∑ σ : L →+* ℂ, Real.log ‖σ C.det‖ := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cusp.LocFrame.logIdx_localFrames | exact GlobalTheory.CompanionTheory.Ar.Cusp.LocFrame.logIdx_localFrames | (intros; apply GlobalTheory.CompanionTheory.Ar.Cusp.LocFrame.logIdx_localFrames <;> assumption)
