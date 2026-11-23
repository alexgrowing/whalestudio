import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeTateLatticeLeOmega
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.AdelicGroupAlgebraActionInjective
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsHTFormOver
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PushInvertible
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GlueApplyOfNotInFibre
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hodge_tate_lattice_le_omega : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X) (G : Over X) [GrpObj G] [IsCommMonObj G] (V : Type) [AddCommGroup V] [Module Ω V] (M : LieModel G ξ V) (N : ℕ) (p : Cpt ξ), IsCptGen ξ → Smooth G.hom → M.htLat N p ≤ M.omLat p ∧ (M.IsHTFormAt N p 0 → ∀ w ∈ M.omLat p, (N : Ω) • w ∈ M.htLat N p) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.htLat_le_omLat_and_smul_mem | exact GlobalTheory.CompanionTheory.Ar.htLat_le_omLat_and_smul_mem | (intros; apply GlobalTheory.CompanionTheory.Ar.htLat_le_omLat_and_smul_mem <;> assumption)
