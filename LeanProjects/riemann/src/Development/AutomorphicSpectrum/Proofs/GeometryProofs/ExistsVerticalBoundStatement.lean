import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsVerticalBound
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ArchBetween
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo NumberField GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top GlobalTheory.CompanionTheory.Ar.Small GlobalTheory.CompanionTheory.Ar.Cmp GlobalTheory.CompanionTheory.Ar.Ht
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_vertical_bound : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] (y : (Σ k, ι k) → Ω) (d : ℕ), IsArithVar (mCoordIdeal y) d → Birational y → ∀ (a : K → ℤ) (u : Ω), GenUnit y a u → ∃ c : ℝ, VertBound y a u c := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Vert.exists_vertBound | exact GlobalTheory.CompanionTheory.Ar.Vert.exists_vertBound | (intros; apply GlobalTheory.CompanionTheory.Ar.Vert.exists_vertBound <;> assumption)
