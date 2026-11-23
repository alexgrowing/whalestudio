import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.SncPatchAtEachComponent
import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsSncPatchRat
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.EmbedsGeneric
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.SncBase
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.snc_patch_at_each_component : ∀ (F : Type) [Field F] [NumberField F] (W : Scheme.{0}) (sW : W ⟶ Sp F) (e : ℕ) (T : Set W) (Ω : Type) [Field Ω] [CharZero Ω] [Algebra F Ω] (ξ' : Sp Ω ⟶ W), IsCptGen ξ' → ξ' ≫ sW = spMap (algebraMap F Ω) → SmoothOfRelativeDimension e sW → ResK.HasSncCoords sW e T → (∀ p q : Cpt ξ', regAt ξ' p = regAt ξ' q → p = q) → ∀ p' : Cpt ξ', ∃ (A : Subalgebra ℚ Ω) (z : Fin e → A) (n : ℕ) (q : Ideal A), IsSncPatch (Set.range (regAt ξ')) (regAt ξ' '' {p | p.1 ∈ T}) e A z n ∧ q.IsPrime ∧ IsLocAt A q (regAt ξ' p') := by
  first | exact @GlobalTheory.CompanionTheory.Ar.SncBase.Patch.exists_patch | exact GlobalTheory.CompanionTheory.Ar.SncBase.Patch.exists_patch | (intros; apply GlobalTheory.CompanionTheory.Ar.SncBase.Patch.exists_patch <;> assumption)
