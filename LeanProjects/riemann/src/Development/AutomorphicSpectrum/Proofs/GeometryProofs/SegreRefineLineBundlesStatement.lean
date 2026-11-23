import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.SegreRefineLineBundles
import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IntegralClosureHeightEqOneOfLiesOver
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GlueApplyOfNotInFibre
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GenWeil
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.segre_refine_line_bundles : ∀ (o : Type) [CommRing o] (Ω : Type) [Field Ω] [Algebra o Ω] (κ : Type) [Finite κ] (x : κ → Ω) (M : PModel o x) (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (A : Type) [Finite A] (Λ : A → Lat M.ξ Ω), (∀ p : Cpt M.ξ, ∃ c₀, InChart M.ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) c₀ p) → (∀ a, (Λ a).IsVB 1 ⊤) → ∃ (K' : Type) (_ : Fintype K') (J' : K' → Type) (_ : ∀ k, Fintype (J' k)) (y' : (Σ k, J' k) → Ω) (bk : K → K') (bx : ∀ k, J k ≃ J' (bk k)) (deg : A → K' → ℤ), Function.Injective bk ∧ (∀ k a, y' ⟨bk k, bx k a⟩ = y ⟨k, a⟩) ∧ CoordTie o M.ξ (fun c' : (k : K') → J' k => ∏ k, y' ⟨k, c' k⟩) ∧ ∀ a, (Λ a).IsDegOn Set.univ y' (deg a) 1 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.ExtraBlocks.exists_blocks_of_lines | exact GlobalTheory.CompanionTheory.Ar.ExtraBlocks.exists_blocks_of_lines | (intros; apply GlobalTheory.CompanionTheory.Ar.ExtraBlocks.exists_blocks_of_lines <;> assumption)
