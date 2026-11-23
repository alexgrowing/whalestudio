import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.CoordsCompatibleAlongMap
import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.EmbedsGeneric
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GlueApplyOfNotInFibre
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IntegralClosureHeightEqOneOfLiesOver
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.GoodOrigin
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import Development.AutomorphicSpectrum.Statements.GeometryStatements.FlatLineGenerator
import Development.AutomorphicSpectrum.Statements.GeometryStatements.CardComapMulFinsumEqFinsumFibres
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.smoothGenericFibre_of_dominates : ∀ (Ω : Type) [Field Ω] [CharZero Ω] (K₁ : Type) [Fintype K₁] (J₁ : K₁ → Type) [∀ k, Fintype (J₁ k)] (y₁ : (Σ k, J₁ k) → Ω) (K₂ : Type) [Fintype K₂] (J₂ : K₂ → Type) [∀ k, Fintype (J₂ k)] (y₂ : (Σ k, J₂ k) → Ω) (X₁ X₂ : Scheme.{0}) (ξ₁ : Spec (CommRingCat.of Ω) ⟶ X₁) (ξ₂ : Spec (CommRingCat.of Ω) ⟶ X₂) (g : X₂ ⟶ X₁), (∀ q : X₁, GlobalTheory.CompanionTheory.Ar.genPt ξ₁ ⤳ q) → (∀ q : X₂, GlobalTheory.CompanionTheory.Ar.genPt ξ₂ ⤳ q) → CoordTie ℤ ξ₁ (fun c' : (k : K₁) → J₁ k => ∏ k, y₁ ⟨k, c' k⟩) → CoordTie ℤ ξ₂ (fun c' : (k : K₂) → J₂ k => ∏ k, y₂ ⟨k, c' k⟩) → GlobalTheory.CompanionTheory.Ar.Dominates ξ₂ ξ₁ g (RingHom.id Ω) → SmoothGenericFibreM y₁ → (∀ q ∈ genFib ξ₁, IsoAt ξ₂ g (RingHom.id Ω) q) → SmoothGenericFibreM y₂ := by
  first | exact @GlobalTheory.CompanionTheory.Ar.SmoothChange.smoothGenericFibreM_of_isoAt | exact GlobalTheory.CompanionTheory.Ar.SmoothChange.smoothGenericFibreM_of_isoAt | (intros; apply GlobalTheory.CompanionTheory.Ar.SmoothChange.smoothGenericFibreM_of_isoAt <;> assumption)
