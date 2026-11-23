import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCrossRelationSectionsAmpleSourcePower
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusHomOfIff
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.TwistBaseChangeAndValuationStatements
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_crossRelation_sections_ample_source_power : ∀ (R : Type) [CommRing R] [IsDomain R] (A₁ A₂ : PolAV (Sp (FractionRing R))) (F : Type) [Field F] [Algebra (FractionRing R) F] (c : A₁.A ⟶ A₂.A), IsMonHom c → ∀ (j k : ℕ), 1 ≤ k → ∃ n, 1 ≤ n ∧ ∀ t₁ t₂ : SecA A₂ F j, ∃ t₁' t₂' : SecA A₁ F (k * n), CrossH c t₁ t₂ t₁' t₂' ∧ ((∀ z J, Good A₂.L z J → sA t₂ (ptSecT A₂.A 1).left z J ≠ 0) → (∀ z J, Good A₁.L z J → sA t₂' (ptSecT A₁.A 1).left z J ≠ 0)) := by
  first | exact @GlobalTheory.Mum.Two.exists_crossH | exact GlobalTheory.Mum.Two.exists_crossH | (intros; apply GlobalTheory.Mum.Two.exists_crossH <;> assumption)
