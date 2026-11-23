import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSpreadMorphismBasicOpenAgreeFlat
import Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_spread_morphism_basicOpen_agree_flat : ∀ (R : Type) [CommRing R] [IsDomain R] (x : Sp R) (B Z B₀ : Scheme.{0}) (pB : B ⟶ Sp R) (pZ : Z ⟶ Sp R), Flat pB → QuasiCompact pB → QuasiSeparated pB → IsSeparated pZ → LocallyOfFinitePresentation pZ → ∀ (φ₀ : B₀ ⟶ B) (u₀ : B₀ ⟶ Z), Flat φ₀ → u₀ ≫ pZ = φ₀ ≫ pB → ∀ u : Limits.pullback pB ((Sp R).fromSpecStalk x) ⟶ Z, u ≫ pZ = Limits.pullback.fst _ _ ≫ pB → (∀ (T : Scheme.{0}) (t₀ : T ⟶ B₀) (t : T ⟶ Limits.pullback pB ((Sp R).fromSpecStalk x)), t₀ ≫ φ₀ = t ≫ Limits.pullback.fst _ _ → t₀ ≫ u₀ = t ≫ u) → ∃ g : R, g ∉ x.asIdeal ∧ ∀ (Y : Scheme.{0}) (a : Y ⟶ B), (∀ y : Y, g ∉ (pB (a y)).asIdeal) → ∃ u' : Y ⟶ Z, u' ≫ pZ = a ≫ pB ∧ ∀ (T : Scheme.{0}) (t₀ : T ⟶ B₀) (t : T ⟶ Y), t₀ ≫ φ₀ = t ≫ a → t₀ ≫ u₀ = t ≫ u' := by
  first | exact @GlobalTheory.Desc.exists_spread_basicOpen_agree | exact GlobalTheory.Desc.exists_spread_basicOpen_agree | (intros; apply GlobalTheory.Desc.exists_spread_basicOpen_agree <;> assumption)
