import Mathlib
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsLieRepresentationEigenLattices
import Development.AbelianVarietyTheory.Definitions.CMLattices.ExistsIsThetaDegOfIsLocalModel
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_lieRepresentation_eigenLattices : ∀ (K : Type) [Field K] [NumberField K] (P : Out.PolAV (Sp (𝓞 K))) (F : GenFib P) (O : Type) [CommRing O] (act : OAct O P.A), ∃ r : O →+* Module.End K (Fin F.P₀.g → K), (∀ a, F.IsDiffOf F (act.act a) (r a)) ∧ ∀ (τ : O →+* 𝓞 K) c, (c ∈ F.eigLat act τ ↔ c ∈ F.lieLat ∧ ∀ a, r a c = τ a • c) ∧ (c ∈ Submodule.span K (F.eigLat act τ : Set (Fin F.P₀.g → K)) ↔ ∀ a, r a c = τ a • c) := by
  first | exact @GlobalTheory.CM.GenFib.exists_lieRep_eigLat | exact GlobalTheory.CM.GenFib.exists_lieRep_eigLat | (intros; apply GlobalTheory.CM.GenFib.exists_lieRep_eigLat <;> assumption)
