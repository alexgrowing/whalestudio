import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.CharpolySplitsOfEmbeddings
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsSubMemEigW
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.Ar.Flat.DegZ
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.charpoly_splits_of_embeddings : ∀ (E : Type) [Field E] [NumberField E] (Ω : Type) [Field Ω] [CharZero Ω] (O : Type) [CommRing O] [Algebra O Ω] (K : Type) [Field K] (g : O →+* K), Function.Injective (algebraMap O Ω) → Nat.card (E →+* Ω) = Module.finrank ℚ E → (∀ (s' : E →+* Ω) (a : 𝓞 E), s' (a : E) ∈ (algebraMap O Ω).range) → ∀ a : 𝓞 E, ((Algebra.lmul ℤ (𝓞 E) a : Module.End ℤ (𝓞 E)).charpoly.map (Int.castRingHom K)).Splits := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.DegZ.charpoly_lmul_splits_of_conjugates | exact GlobalTheory.CompanionTheory.Ar.Flat.DegZ.charpoly_lmul_splits_of_conjugates | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.DegZ.charpoly_lmul_splits_of_conjugates <;> assumption)
