import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFirstOrderTangentPointSmooth
import Development.AbelianVarietyTheory.Definitions.Divisors.SRelOneOneIff
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.SiegelToroidalIntegral
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_firstOrder_tangentPoint_smooth : ∀ {o : Type} [CommRing o] (X : Scheme.{0}) (s : X ⟶ Sp o) (D : ℕ), SmoothOfRelativeDimension D s → ∀ (K : Type) [Field K] (β : o →+* K) (x₀ : Sp K ⟶ X), x₀ ≫ s = spMap β → ∃ y : Sp (TrivSqZeroExt K (Fin D → K)) ⟶ X, spMap (TrivSqZeroExt.fstHom K K (Fin D → K)).toRingHom ≫ y = x₀ ∧ y ≫ s = spMap ((algebraMap K (TrivSqZeroExt K (Fin D → K))).comp β) ∧ ∀ mu : (Fin D → K) →ₗ[K] K, spMap (dirMap mu) ≫ y = constPt (spMap (dirMap mu) ≫ y) → mu = 0 := by
  first | exact @GlobalTheory.TanPt.exists_tangent_point | exact GlobalTheory.TanPt.exists_tangent_point | (intros; apply GlobalTheory.TanPt.exists_tangent_point <;> assumption)
