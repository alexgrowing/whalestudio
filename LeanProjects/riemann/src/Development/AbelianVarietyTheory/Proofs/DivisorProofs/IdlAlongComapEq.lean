import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.NonUnitAt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StalkIdComapOfAffine
open AlgebraicGeometry CategoryTheory Limits IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.ZH GlobalTheory.Poinc
open GlobalTheory.SiegelTor

noncomputable section

namespace GlobalTheory.PullAlong

theorem idlAlong_comap_eq : ∀ {X Y : Scheme.{0}} (π : Y ⟶ X) (J : X.IdealSheafData) {R : Type} [CommRing R]
    [IsLocalRing R] (ξ : Sp R ⟶ Y), idlAlong (J.comap π) ξ = idlAlong J (ξ ≫ π) := by
  intro X Y π J R _ _ ξ
  unfold idlAlong
  rw [GlobalTheory.VanStalk.stalkId_comap, Ideal.map_map, Scheme.stalkClosedPointTo_comp]
  rfl

end GlobalTheory.PullAlong
