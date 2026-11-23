import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualAbelianSchemeExistsBiduality
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AV

theorem exists_dualPair : ∀ (K : Type) [Field K] (A : AbVar K),
    ∃ (B : AbVar K) (P : LB (A.X ⊗ B.X).left), IsDualPair A B P ∧ B.dim = A.dim := by
  intro K _ A
  obtain ⟨B, hg, P, hB, hdim, h1, h2⟩ := GlobalTheory.dualAbelianScheme (Sp K) A.X A.ab
  exact ⟨{ X := B, grp := hg, ab := hB, dim := A.dim, smooth := hdim A.dim A.smooth }, P, ⟨h1, h2⟩, rfl⟩

end GlobalTheory.AV
