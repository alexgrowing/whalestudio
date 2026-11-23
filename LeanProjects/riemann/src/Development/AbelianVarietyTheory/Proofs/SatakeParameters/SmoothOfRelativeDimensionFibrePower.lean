import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsGDatumOneOneOne
import Development.AbelianVarietyTheory.Definitions.Divisors.HxiTZeroComb
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.SmoothOfRelativeDimensionPowObj
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen

namespace GlobalTheory.FibPow

theorem smoothOfRelativeDimension_pow {X : Scheme.{0}} (A : Over X) (g : ℕ)
    (hA : SmoothOfRelativeDimension g A.hom) (k : ℕ) : SmoothOfRelativeDimension (k * g) (GlobalTheory.KS.pow A k).hom := by
  let e : GlobalTheory.KS.pow A k ≅ ReciprocityTheory.ChartRestriction.G.Out.powObj A k :=
    (limit.isLimit (Discrete.functor fun _ : Fin k => A)).conePointUniqueUpToIso
      (ReciprocityTheory.ChartRestriction.G.Out.powIsLimit A k)
  have hw : (GlobalTheory.KS.pow A k).hom = e.hom.left ≫ (ReciprocityTheory.ChartRestriction.G.Out.powObj A k).hom := (Over.w e.hom).symm
  have h1 := GlobalTheory.smoothOfRelativeDimension_powObj A g hA k
  have : IsIso e.hom.left := inferInstanceAs (IsIso ((Over.forget _).map e.hom))
  have h2 : SmoothOfRelativeDimension (0 + k * g) (e.hom.left ≫ (ReciprocityTheory.ChartRestriction.G.Out.powObj A k).hom) :=
    inferInstance
  rw [hw]; simpa using h2

theorem smoothOfRelativeDimension_fibrePower : ∀ (R : Type) [CommRing R] (X : Scheme.{0}) (s : X ⟶ Sp R) (d g : ℕ),
    SmoothOfRelativeDimension d s → ∀ (A : Over X) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A →
    SmoothOfRelativeDimension g A.hom → ∀ k : ℕ, SmoothOfRelativeDimension (d + k * g) ((GlobalTheory.KS.pow A k).hom ≫ s) := by
  intro R _ X s d g hs A _ _ _ hA k
  have h := smoothOfRelativeDimension_pow A g hA k
  have h2 : SmoothOfRelativeDimension (k * g + d) ((GlobalTheory.KS.pow A k).hom ≫ s) := inferInstance
  rw [Nat.add_comm]; exact h2

end GlobalTheory.FibPow
