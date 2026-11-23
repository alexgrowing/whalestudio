import Mathlib
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsFgIsSeparated
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.MorphismsSpreadOutToFgSubalgebra
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
theorem _root_.GlobalTheory.T.exists_fg_subalgebra_isSeparated_pullback_snd : ∀ (k V : Type) [CommRing k] [IsNoetherianRing k] [CommRing V] [Algebra k V] (X : Scheme.{0}) (p : X ⟶ Sp k), LocallyOfFiniteType p → QuasiCompact p → IsSeparated (pullback.snd p (spMap (algebraMap k V))) → ∃ R : Subalgebra k V, R.FG ∧ IsSeparated (pullback.snd p (spMap (algebraMap k R))) := by
  first | exact @GlobalTheory.SpreadSep.exists_fg_isSeparated | exact GlobalTheory.SpreadSep.exists_fg_isSeparated | (intros; apply GlobalTheory.SpreadSep.exists_fg_isSeparated <;> assumption)
