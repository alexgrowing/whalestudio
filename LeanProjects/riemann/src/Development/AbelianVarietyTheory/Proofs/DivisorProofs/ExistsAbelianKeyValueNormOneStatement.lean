import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAbelianKeyValueNormOne
import Development.AbelianVarietyTheory.Definitions.Divisors.TanRel
import Development.AbelianVarietyTheory.Definitions.Divisors.IsPolAVSectionInverseImage
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbsoluteSiegel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffTopMonEqZero
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.MBModel GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_abelianKeyValue_norm_one : ∀ κ : Rule, Rule4 κ → ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [CharZero V] (D : DegPre V) (C : Type) [NontriviallyNormedField C] [IsUltrametricDist C] [CharZero C] [Algebra (FractionRing V) C], CExt V (IsLocalRing.maximalIdeal V) C → ∀ (N : NumD C) (ν : NumOf D C N), ν.IntN → ∀ vB : Fin D.P.g → (epsR V ⟶ D.P.A), IsLieBasis vB → ∃ k : C, BKey κ ν vB k ∧ ‖k‖ = 1 := by
  first | exact @GlobalTheory.MBLow.AbKey.exists_bKey | exact GlobalTheory.MBLow.AbKey.exists_bKey | (intros; apply GlobalTheory.MBLow.AbKey.exists_bKey <;> assumption)
