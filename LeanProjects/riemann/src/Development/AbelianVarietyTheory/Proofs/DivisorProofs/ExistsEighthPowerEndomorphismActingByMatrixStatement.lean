import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEighthPowerEndomorphismActingByMatrix
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsE8WeightedBundle
import Development.AbelianVarietyTheory.Definitions.Divisors.IsChartMember
import ReciprocityTheory.AnalyticForms.RegularLocalRings.FinalTheorems
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.GoodClass
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.ExistsArBaseAway
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_eighth_power_endomorphism_acting_by_matrix : ∀ (S : Scheme.{0}) (A B : Over S) [GrpObj A] [GrpObj B] [IsCommMonObj B] (pr : Fin 8 → (A ⟶ B)),
  E8Fibration.IsProd pr → ∀ m : Matrix (Fin 8) (Fin 8) ℤ, ∃ f : A ⟶ A, IsMonHom f ∧ E8Fibration.ActsBy pr f m := by
  first | exact @GlobalTheory.Poinc.Sep.E8Fibration.exists_monHom_actsBy | exact GlobalTheory.Poinc.Sep.E8Fibration.exists_monHom_actsBy | (intros; apply GlobalTheory.Poinc.Sep.E8Fibration.exists_monHom_actsBy <;> assumption)
