import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PartialSumInsertKilledCoordinateComp
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSumPolAV
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Mum
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MumFam GlobalTheory.MumProd
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.partialSum_insert_killed_coordinate_comp : ∀ (S : Scheme.{0}) (B B₂ T : Over S) [GrpObj B] [IsCommMonObj B] [GrpObj B₂] [IsCommMonObj B₂] (p : B ⟶ B₂) (x : Fin 2 → (T ⟶ B)), IsMonHom p → x 0 ≫ p = toUnit T ≫ η[B₂] → ∀ I : Finset (Fin 2), psum B x I ≫ p = psum B x (insert 0 I) ≫ p := by
  first | exact @GlobalTheory.MumProd.PsumCancel.psum_insert_zero_comp | exact GlobalTheory.MumProd.PsumCancel.psum_insert_zero_comp | (intros; apply GlobalTheory.MumProd.PsumCancel.psum_insert_zero_comp <;> assumption)
