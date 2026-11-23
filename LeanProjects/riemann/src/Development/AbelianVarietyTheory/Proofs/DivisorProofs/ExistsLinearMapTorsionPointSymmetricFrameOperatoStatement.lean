import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLinearMapTorsionPointSymmetricFrameOperato
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FamExt
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.Mum.Desc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_linearMap_torsionPoint_symmetricFrame_operator : ∀ (R : Type) [CommRing R] [IsDomain R] [CharZero R] (I : Ideal R), AdmBase R I → ∀ (D : DegData R I) (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] (N : ℕ), Odd N → ∀ (p : QkPt D.toPre F N) (w : GlobalTheory.UT.Frm D.toPre F N p.g.b), GlobalTheory.UT.TXFrame N p w → ∃ a : Fam D.toPre F N →ₗ[F] Fam D.toPre F N, ∀ s s', PhiRel D.toPre F N p w s s' ↔ s' = a s := by
  first | exact @GlobalTheory.Mum.PhiLinear.exists_linear_phi | exact GlobalTheory.Mum.PhiLinear.exists_linear_phi | (intros; apply GlobalTheory.Mum.PhiLinear.exists_linear_phi <;> assumption)
