import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SectionValueEqAdicSumAtImageOfZeroPair
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoefTwistPull
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory.ZH
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_generic_frame_liesOver_of_y_eq_zero : ∀ (R : Type) [CommRing R] [IsDomain R] [CharZero R] (I : Ideal R), AdmBase R I → ∀ (D : DegData R I) (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (U : Unif I D A G) (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] (w₀ : W0 U.toUnifPre), w₀.IsGen → ∀ (k : ℕ), 1 ≤ k → ∀ (p : QkPt D.toPre F k) (x : TFK (R := R) F ⟶ A.A), p.y = 0 → QkToAkU U.toUnifPre F k p x → ∃ (w : Frm D.toPre F 1 p.g.b) (fr : FrAt x), w.IsGen ∧ fr.IsGen ∧ GlobalTheory.Poinc.Tors.LiesOver U.toUnifPre w₀ p.g w x fr := by
  first | exact @GlobalTheory.Poinc.Tors.ValPair.liesOver_of_qkToAkU | exact GlobalTheory.Poinc.Tors.ValPair.liesOver_of_qkToAkU | (intros; apply GlobalTheory.Poinc.Tors.ValPair.liesOver_of_qkToAkU <;> assumption)
