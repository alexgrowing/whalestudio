import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsRationalTateIsomorphism
import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CmIdempotentAddStarEqOne
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.TorRef
open ReciprocityTheory.ChartRestriction.G.DVR
open MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_rational_tate_isomorphism : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (T : CDVR) (t : SAB H (Sp T.V)) (P : PELUnif (maximalIdeal T.V) t), P.TorsionIso → ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing T.V) F], letI := H.starRing; ∀ J : TateIso D F (Out.TFK (R := T.V) F ⟶ P.A.A) (fun a g => g ≫ P.oA.act a) (fun n g g' c => Out.WeilIs P.A.A P.A.L n g g' (unitOn c)), ∃ I : TateIsoQ D P.D.toPre P.oD F, I.ζ = J.ζ ∧ ∀ k, 0 < k → ∀ a q, P.ToA F k q (J.ev k a) → Out.QkPt.Equiv P.D.toPre F q (I.ev k a) := by
  first | exact @GlobalTheory.ArcBuild.exists_tateIsoQ_of_torsionIso | exact GlobalTheory.ArcBuild.exists_tateIsoQ_of_torsionIso | (intros; apply GlobalTheory.ArcBuild.exists_tateIsoQ_of_torsionIso <;> assumption)
