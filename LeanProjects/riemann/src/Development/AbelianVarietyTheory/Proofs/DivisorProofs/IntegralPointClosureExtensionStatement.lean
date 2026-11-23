import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralPointClosureExtension
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitKOfIsAlgClosed
open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj
open GlobalTheory GlobalTheory.ArInt GlobalTheory.ShFam.Pad GlobalTheory.TrueGeo GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.Mean4O GlobalTheory.LineNorm GlobalTheory.CoverNorm GlobalTheory.VertForm GlobalTheory.HtGen
open Formalism.MainNotions.DIV.Cons (intO)
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_point_closure_extension : ∀ (F : Type) [Field F] [NumberField F] (Y : Var F) (V : Cover Y) (l : ℕ) (W : V.X.Opens) (x : V.X), x ∈ W → (l : 𝓞 F) ∈ (V.p x).asIdeal → ∃ (v : HeightOneSpectrum (𝓞 F)) (e : TrueGeo.Ext v) (z : Sp (AlgebraicClosure F) ⟶ V.G) (yt : Sp e.O ⟶ V.X), (l : 𝓞 F) ∈ v.asIdeal ∧ z ≫ V.π ≫ Y.str = spMap (algebraMap F (AlgebraicClosure F)) ∧ spMap e.O.subtype ≫ yt = z ≫ V.j ∧ ⊤ ≤ yt ⁻¹ᵁ W ∧ x ⤳ yt (IsLocalRing.closedPoint e.O) ∧ ∀ g : V.X.functionField, RegAt (yt (IsLocalRing.closedPoint e.O)) g → (e.w (TrueGeo.valAt (z ≫ V.j) g) = 1 ↔ UnitAt (yt (IsLocalRing.closedPoint e.O)) g) := by
  first | exact @GlobalTheory.HtGen.IntPt.exists_intPt | exact GlobalTheory.HtGen.IntPt.exists_intPt | (intros; apply GlobalTheory.HtGen.IntPt.exists_intPt <;> assumption)
