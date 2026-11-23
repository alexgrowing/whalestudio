import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigenframeFlagPointLift
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LnStepFalse
open AlgebraicGeometry CategoryTheory NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj
open GlobalTheory.TrueGeo GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.Toroidal GlobalTheory.LocM.Frm GlobalTheory.HeightParts
open GlobalTheory.GradedNorm GlobalTheory.LieHt
open Formalism.MainNotions.DIV.Cons (intO)
open GlobalTheory.LieSmooth

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eigenframe_flag_point_lift : ∀ {D : D7} {A : Amb D} {N j : ℕ} {S : Sig A N j} {κ : Lv A} {s : FinalTheorems S κ} (Φ : s.Flag) (y : Pt s) {K : Type} [Field K] [NumberField K] (io : K →+* Qb) (fK : κ.c.F →+* K) (yK : Sp K ⟶ gen s.T.Z), spMap io ≫ yK = y.y → yK ≫ genStr s.T.Z = spMap fK → ∀ g : EigFrame s.T.Z fK (yK ≫ genι s.T.Z), g.IsMap io y.frame → ∃ p : Sp K ⟶ (Φ.C (compPt s y)).Y.X, p ≫ (Φ.C (compPt s y)).π = yK ∧ (Φ.C (compPt s y)).Carries p g ∧ below p = basePt Φ y := by
  first | exact @GlobalTheory.LieSmooth.basePt_definedOver | exact GlobalTheory.LieSmooth.basePt_definedOver | (intros; apply GlobalTheory.LieSmooth.basePt_definedOver <;> assumption)
