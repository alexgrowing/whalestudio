import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DegEqSumLineHeights
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LnStepFalse
open AlgebraicGeometry CategoryTheory NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj
open GlobalTheory.TrueGeo GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.Toroidal GlobalTheory.LocM.Frm GlobalTheory.HeightParts
open GlobalTheory.GradedNorm GlobalTheory.LieHt
open Formalism.MainNotions.DIV.Cons (intO)
open GlobalTheory.LieSmooth

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.deg_eq_sum_line_heights : ∀ (K : Type) [Field K] [NumberField K] (V : Type) [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (h : HermFam K V) (E : Submodule (𝓞 K) V) (r : ℕ) (v : Fin r → V), E.FG → LinearIndependent K v → Submodule.span K (E : Set V) = Submodule.span K (Set.range v) → deg h E = ∑ i, lineHt h E v i := by
  first | exact @GlobalTheory.LatFlag.deg_eq_sum_lineHt | exact GlobalTheory.LatFlag.deg_eq_sum_lineHt | (intros; apply GlobalTheory.LatFlag.deg_eq_sum_lineHt <;> assumption)
