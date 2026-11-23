import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GradedIdealFgNeBot
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LnStepFalse
open AlgebraicGeometry CategoryTheory NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj
open GlobalTheory.TrueGeo GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.Toroidal GlobalTheory.LocM.Frm GlobalTheory.HeightParts
open GlobalTheory.GradedNorm GlobalTheory.LieHt
open Formalism.MainNotions.DIV.Cons (intO)
open GlobalTheory.LieSmooth

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.graded_ideal_fg_ne_bot : ∀ (K : Type) [Field K] [NumberField K] (V : Type) [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (E : Submodule (𝓞 K) V) (r : ℕ) (v : Fin r → V) (i : Fin r), E.FG → LinearIndependent K v → Submodule.span K (Set.range v) ≤ Submodule.span K (E : Set V) → (grIdeal E v i).FG ∧ grIdeal E v i ≠ ⊥ := by
  first | exact @GlobalTheory.LieSmooth.grIdeal_fg_ne_bot | exact GlobalTheory.LieSmooth.grIdeal_fg_ne_bot | (intros; apply GlobalTheory.LieSmooth.grIdeal_fg_ne_bot <;> assumption)
