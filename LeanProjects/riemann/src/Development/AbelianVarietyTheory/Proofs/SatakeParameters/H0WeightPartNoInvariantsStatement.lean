import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.H0WeightPartNoInvariants
import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.SumRepresentations
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.WeightRegularOfExt
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.H0_weight_part_no_invariants : ∀ (R : Ranks) (H : Host R) (what₂ : Rows.Data R) (N : NData R H what₂) (i : N.Loc) (ρ : G H.E N.Om →* GL (Fin R.r) (N.O i)) (Dg : Subgroup (G H.E N.Om)), GlobalTheory.IndefiniteRowSideFullHecke.NoLocalInvariantsRankParts.NoInv Dg (GlobalTheory.IndefiniteRowSideFullHecke.NoLocalInvariantsRankParts.matW N i ρ) → H0 ((Formalism.MainNotions.N.Glob.WpK N i ρ).comp Dg.subtype) = ⊥ := by
  first | exact @GlobalTheory.Ggeo.WpKInv.H0_weight_part_eq_bot | exact GlobalTheory.Ggeo.WpKInv.H0_weight_part_eq_bot | (intros; apply GlobalTheory.Ggeo.WpKInv.H0_weight_part_eq_bot <;> assumption)
