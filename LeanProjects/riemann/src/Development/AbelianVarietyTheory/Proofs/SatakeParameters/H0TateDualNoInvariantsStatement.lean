import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.H0TateDualNoInvariants
import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.SumRepresentations
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.WeightRegularOfExt
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.H0_coefRep_T2_subtype_eq_bot_of_noInv_matT : ∀ (R : Ranks) (H : Host R) (what₂ : Rows.Data R) (N : NData R H what₂) (i : N.Loc) (ρ : G H.E N.Om →* GL (Fin R.r) (N.O i)) (Dg : Subgroup (G H.E N.Om)), GlobalTheory.IndefiniteRowSideFullHecke.NoLocalInvariantsRankParts.NoInv Dg (GlobalTheory.IndefiniteRowSideFullHecke.NoLocalInvariantsRankParts.matT N i ρ) → H0 ((Formalism.MainNotions.N.coefRep (Formalism.MainNotions.N.Glob.T2 N i ρ) (Kf N i)).comp Dg.subtype) = ⊥ := by
  first | exact @GlobalTheory.TateDualCoef.H0_coefRep_T2_comp_subtype_eq_bot_of_noInv | exact GlobalTheory.TateDualCoef.H0_coefRep_T2_comp_subtype_eq_bot_of_noInv | (intros; apply GlobalTheory.TateDualCoef.H0_coefRep_T2_comp_subtype_eq_bot_of_noInv <;> assumption)
