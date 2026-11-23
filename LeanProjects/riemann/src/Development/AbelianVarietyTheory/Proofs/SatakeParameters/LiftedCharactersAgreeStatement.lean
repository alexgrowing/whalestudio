import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LiftedCharactersAgree
import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsUniqueVec
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HarishChandraFinite
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CharacteristicFunctionIntegralApply
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lifted_characters_agree : ∀ (hL : GlobalTheory.Published.LocalLanglandsGL) (D : D7) (P : Pin hL D) (X : GlobalTheory.NJoin.RealAt D P.cf P.C P.tp) (A : GlobalTheory.NJoin.Agree X P.M P.rep) (i : D.nd.Loc) (j : Fin D.R.m) (hj : j.1 + 1 = D.nd.j i), Formalism.IndefR.Links.ChrEq (Formalism.IndefR.Lift.chrTh (X.R.toLevCh.mu (X.tupT (D.nd.mu i))) X.R.eta (j.1 + 1)).1 (P.tp.tup (D.nd.mu i) j) ∧ Formalism.IndefR.Links.ChrEq (Formalism.IndefR.Lift.chrTh (X.R.toLevCh.mu (X.tupT (D.nd.mu i))) X.R.eta (j.1 + 1)).2 (P.tp.tup (D.nd.mu i) j * P.cf.eta⁻¹) := by
  first | exact @GlobalTheory.WeilDatumChars.weil_chars | exact GlobalTheory.WeilDatumChars.weil_chars | (intros; apply GlobalTheory.WeilDatumChars.weil_chars <;> assumption)
