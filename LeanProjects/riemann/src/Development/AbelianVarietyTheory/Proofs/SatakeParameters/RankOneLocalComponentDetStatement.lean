import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.RankOneLocalComponentDet
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsSpanFormsNeBot
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rank_one_local_component_det : GlobalTheory.Published.AutomorphicFormsFiniteGL → ∀ (hL : GlobalTheory.Published.LocalLanglandsGL) (D : D7) (P : Pin hL D), ∀ (π : D.naut.CG 1) (w : PlE D.host) (ξ : (w.adicCompletion D.host.E)ˣ →* ℂˣ) (h : IsComp (P.chr.e1 π).1 w ξ), P.T.e w (D.naut.locG π w) = rcAt hL D w 1 (Irr.ofDet 1 ξ h.1) := by
  first | exact @GlobalTheory.RankOneComp.locG_rankOne_eq_rcAt | exact GlobalTheory.RankOneComp.locG_rankOne_eq_rcAt | (intros; apply GlobalTheory.RankOneComp.locG_rankOne_eq_rcAt <;> assumption)
