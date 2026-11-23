import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualFrameVacuumStep
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.FrameTopAlt
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.RatioOKOfRootOfUnity
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ChainParSucc
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.self_dual_frame_vacuum_step : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : RealPack ex) (u : D.what₂.Word), PkHyp W → ∀ (j : ℕ), j < D.R.m → ∀ (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (Λ : GlobalTheory.FinPl.Lat V) (β : GL (Fin V.rank) (Lev.EAf D)) (vac : WO (Yc D j) V → ℂ), IsSDFrame V β Λ 1 ∨ IsSDFrame V β Λ (D.host.g 0 * D.host.g 1) → IsVacO (pk W).ψ (pk W).θ (Yc D j) V (cart ((pk W).MY j)) (cart M) ((pk W).ΛY j) Λ vac → ∃ dG, IsDG W j M Λ β vac dG ∧ ∀ t, ∃ dQ, IsDQ W t j M Λ β vac dQ ∧ ∀ v, IsStepVecOf (pk W).ψ (pk W).θ (Yc D j) V (cart ((pk W).MY j)) (cart M) ((pk W).ΛY j) Λ ((pk W).βY j) β ((pk W).datYt t j (lvP W)) ((pk W).chi (j + 1)) ((pk W).Q t) ((pk W).xiR t) vac v ↔ v = comb (pk W).ψ _ _ dQ (comb (pk W).ψ _ _ dG vac) := by
  first | exact @GlobalTheory.FamSplit.split_datum | exact GlobalTheory.FamSplit.split_datum | (intros; apply GlobalTheory.FamSplit.split_datum <;> assumption)
