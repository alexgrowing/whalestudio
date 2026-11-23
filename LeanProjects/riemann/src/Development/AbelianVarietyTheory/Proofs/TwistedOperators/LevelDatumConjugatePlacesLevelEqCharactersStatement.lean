import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LevelDatumConjugatePlacesLevelEqCharacters
import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LamHomApply
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.levelDatum_conjugatePlacesLevel_eq_characters : ∀ (D : D7) (S T : HSp D) (C : Ctx S T) (hn : T.rank ≤ S.rank) (Pg Q : Finset (Formalism.L2.DIV.Pl D.host.E)) (ξ : ∀ PP : Formalism.L2.DIV.Pl D.host.E, (Formalism.L2.DIV.kP PP)ˣ →* ℂˣ) (h1 : GlobalTheory.LiftLevel.liftI Pg Q ≠ ⊤) (h2 : GlobalTheory.LiftLevel.liftI Pg Q ≠ ⊥) (h3 : IsCoprime (GlobalTheory.LiftLevel.liftI Pg Q) (conjI (GlobalTheory.LiftLevel.liftI Pg Q))) (h4 : IsCoprime (GlobalTheory.LiftLevel.liftI Pg Q) (Ideal.span {2})) (β : Fin T.rank → Fin T.rank → D.host.E) (hβ : ∀ i, β i ∈ C.X.Λ) (hsp : C.X.Λ ≤ Submodule.span (𝓞 D.host.E) (Set.range β) ⊔ GlobalTheory.LiftLevel.liftI Pg Q • C.X.Λ) (Lv0 : GlobalTheory.SW.Level C.X), (∀ d : Fin T.rank → 𝓞 D.host.E, GlobalTheory.SW.Cong C.X (GlobalTheory.LiftLevel.liftI Pg Q) (∑ j, d j • β j) 0 → ∀ j, d j ∈ GlobalTheory.LiftLevel.liftI Pg Q) → ∀ (y : Matrix (Fin S.rank) (Fin T.rank) D.host.E) (c : Fin S.rank → Fin T.rank → 𝓞 D.host.E), (∀ i, y i - ∑ j, c i j • β j ∈ GlobalTheory.LiftLevel.liftI Pg Q • C.X.Λ) → ∀ Y : ∀ PP : Formalism.L2.DIV.Pl D.host.E, Matrix (Fin S.rank) (Fin T.rank) (Formalism.L2.DIV.kP PP), (∀ PP ∈ Pg ∪ Q, ∀ i j, Y PP i j = Ideal.Quotient.mk PP.asIdeal (GlobalTheory.SW.Lev.bar (c i j))) → (GlobalTheory.LiftDat.mkLevel C Pg Q ξ h1 h2 h3 h4 β hβ hsp Lv0).dat hn y = omegaK Pg Y * omegaQ Q T.rank ξ (-1) Y := by
  first | exact @GlobalTheory.LiftDat.dat_mkLevel_eq | exact GlobalTheory.LiftDat.dat_mkLevel_eq | (intros; apply GlobalTheory.LiftDat.dat_mkLevel_eq <;> assumption)
