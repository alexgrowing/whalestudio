import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitBlockCosetIffMaximalLevelCongruentConjIdeal
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GoodIdemEmpty
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardLatticeDoubleCosetClassesStabilisers
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsThetaFunctionStandardPairSecond
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open Formalism.DivisionValues (vw)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.NormSum (Pair Tup)
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.BotSmallDict GlobalTheory.NormExact
open scoped Pointwise

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitBlockCoset_iff_maximalLevel_congruent_conjIdeal : ∀ {D : D7} (S T : HSp D), S.gram = 1 →
    ∀ (e : Formalism.L2.Theta.AE D) (P : Finset (Formalism.L2.DIV.Pl D.host.E)) (c : Formalism.L2.DIV.Pl D.host.E → ℕ), IsIdemSum e P →
    ∀ o : ℕ, o + S.rank = T.rank → ∀ k ∈ GlobalTheory.NormSum.intG D S.rank, ∀ k' ∈ GlobalTheory.NormSum.intG D S.rank, ∀ g g' : Formalism.L2.Theta.GA D S,
    GlobalTheory.BotFormula.IsFinPt S g k → GlobalTheory.BotFormula.IsFinPt S g' k' → ∀ y : WO S T,
    cosetFn (cA D e) (D.host.conj • modul P c) (unitPt S T (cA D e) o) (actO S T g⁻¹ 1 y) ≠ 0 →
    (cosetFn (cA D e) (D.host.conj • modul P c) (unitPt S T (cA D e) o) (actO S T g'⁻¹ 1 y) ≠ 0 ↔
      CongOne D (D.host.conj • modul P c) (k'⁻¹ * k)) := by
  first | exact @GlobalTheory.BotSmallDict.CosetCong.coset_iff_congOne | exact GlobalTheory.BotSmallDict.CosetCong.coset_iff_congOne | (intros; apply GlobalTheory.BotSmallDict.CosetCong.coset_iff_congOne <;> assumption)
