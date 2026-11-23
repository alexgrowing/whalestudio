import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsFrameReorderingLevelData
import Formalism.LocalToGlobal.IndefiniteReal.ZeroPartEigenvalueConvention
import Formalism.LocalToGlobal.IndefiniteReal.EvalTieTOne
import Formalism.LocalToGlobal.IndefiniteReal.RationalEmbedding
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowLevelMatch
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.DiscreteSeriesClassificationIff
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_frame_reordering_levelData : ∀ {D : D7} {T : Type} (Lc : LevCh D T) (P P' : LevelP Lc.Pg D.R.r ℂ) (π : Equiv.Perm (Fin D.R.r)), (∀ g, g ∈ P.H ↔ reord π g ∈ P'.H) → (∀ g hg hg', P.chi ⟨g, hg⟩ = P'.chi ⟨reord π g, hg'⟩) → ∀ β₃ : GL (Fin (Yc D 0).rank) (EAf D), IsFrame β₃ (Formalism.L2.Herm.crdLat (Yc D 0) (Yc D 0).L0) → ∃ β₂ : GL (Fin (Yc D 0).rank) (EAf D), IsFrame β₂ (Formalism.L2.Herm.crdLat (Yc D 0) (Yc D 0).L0) ∧ ∀ κ : GA D (Yc D 0), (κ ∈ levS (Yc D 0) β₂ (Lc.dat0 P) ↔ κ ∈ levS (Yc D 0) β₃ (Lc.dat0 P')) ∧ levChi (Yc D 0) β₂ (Lc.dat0 P) κ = levChi (Yc D 0) β₃ (Lc.dat0 P') κ := by
  first | exact @GlobalTheory.SeeConjReord.exists_frame_reord | exact GlobalTheory.SeeConjReord.exists_frame_reord | (intros; apply GlobalTheory.SeeConjReord.exists_frame_reord <;> assumption)
