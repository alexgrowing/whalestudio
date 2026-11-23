import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ReductionMemUnipSymOfFlagCongruences
import Formalism.LocalToGlobal.IndefiniteReal.ZeroPartEigenvalueConvention
import Formalism.LocalToGlobal.IndefiniteReal.EvalTieTOne
import Formalism.LocalToGlobal.IndefiniteReal.RationalEmbedding
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowLevelMatch
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.DiscreteSeriesClassificationIff
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DiagGLConjApply
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LevelPlacesNotIsConjPlaceRealDat
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.BunExists
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.LevelSubgroupCharacterUnitary
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BSlotD
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SeeConjRead
open GlobalTheory.SeeConjGroup Formalism.L2.SG.HidaSetting
open scoped Matrix

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.reduction_mem_unipSym_of_flag_congruences : ∀ {D : D7} (g : ℕ) (e0 f0 : Fin D.R.rS → VA (II D)) (z0 : VA (II D)) (bb cc : Fin D.R.k → VA (II D)) (β : GL (Fin (Yc D 0).rank) (EAf D)) (PP : Pl D.host.E), IsFrame β (II D).L → ((g : 𝓞 D.host.E) ∈ PP.asIdeal) → RedIs β PP (flagV D.R.rS D.R.k (Yc D 0).rank e0 f0 bb z0) → (∀ i, cc i ∈ (II D).Lf ∧ redV β PP (cc i) = 0) → ∀ M : GL (Fin (Yc D 0).rank) (EAf D), M ∈ St β → (∀ a, (M.val - 1) *ᵥ e0 a ∈ Formalism.L2.SG.Pf.unitaryCongruence.Mo (II D) g (e0 '' {b | b.1 < a.1})) → ((M.val - 1) *ᵥ z0 ∈ Formalism.L2.SG.Pf.unitaryCongruence.Mo (II D) g (Set.range e0)) → (∀ i, (M.val - 1) *ᵥ bb i ∈ Formalism.L2.SG.Pf.unitaryCongruence.Mo (II D) g (Set.range e0 ∪ Set.range cc ∪ bb '' {j | j.1 < i.1})) → (∀ b, (M.val - 1) *ᵥ f0 b ∈ Formalism.L2.SG.Pf.unitaryCongruence.Mo (II D) g (Set.range e0 ∪ {z0} ∪ Set.range bb ∪ Set.range cc ∪ f0 '' {c | b < c})) → upperLeftBlock (r_le_Y (D := D) 0) (redFn β PP M) ∈ unipSym (kP PP) D.R.r D.R.rS D.R.k := by
  first | exact @GlobalTheory.SeeConjGroup.redFn_mem_unipSym_of_cong | exact GlobalTheory.SeeConjGroup.redFn_mem_unipSym_of_cong | (intros; apply GlobalTheory.SeeConjGroup.redFn_mem_unipSym_of_cong <;> assumption)
