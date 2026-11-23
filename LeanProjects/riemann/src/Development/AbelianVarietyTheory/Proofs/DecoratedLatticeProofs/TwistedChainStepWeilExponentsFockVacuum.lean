import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsLevMeas
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaChainStepWeilDatumNonzeroFockVacuum
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.TransferOn
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CartFrSgn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HarishChandraFinite
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.ChainTw
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (SplitProj IsProjAt IsIdemOf LiftsChar rdA grpCo frCo gAt)
open GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection (Blocks parahoric datum)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.Chain GlobalTheory.ChainFr GlobalTheory.PairLift GlobalTheory.Chain.RealIt

namespace GlobalTheory.ChainTw.StepExpTw

theorem twStepExpVac : ∀ D : D7, ForStepQ D fun c _ k s s' p => ∀ hk : k < D.R.m,
    IsWeilExp c.ψ s.V s'.V (GlobalTheory.Chain.expS D ⟨k, hk⟩) (GlobalTheory.Chain.expT D ⟨k, hk⟩) p.ω ∧
      GlobalTheory.Chain.IsVacVec c.ψ c.θ s.M s'.M p.f := by
  intro D _ c w hw k _ s s' hs hs' p hp hk
  obtain ⟨hr, _, hsf⟩ := hs
  obtain ⟨hr', _, hsf'⟩ := hs'
  refine ⟨⟨c.chS (k + 1), c.chT (k + 1), hp.weil, fun τ => StepExp.chrStep_exp' hw.com ⟨k, hk⟩ τ⟩, ?_⟩
  obtain ⟨f₀, hv⟩ := hp.vec
  have hrk : s.V.rank ≤ s'.V.rank := by
    have h1 : s.V.rank = D.R.rankY k := hsf.rank
    have h2 : s'.V.rank = D.R.rankY (k + 1) := hsf'.rank
    rw [h1, h2]
    exact Nat.add_le_add_left (Nat.mul_le_mul_right D.R.t (Nat.le_succ k)) D.R.r
  obtain ⟨a, b, d⟩ := StepVac.stepVec_vac hsf.selfDual hsf'.selfDual hrk hv
  exact { theta := a, ne := b, vac := d }

end GlobalTheory.ChainTw.StepExpTw
