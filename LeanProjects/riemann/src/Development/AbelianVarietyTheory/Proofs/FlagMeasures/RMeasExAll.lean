import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.LoopBCovN
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsRootHaar
open scoped Classical ENNReal
open Matrix MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.PackageTie2 Formalism.L2.SG.TermTieOf Formalism.L2.SG.LocWSOf Formalism.L2.SG.LoopTerm
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RMeasAll

theorem rMeasEx_all : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (hF : FinX Y) (hI : SIso D.s (sOf hF)) (C : Choice X 1) (u u' : D.what₂.Word), (∀ τ, GoodW D τ u u' 1 (locW C u u' τ)) → RMeasEx hI C u u' := by
  intro D X Y hF hI C u u' hW t hG hr τ
  obtain ⟨_, _, h3, h4, h5, h6, h7, _⟩ := hW τ
  have hTu : 0 < Formalism.MainNotions.S.Tr D u := Nat.cast_pos.2 (D.mem u).A.T_prime.pos
  have hTu' : 0 < Formalism.MainNotions.S.Tr D u' := Nat.cast_pos.2 (D.mem u').A.T_prime.pos
  obtain ⟨p, hp⟩ := Formalism.L2.SG.LoopTerm.relPtEx_holds hI C u u' t hG hr τ
  exact GlobalTheory.Amp.RootQuot.exists_rMeas D (locW C u u' τ) _ p h3 h4 (by rw [h5]; exact hTu) (by rw [h6]; exact hTu') h7 hp

end GlobalTheory.RMeasAll
