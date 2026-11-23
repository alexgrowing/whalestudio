import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.LinksW
import Formalism.LocalToGlobal.IndefiniteReal.LinksLemmas
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsMultiplicityLiftLastChainStepStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsLastStepIntertwinerChainStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Twist.LastStepLift

theorem exists_lastStep_lift : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type)
    (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks]
    [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), R.toLevCh.Is A.μ0 → R.IsFam → R.IsModels →
    R.IsChainW → R.ex_ioX := by
  intro D G _ _ Pl0 T A Ks _ _ _ R hlev hfam hmod hc
  have hIt : R.chain_ItX := hc.ItX.1 (GlobalTheory.T.exists_lastStep_intertwiner_chain D G Pl0 T A Ks R hlev hfam hmod hc)
  obtain ⟨io, hio⟩ := GlobalTheory.T.exists_multiplicityLift_lastChainStep D G Pl0 T A Ks R hlev hfam hmod hc.ωX hc.vX hc.ptX hIt
  exact fun t => ⟨io t, hio t⟩

end GlobalTheory.Twist.LastStepLift
