import Formalism.SharpRestriction.CuspSpanNormBounds.BridgeLitG
import Formalism.LocalToGlobal.SiegelLatticeTheory.CasimirReductionTheory.GgExistsAddCharNeOne

noncomputable section

open MeasureTheory Matrix Filter Topology Finset
open scoped InnerProductSpace ContDiff Convolution ComplexOrder

namespace Formalism.MainNotions.GapDS

open Formalism.MainNotions.S Formalism.MainNotions.PlaceDegreeData Formalism.MainNotions.S.UnitaryLevelOperators Formalism.QuantumDeterminants

def InfCharDSG : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), Formalism.QuantumDeterminants.IsHCParam lam → Formalism.MainNotions.S.IsDS ε lam σ →
    ∀ h : ℝ, Formalism.QuantumDeterminants.GapAtLeast ε lam h → thrX ε < h →
    ∀ v ∈ PI.PhMeasCore.smoothVecs (Formalism.REAL.Jm ε) σ, ∀ Y : ℂ,
      Formalism.L2.SG.LitS.actU ε σ (Formalism.REAL.qdet (Formalism.L2.SG.LitS.Egl n) (Y + ((n : ℂ) - 1) / 2)) v =
        Formalism.QuantumDeterminants.capP (fun s => (lam s : ℂ)) Y • v

end Formalism.MainNotions.GapDS
