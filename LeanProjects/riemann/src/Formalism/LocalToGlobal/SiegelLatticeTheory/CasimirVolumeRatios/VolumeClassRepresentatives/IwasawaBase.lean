import Formalism.LocalToGlobal.SiegelLatticeTheory.CasimirVolumeRatios.VolumeClassRepresentatives.WittLeviObjects
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedVolumeStatements.LevelSubgroupProperties
import Formalism.SharpRestriction.CuspSpanNormBounds.UnimodularSchurMeasures.RightRegularIsometricMultiplicative

noncomputable section

namespace Formalism.L2.S.S7.IwasawaBase

open MeasureTheory NumberField
open scoped ENNReal
open Formalism.MainNotions.S Formalism.MainNotions.BridgeLemma Formalism.MainNotions.LeviCoordinates Formalism.L2.S.S7.DensDefs Formalism.L2.S.S7.WittLeviSubgroups

variable (I : AutInst)

theorem muA_right (μf : Measure I.Gf) [SigmaFinite μf] [μf.IsHaarMeasure] : (I.muA μf).IsMulRightInvariant := by
  have : μf.IsMulRightInvariant := Formalism.L2.SG.Closed.GfUnimod_holds I μf
  exact rr_muA_right I μf

def BaseExists : Prop :=
  ∀ (I : AutInst) {J : ℕ} (c : Composition J) (W : Fin c.length → Submodule I.E (Fin I.n → I.E)),
    IsIsoFlag I c W → 2 * J ≤ I.n → ∃ D : BaseDatum I J, ∀ i, D.toWittFrame.flag c i = W i

def IwaBase (kp : (X : CData) → (J : ℕ) → Composition J → ℝ) : Prop :=
  ∀ (X : CData) (n₀ : ℕ) (A : ℝ), X.HypB n₀ A → X.FinVol → 2 * X.qq + 2 ≤ X.I.n →
    ∀ (J : ℕ) (c : Composition J), 1 ≤ J → J ≤ X.qq → ∀ D : BaseDatum X.I J,
      ∀ FP : Set X.I.GA, IsFD (X.I.muA X.μf) (PPF X.I (D.toWittFrame.flag c) : Set X.I.GA) FP →
        ∀ Ψ : (Fin c.length → ℝ) → ℝ≥0∞, Measurable Ψ →
          ∫⁻ x in FP, (cn_Reg c.length).indicator Ψ (gradSize X.I (x * D.y) (D.toWittFrame.flag c))
              ∂(X.I.muA X.μf) ≤
            ENNReal.ofReal (X.I.vol X.μf X.fund * kp X J c) *
              ∫⁻ t in cn_Reg c.length, Ψ t * ENNReal.ofReal
                (cn_dens c.blocksFun (X.I.n - 2 * J) X.I.f t * cn_wt c.blocksFun X.I.f t)

end Formalism.L2.S.S7.IwasawaBase

end
