import Formalism.SharpRestriction.CuspSpanNormBounds.AbsoluteAmplitudeSecondOfSource

set_option linter.unusedVariables false

noncomputable section

namespace Formalism.MainNotions.S.Pv.Mom

open NumberField Formalism.BasicNotions Formalism.MainNotions.S.Lat Module
open MeasureTheory Formalism.QuantumDeterminants Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.S.ThB Formalism.MainNotions.S.Bridge
open scoped ENNReal

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section

variable (D : D7) (large₂ : SizeData₂ D)

def MomNorm' (C' Cl Cg cb Cu cT CT C0 Cn : ℝ) : Prop :=
  Cnt.Hyp0 D large₂ C' Cl Cg cb Cu cT CT C0 →
  ∀ τ w w' θ (W : LocW D.R.k D.R.rS) (hW : GoodW D τ w w' θ W) (lam' : Fin (2 * D.R.rS + D.R.k + 1) → ℝ),
    l1dist lam' (lamD D τ) ≤ Cn * D.R.k * (D.R.m : ℝ) ^ 3 →
    ∀ (A : LocS W) (hA : GoodS D lam' A) (hT : 0 < Tr D w) (hT' : 0 < Tr D w'),
    ∃ (Bf : A.H → W.Wp) (P : Mx D.R.k D.R.rS) (w0 : A.H),
      IsBesselMapSm W.z (psi D.R.k D.R.rS W.z (cOfDpsi ((kaS D : ℝ) : ℂ))) A.σ W.π Bf ∧
      (∀ v ∈ smoothVecs (k := D.R.k) (r := D.R.rS) A.σ,
        l2SG W.νS (fun g => Bf (A.σ g v)) = (‖v‖₊ : ℝ≥0∞) ^ 2) ∧
      IsCayleyU D.R.k D.R.rS (epsSH D.R) P ∧
      w0 ∈ shell (toBesselK D τ w w' θ W lam' A hW hA hT hT') P 0 ∧ w0 ≠ 0 ∧
      ∀ F : (Fin (D.R.rS + 1) → ℝ) → ℝ≥0∞, Measurable F →
        ∫⁻ x, F (fun a => lA D.R.k D.R.rS W.z (Matrix.of x) a) * (‖A.Φ (Matrix.of x)‖₊ : ℝ≥0∞) ^ 2 ∂W.νS =
          l2SG W.νS A.Φ * Emom (toBesselK D τ w w' θ W lam' A hW hA hT hT') Bf W.νS w0
            (fun g => F (fun a => lA D.R.k D.R.rS W.z g a))

end

section Fam

variable {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) (Cg cb Cu cT CT C0 C1 : ℝ)

def MomF' : Prop :=
  ∀ Cn, Formalism.MainNotions.S.OwnEv Fm fun C' Cl x i => MomNorm' (Fm.D x i) (Fm.L x i) C' Cl Cg cb Cu cT CT C0 Cn

end Fam

section
variable (D : D7) (large₂ : SizeData₂ D)

def BesselSchur' (C' Cl Cg cb Cu cT CT C0 Cn : ℝ) : Prop :=
  Cnt.Hyp0 D large₂ C' Cl Cg cb Cu cT CT C0 →
  ∀ τ w w' θ (W : LocW D.R.k D.R.rS), GoodW D τ w w' θ W → ∀ (lam' : Fin (2 * D.R.rS + D.R.k + 1) → ℝ),
    l1dist lam' (lamD D τ) ≤ Cn * D.R.k * (D.R.m : ℝ) ^ 3 → ∀ (A : LocS W), GoodS D lam' A → 0 < Tr D w →
    ∀ v ∈ smoothVecs (k := D.R.k) (r := D.R.rS) A.σ,
      l2SG W.νS (fun g => A.B (A.σ g v)) * (‖A.v0‖₊ : ℝ≥0∞) ^ 2 = l2SG W.νS A.Φ * (‖v‖₊ : ℝ≥0∞) ^ 2

end

end Formalism.MainNotions.S.Pv.Mom
