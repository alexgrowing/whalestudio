import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.AmpWinJF

noncomputable section

open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.PackageTie2
  Formalism.L2.SG.TermTieOf Formalism.L2.SG.LocWSOf Formalism.L2.SG.RealObj

namespace Formalism.L2.SG.Pf.LocalDoubleCoset

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def Move {k r : ℕ} (z z' : Fin (2 * r + k + 1) → ℂ) (γ γ' : Formalism.MainNotions.S.MatKR k r) : Prop :=
  ∃ n ∈ Formalism.QuantumDeterminants.Nset k r, ∃ s ∈ Formalism.QuantumDeterminants.UWset k r z, ∃ s' ∈ Formalism.QuantumDeterminants.UWset k r z', ∃ n' ∈ Formalism.QuantumDeterminants.Nset k r,
    γ' = (s * n) * γ * (n' * s')

variable {D : D7} {X : HidaSetting D} {Y : Full X} {hF : FinX Y} (hI : SIso D.s (sOf hF)) {θ : ℝ} (C : Choice X θ)
  (hB : WuBessel C) (u u' : D.what₂.Word)

def JMove : Prop :=
  ∀ (τ : D.what₂.Tau) (γ γ' : Formalism.MainNotions.S.MatKR D.R.k D.R.rS) (ν ν' : Measure (Formalism.QuantumDeterminants.Mt D.R.k D.R.rS)),
    Move (locW C u u' τ).z (locW C u u' τ).z' γ γ' → (∃ p, RelPt D (locW C u u' τ).z (locW C u u' τ).z' γ p) →
    RMeas D (locW C u u' τ) γ 1 ν → RMeas D (locW C u u' τ) γ' 1 ν' →
    hsNormSq ((locS hB u u' τ).J ν' γ') = hsNormSq ((locS hB u u' τ).J ν γ)

def DecR : Prop :=
  ∀ t : D.s.Term u u', D.s.Gterm t ≠ 0 → D.s.relevant t → ∀ τ,
    Move (locW C u u' τ).z (locW C u u' τ).z'
      (Formalism.L2.SG.Pf.JointAmplitudePoints.gamP C u u' (Formalism.L2.SG.Pf.AmpWinJF.wt hI t) τ) (Formalism.L2.SG.LoopTerm.gamR hI C t τ) ∧
    ∃ p, RelPt D (locW C u u' τ).z (locW C u u' τ).z'
      (Formalism.L2.SG.Pf.JointAmplitudePoints.gamP C u u' (Formalism.L2.SG.Pf.AmpWinJF.wt hI t) τ) p

def RMeasExT : Prop :=
  ∀ t : D.s.Term u u', D.s.Gterm t ≠ 0 → D.s.relevant t → ∀ τ,
    ∃ ν, RMeas D (locW C u u' τ) (Formalism.L2.SG.Pf.JointAmplitudePoints.gamP C u u' (Formalism.L2.SG.Pf.AmpWinJF.wt hI t) τ) 1 ν

end Formalism.L2.SG.Pf.LocalDoubleCoset
