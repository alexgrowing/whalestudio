import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
import Formalism.LocalToGlobal.ProjectiveLattices.CuspidalL2Subspace
import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsTopologicalRingAE

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum
open NumberField Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.VacRealForm

open GlobalTheory.FockCompare

variable {D : D7}

def frPt {m n : ℕ} (B : D.what₂.Tau → Matrix (Fin n) (Fin n) ℂ) (B' : D.what₂.Tau → Matrix (Fin m) (Fin m) ℂ)
    (Z : D.what₂.Tau → Fin m → Fin n → ℂ) : D.what₂.Tau → Fin m → Fin n → ℂ :=
  fun τ => (B' τ * Matrix.of (Z τ) * (B τ)⁻¹ : Matrix (Fin m) (Fin n) ℂ)

def sqSum {m n : ℕ} (Z : D.what₂.Tau → Fin m → Fin n → ℂ) : ℝ := ∑ τ, ∑ a, ∑ b, ‖Z τ a b‖ ^ 2

def gZ (σ : (D.what₂.Tau → ℂ) →+ AE D) (S T : HSp D) (B : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ)
    (B' : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) (f : WO S T → ℂ) (Z : D.what₂.Tau → Fin T.rank → Fin S.rank → ℂ) : ℂ :=
  f (iotaW σ T S (frPt B B' Z)) * Complex.exp ((Real.pi * Formalism.L2.Pj.xiR D * sqSum Z : ℝ) : ℂ)

def thY (σ : (D.what₂.Tau → ℂ) →+ AE D) (S T : HSp D) (B : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ)
    (B' : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) (f : WO S T → ℂ) (δ : ℂ)
    (Y : D.what₂.Tau → Fin T.rank → Fin S.rank → ℂ) : ℂ :=
  gZ σ S T B B' f (δ⁻¹ • Y)

end GlobalTheory.VacRealForm
