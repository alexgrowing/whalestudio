import Formalism.SharpRestriction.CuspSpanNormBounds.RootMeasBig

open MeasureTheory
open scoped ENNReal

noncomputable section

namespace PI.AmpRoot

open Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions.S

def RootJac : Prop :=
  ∀ (k r : ℕ) (L : LocBessel k r) (p : Point ℂ (r + 1)) (g₀ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)
    (μ₀ : Measure (Mt k r)), IsPtRepO L p g₀ → 0 < Gf k r L.z L.z' g₀ →
    μ₀ {x | Matrix.of x ∉ Rset k r g₀} = 0 →
    μ₀.map (rootCoords k r L.z' p) = ENNReal.ofReal ((‖L.c‖ / (2 * Real.pi)) ^ (rootPat p).card) • volume →
    IsRootMeas L p g₀ (μ₀.map (fun x => fun i j => (g₀ * Matrix.of x * g₀⁻¹) i j))

def RelAtPt : Prop :=
  ∀ (k r : ℕ) (L : LocBessel k r) (p : Point ℂ (r + 1)) (g₀ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ),
    star L.c = L.c → IsPtRepO L p g₀ → 0 < Gf k r L.z L.z' g₀ → IsRelStab L g₀

end PI.AmpRoot
