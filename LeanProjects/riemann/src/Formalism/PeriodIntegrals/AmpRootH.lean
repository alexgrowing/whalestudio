import Formalism.SharpRestriction.CuspSpanNormBounds.RootMeasBig

open MeasureTheory
open scoped ENNReal

noncomputable section

namespace PI.AmpRootH

open Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions.S

def RootHaar : Prop :=
  ∀ (k r : ℕ) (L : LocBessel k r) (p : Point ℂ (r + 1)) (g₀ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)
    (μ₀ : Measure (Mt k r)), L.c ≠ 0 → IsPtRepO L p g₀ → 0 < Gf k r L.z L.z' g₀ →
    μ₀ {x | Matrix.of x ∉ Rset k r g₀} = 0 →
    μ₀.map (rootCoords k r L.z' p) = ENNReal.ofReal ((‖L.c‖ / (2 * Real.pi)) ^ (rootPat p).card) • volume →
    IsHaarOn (RStab k r g₀) (μ₀.map (fun x => fun i j => (g₀ * Matrix.of x * g₀⁻¹) i j))

end PI.AmpRootH
