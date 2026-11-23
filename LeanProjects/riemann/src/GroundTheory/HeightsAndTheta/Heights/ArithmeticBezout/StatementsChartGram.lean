import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.IsSemipositiveOn
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

open Filter Topology
open ReciprocityTheory.ChartRestriction.G.Geo (maDensity)

def gramVol {e n : ℕ} (v : (Fin e → ℂ) → (Fin n → ℂ)) (y : Fin e → ℂ) : ℝ :=
  let w : Fin (e + 1) → Fin n → ℂ := Fin.cons (v y) fun j => fderiv ℂ v y (Pi.single j 1)
  (Matrix.det (Matrix.of fun a b => ∑ i, star (w a i) * w b i)).re

def ChartGramMA.Statement : Prop :=
  ∀ (e n : ℕ) (v : (Fin e → ℂ) → (Fin n → ℂ)) (y : Fin e → ℂ),
    (∀ᶠ y' in 𝓝 y, DifferentiableAt ℂ v y') → v y ≠ 0 →
      maDensity (fun _ y' => Real.log ‖WithLp.toLp 2 (v y')‖) y =
        (e.factorial : ℝ) / Real.pi ^ e * gramVol v y / ‖WithLp.toLp 2 (v y)‖ ^ (2 * (e + 1))

end GroundTheory.Heights₂.Heights
