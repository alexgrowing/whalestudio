import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DbarEqZeroOfHolomorphic
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeriodMapFlatDerivative
open Matrix GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe GlobalTheory.TorsionForm GlobalTheory.TorsionForm.FlatAcyc
open scoped Real ContDiff

set_option autoImplicit false

namespace GlobalTheory.TorsionForm.FlatAcyc

theorem curvature_vertical : ∀ {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {g : ℕ} {B : Set E}
    {τ : E → Matrix (Fin g) (Fin g) ℂ} (hτ : IsPeriodMap B τ) {b : E} (hb : b ∈ B)
    (z v w : Fin g → ℂ),
    om0 τ (b, z) ![(0, v), (0, w)] = riem (flatOf (τ b) v) (flatOf (τ b) w) := by
  intro E _ _ g B τ hτ b hb z v w
  have hv := GlobalTheory.FlatVert.dflat_vert hτ b hb z v
  have hw := GlobalTheory.FlatVert.dflat_vert hτ b hb z w
  show riem _ _ = _
  simp only [ContinuousAlternatingMap.compContinuousLinearMap_apply]
  simp [hv, hw]

end GlobalTheory.TorsionForm.FlatAcyc
