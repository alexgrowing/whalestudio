import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsArith
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.GeometryOfNumbersTheory Filter Asymptotics

noncomputable section

variable {D : ℕ} {Ω : Type} [Field Ω] [CharZero Ω] {κ : Type} [Fintype κ]

def HSMDatum.withMetric (d : HSMDatum D Ω κ) (m : ConeMetric ℂ (Ix κ)) (P0 : Ideal (MRing (GlobalTheory κ)))
    (hs : IsSmoothMetric m) (hc : IsConjInvariant m) (hle : P0 ≤ coordIdeal ℤ d.x)
    (hp : IsSemipositiveRel P0 (coordIdeal ℤ d.x) (HermLine.ofCone m)) : HSMDatum D Ω κ :=
  { d with m := m, P0 := P0, smooth := hs, conjInv := hc, normalForm_baseLattice_le_dualSpan_sup_line := hle, semipos := hp }

def DefectMetricChange.Statement : Prop :=
  ∀ (D : ℕ) (Ω : Type) [Field Ω] [CharZero Ω] (κ : Type) [Fintype κ] (I : AllFam) (d : HSMDatum D Ω κ)
    (m₁ : ConeMetric ℂ (Ix κ)) (P0₁ : Ideal (MRing (GlobalTheory κ))) (hs : IsSmoothMetric m₁)
    (hc : IsConjInvariant m₁) (hle : P0₁ ≤ coordIdeal ℤ d.x)
    (hp : IsSemipositiveRel P0₁ (coordIdeal ℤ d.x) (HermLine.ofCone m₁)) (e : Fin (D + 1) → Ix κ),
    I.IsFamily → IsProjFrame d.x e →
    (fun n => hsDefect D (resChi (d.withMetric m₁ P0₁ hs hc hle hp)) (top I d.x m₁ D) n -
        hsDefect D (resChi d) (top I d.x d.m D) n) =o[atTop] pw D

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
