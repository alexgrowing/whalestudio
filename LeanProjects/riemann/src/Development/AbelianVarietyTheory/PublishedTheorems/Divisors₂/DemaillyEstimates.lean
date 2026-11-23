import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DemaillyRegularisation

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Set Filter Topology
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.L2DbarEstimates GlobalTheory.CxPts GlobalTheory.ShFam GlobalTheory.ChernReg

namespace GlobalTheory.ChernReg

variable {k : Type} [CommRing k] {Y : Scheme.{0}} {p : Y ⟶ Sp k} {σ : k →+* ℂ} {d : ℕ} [SmoothOfRelativeDimension d p]

def psiC (a : ChartForm p σ d) (E : ChartMap p σ d) (ψ : CxPts p σ → EReal) (y : CxPts p σ) (w : ℂ) : ℝ :=
  mean (a (AlgChart.exists_mem_source (D := d) y).choose y) fun ξ =>
    (ψ (E (AlgChart.exists_mem_source (D := d) y).choose y (w • ξ))).toReal

def psiE (a : ChartForm p σ d) (E : ChartMap p σ d) (ψ : CxPts p σ → EReal) (y : CxPts p σ) (t : ℝ) : EReal :=
  if t = 0 then ψ y else (psiC a E ψ y t : ℝ)

end GlobalTheory.ChernReg

namespace GlobalTheory.Published

def DemaillyEstimates : Prop :=
  ∀ (k : Type) [CommRing k] (Y : Scheme.{0}) (p : Y ⟶ Sp k) (σ : k →+* ℂ) (d : ℕ) [SmoothOfRelativeDimension d p],
    CompactSpace (CxPts p σ) → T2Space (CxPts p σ) →
    ∀ (a θ : ChartForm p σ d) (E : ChartMap p σ d) (ψ : CxPts p σ → EReal),
      IsKaehlerForm (AnRead.all p σ d) a → IsExph a E → IsClosedForm (AnRead.all p σ d) θ →
      IsFormPsh (AnRead.all p σ d) θ ψ →
      ∃ A K δ₀ : ℝ, 0 ≤ A ∧ 0 < K ∧ 0 < δ₀ ∧
        (∀ y, MonotoneOn (fun t : ℝ => psiE a E ψ y t + ((K * t ^ 2 : ℝ) : EReal)) (Icc 0 δ₀)) ∧
        ∀ c : AlgChart p σ d, ∀ y ∈ c.e.source, ∀ w : ℂ, 0 < ‖w‖ → ‖w‖ < δ₀ → ∀ (ξ : V d) (η : ℂ),
          -(A * (‖w‖ * deriv (fun t : ℝ => psiC a E ψ y t + K * t ^ 2) ‖w‖) * a c y ξ.ofLp) -
              K * (‖w‖ ^ 2 * a c y ξ.ofLp + √(a c y ξ.ofLp) * ‖η‖ + ‖η‖ ^ 2) ≤
            θ c y ξ.ofLp +
              (leviForm (fun q : V d × ℂ => psiC a E ψ (c.e.symm q.1) q.2) (c.e y, w) (ξ, η) (ξ, η)).re / Real.pi

end GlobalTheory.Published

end
