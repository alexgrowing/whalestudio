import Formalism.LocalToGlobal.TorsionIntegrality.RamifiedCurveKernels.IntDThmB

noncomputable section
open scoped BigOperators

namespace Formalism.L2.Th1.G

open Formalism.L2.Th1.C
open Formalism.G (unitBall)
open Formalism.DworkPowerSeriesWeights (JetsIntegral jetPairPoly minorProd)

def IntDThmBGauss : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (l linv ph : PowerSeries ℂ_[p]),
    Frame (unitBall ℂ_[p]) l linv ph → IsOneUnit (unitBall ℂ_[p]) (PowerSeries.derivative ℂ_[p] l) →
    F1 (unitBall ℂ_[p]) l linv ph → ShapeAt l linv ph p → ‖(2 : ℂ_[p])‖ = 1 →
    ∀ (O : Type) [CommRing O] [StarRing O] (τ : O →+* ℂ_[p]),
    (∀ α, EndInt (unitBall ℂ_[p]) l linv (τ α)) →
    (∀ z : O, star z = z → IsBinomScalar (unitBall ℂ_[p]) (τ z)) →
    (∀ α : O, PhNormAt (unitBall ℂ_[p]) l linv ph (τ α) (τ (star α))) →
    (∀ α : O, AdjAt (unitBall ℂ_[p]) l linv ph (τ α) (τ (star α))) →
    ∀ (n m : Type) [Fintype n] [DecidableEq n] [Fintype m] (w : n → O), (∀ j, star (w j) = w j) →
    ∀ δ : m → Fin 4 × n → O,
      (∀ a b, ∑ i, star (δ i a) * δ i b = if a = b then w a.2 else 0) →
    ∀ (Th : MvPowerSeries n ℂ_[p]) (G : MvPowerSeries (Fin 4 × n) ℂ_[p]), IntMv (unitBall ℂ_[p]) G →
      tens4 Th = toZ linv (mvExp (-(phIso τ l linv ph δ)) * G) →
    ∀ (H : Type) [Fintype H] [DecidableEq H] (N0 N1 : ℕ)
      (A : n → ((Bool × H) × Fin N0 × Fin N1) → ℂ_[p]) (u : H → ℂ_[p]) (th : ℂ_[p])
      (Q2 : MvPowerSeries ((Bool × H) × Fin N0 × Fin N1) ℂ_[p]),
    (∀ i x, ‖A i x‖ ≤ 1) → ‖th‖ ≤ ‖(p : ℂ_[p])‖ ^ (1 / 2 : ℝ) →
    (∀ t, ‖u t‖ ≤ 1) → MvPowerSeries.constantCoeff Q2 = 0 → JetsIntegral Q2 →
    linSub A (sqSum (fun j => τ (w j))) =
      MvPowerSeries.C 2 * betaPair H N0 N1 u + MvPowerSeries.C th * Q2 →
    ∀ (TT : Finset H) (colN : Bool × H → ℕ) (ht : ∀ τ, Fin (colN τ) → ℕ)
      (hht : ∀ τ c, ht τ c ≤ N0), (∀ τ c, 1 ≤ ht τ c) → ∀ (I : ∀ τ c, Fin (ht τ c) → Fin N1),
    ∀ (nu1 nu2 size : Bool × H → ℕ), (∀ τ, nu1 τ = colN τ) →
      (∀ τ, nu2 τ = (Finset.univ.filter (fun c => 2 ≤ ht τ c)).card) →
      (∀ τ, size τ = ∑ c, ht τ c) →
    ∀ nn : ((Bool × H) × Fin N0 × Fin N0) →₀ ℕ,
      ‖MvPolynomial.coeff nn (jetPairPoly (∏ τ : Bool × H, minorProd
            (fun (i : Fin N0) (b : Fin N1) =>
              (∑ a : Fin N0, MvPolynomial.C (MvPolynomial.X (τ, i, a)) * MvPolynomial.X (τ, a, b) :
                MvPolynomial ((Bool × H) × Fin N0 × Fin N1)
                  (MvPolynomial ((Bool × H) × Fin N0 × Fin N0) ℂ_[p])))
            (ht τ) (hht τ) (I τ))
          (linSub A Th))‖ ≤
        ‖(p : ℂ_[p])‖ ^ (-(1 / 2 : ℝ) * ∑ t : H, ((size (false, t) : ℝ) -
          (if t ∈ TT then (nu1 (false, t) : ℝ) - nu2 (false, t) else 0) +
          (if t ∈ TT then (nu1 (true, t) : ℝ) else 0)))

end Formalism.L2.Th1.G
