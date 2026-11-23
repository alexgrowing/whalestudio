import Formalism.LocalToGlobal.TorsionIntegrality.TorsionTranslationPowers.StatementP

open PowerSeries

noncomputable section

namespace Formalism.L2.Th1.E

open Formalism.DworkPowerSeriesWeights (Integral mvExp)

section Four

variable {K : Type} [Field K]

def tensor4 {n : Type} (Θ : MvPowerSeries n K) : MvPowerSeries (Fin 4 × n) K :=
  ∏ a : Fin 4, MvPowerSeries.subst (fun i => (MvPowerSeries.X (a, i) : MvPowerSeries (Fin 4 × n) K)) Θ

def matCoord {O m : Type} [Semiring O] [Fintype m] (l linv : PowerSeries K) (τ : O →+* K)
    (γ : Matrix m m O) (w : m) : MvPowerSeries m K :=
  Formalism.L2.Th1.C.flin l linv (fun w' => τ (γ w w')) (fun w' => (MvPowerSeries.X w' : MvPowerSeries m K))

end Four

def FourthPower : Prop :=
  ∀ (K : Type) [NormedField K] [IsUltrametricDist K] (n : Type) (f : MvPowerSeries n K),
    Integral (tensor4 f) → Integral f

def ThetaFourthTensorPowerProductShape {K : Type} [NormedField K] [CharZero K] {O n : Type} [Semiring O] [Fintype n]
    (l linv ph : PowerSeries K) (τ : O →+* K) (Θ : MvPowerSeries n K) (γ : Matrix (Fin 4 × n) (Fin 4 × n) O) :
    Prop :=
  ∃ (κ : Type) (_ : Fintype κ) (r : κ → K) (V : κ → Fin 4 × n → PowerSeries K),
    (∀ k, ‖r k‖ ≤ 1) ∧ (∀ k w, IntS (V k w)) ∧
    MvPowerSeries.subst (matCoord l linv τ γ) (tensor4 Θ) =
      thetaProd r (fun k w => (mvExp (-ph) : PowerSeries K) * V k w)

def GeneralIntOf : Prop :=
  ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CharZero K] (R : Subring K),
    (∀ a, a ∈ R ↔ ‖a‖ ≤ 1) → ∀ (l linv ph : PowerSeries K), Formalism.L2.Th1.C.Frame R l linv ph →
    ∀ (O : Type) [CommRing O] [StarRing O] (τ : O →+* K),
    (∀ α, Formalism.L2.Th1.C.EndInt R l linv (τ α)) →
    (∀ z : O, star z = z → Formalism.L2.Th1.C.IsBinomScalar R (τ z)) →
    Formalism.L2.Th1.C.F1 R l linv ph →
    (∀ α : O, Formalism.L2.Th1.C.PhNormAt R l linv ph (τ α) (τ (star α))) →
    (∀ α : O, Formalism.L2.Th1.C.AdjAt R l linv ph (τ α) (τ (star α))) →
    ∀ (n : Type) [Fintype n] [DecidableEq n] (Θ : MvPowerSeries n K)
      (γ : Matrix (Fin 4 × n) (Fin 4 × n) O), γ.conjTranspose * γ = 1 →
      ThetaFourthTensorPowerProductShape l linv ph τ Θ γ → Integral (mvExp (phSum ph : MvPowerSeries n K) * Θ)

end Formalism.L2.Th1.E
