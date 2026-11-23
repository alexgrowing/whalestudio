import Formalism.LocalToGlobal.TorsionIntegrality.GaussianEigenFrames.StatementH

noncomputable section
open scoped BigOperators

namespace Formalism.L2.AlgTh

open Formalism.L2.Th1.G (linSub)
open Formalism.DworkPowerSeriesWeights (JetsIntegral mfact)

def scl {K : Type} [Field K] (n : Type) [DecidableEq n] (c : K) : n → n → K := fun i j => if i = j then c else 0

def LogDerJets : Prop :=
  ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CharZero K] (F a : PowerSeries K) (ρ : ℝ), 1 ≤ ρ →
    PowerSeries.derivative K F = a * F → ‖PowerSeries.constantCoeff F‖ ≤ 1 →
    (∀ i : ℕ, ‖((i.factorial : ℕ) : K) * PowerSeries.coeff i a‖ ≤ ρ) →
    ∀ i : ℕ, ‖((i.factorial : ℕ) : K) * PowerSeries.coeff i F‖ ≤ ρ ^ i

def PowLogDer : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (G V : PowerSeries K) (c : K) (M : ℕ), 0 < M → c ≠ 0 →
    G ^ M = PowerSeries.C (c ^ M) * V →
    PowerSeries.C (M : K) * (PowerSeries.derivative K G * V) = G * PowerSeries.derivative K V

def ScaleJets : Prop :=
  ∀ (K : Type) [NormedField K] (n : Type) [Fintype n] [DecidableEq n] (c : K) (f : MvPowerSeries n K),
    JetsIntegral (linSub (scl n c) f) ↔
      ∀ κ : n →₀ ℕ, ‖((mfact κ : ℕ) : K) * MvPowerSeries.coeff κ f‖ * ‖c‖ ^ κ.degree ≤ 1

def ProdScaleJets : Prop :=
  ∀ (K : Type) [NormedField K] [IsUltrametricDist K] (κ n : Type) [Fintype κ] [Fintype n] [DecidableEq n] (c : K)
    (r : κ → K) (H : κ → n → PowerSeries K), (∀ k, ‖r k‖ ≤ 1) →
    (∀ k i (j : ℕ), ‖((j.factorial : ℕ) : K) * PowerSeries.coeff j (H k i)‖ * ‖c‖ ^ j ≤ 1) →
    JetsIntegral (linSub (scl n c) (Formalism.L2.Th1.E.thetaProd r H))

def LinScale : Prop :=
  ∀ (K : Type) [Field K] (n m : Type) [Fintype n] [Fintype m] [DecidableEq n] [DecidableEq m] (c : K) (A : n → m → K)
    (f : MvPowerSeries n K),
    linSub (scl m c) (linSub A f) = linSub (fun i x => c * A i x) f ∧
    linSub A (linSub (scl n c) f) = linSub (fun i x => c * A i x) f

end Formalism.L2.AlgTh
