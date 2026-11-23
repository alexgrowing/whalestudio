import Formalism.GaussJetBounds.StatementO

noncomputable section
open scoped BigOperators

universe u v w

namespace Formalism.DworkPowerSeriesWeights

open Formalism.IncomingBounds

def OrbitsAddFam : Prop :=
  ∀ (K : Type u) [NormedField K] [IsUltrametricDist K] [CharZero K] (l : ℕ), l.Prime →
    ‖(l : K)‖ < 1 → ∀ (O : Type w) [Fintype O] (ι : O → Type v) [∀ o, Fintype (ι o)]
      (sig : ∀ o, ι o → ℝ) (κ : (Σ o, ι o) →₀ ℕ) (a : ℕ), 1 ≤ a → (∀ i, κ i ≤ a) →
    ∀ (B : ∀ o, MvPowerSeries (ι o) K) (U : MvPowerSeries (Σ o, ι o) K),
      (∀ o, MvPowerSeries.constantCoeff (B o) = 0) →
      (∀ o, ∀ n : ι o →₀ ℕ, (∀ i, n i ≤ κ ⟨o, i⟩) →
        MonoWtGe ‖(l : K)‖ (fun i => rho l + sig o i) (1 / ((l : ℝ) - 1)) n
          (MvPowerSeries.coeff n (B o))) →
      (∀ n, n ≤ κ → MonoWtGe ‖(l : K)‖ (fun x : (Σ o, ι o) => rho l + sig x.1 x.2) 0 n
        (MvPowerSeries.coeff n U)) →
      ‖((mfact κ : ℕ) : K) * MvPowerSeries.coeff κ (U * mvExp
          (∑ o, MvPowerSeries.subst
            (fun i : ι o => (MvPowerSeries.X ⟨o, i⟩ : MvPowerSeries (Σ o, ι o) K)) (B o)))‖ ≤
        ‖(l : K)‖ ^ ((∑ o, ∑ i, (κ ⟨o, i⟩ : ℝ) * (gam l - sig o i)) -
          (∑ o, (Fintype.card (ι o) : ℝ)) * (Real.logb l (a : ℝ) + 1))

def OneLetterWt : Prop :=
  ∀ (K : Type u) [NormedField K] [IsUltrametricDist K] [CharZero K] (l N0 N1 : ℕ),
    l.Prime → Odd l → ‖(l : K)‖ < 1 →
    ∀ (K0 : Subfield K), Unram l K0 → ∀ ζ : K, IsPrimitiveRoot ζ (l ^ 2 - 1) →
    ∀ be : MvPowerSeries (ZMod 2) K, BHyp l 2 K0 ζ be →
    ∀ (ep : K), ‖ep‖ = 1 →
    ∀ (ι : Type v) [Fintype ι] (M : Fin N0 × Fin N1 → ι → K), (∀ x i, ‖M x i‖ ≤ 1) →
    ∀ (sgn : K), (sgn = 1 ∨ sgn = -1) →
      MvPowerSeries.constantCoeff ((sgn / 2) • ∑ x : Fin N0 × Fin N1, MvPowerSeries.subst
              (fun s : ZMod 2 => (if s = 0 then (1 : K) else ep) •
                ∑ i, MvPowerSeries.C (M x i) * MvPowerSeries.X i) be : MvPowerSeries ι K) = 0 ∧
      WtGe ‖(l : K)‖ (fun _ : ι => rho l + 1 / ((l : ℝ) + 1)) (1 / ((l : ℝ) - 1))
        ((sgn / 2) • ∑ x : Fin N0 × Fin N1, MvPowerSeries.subst
              (fun s : ZMod 2 => (if s = 0 then (1 : K) else ep) •
                ∑ i, MvPowerSeries.C (M x i) * MvPowerSeries.X i) be)

end Formalism.DworkPowerSeriesWeights
