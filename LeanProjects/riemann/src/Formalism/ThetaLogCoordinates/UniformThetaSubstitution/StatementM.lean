import Mathlib
import Formalism.ThetaLogCoordinates.UniformThetaSubstitution.CyclicPowerClassOfExpEquiv
import Formalism.GaussJetBounds.StatementI

noncomputable section

open scoped BigOperators
open Finset

namespace Formalism.InvariantFactorPaths.G7

open Formalism.DworkPowerSeriesWeights (Integral mvExp jetPair)

def ThmSExact : Prop :=
  ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CharZero K] (p ν r0 r1 : ℕ) [NeZero ν]
    (om oms : Fin ν → ZMod (2 * ν) → K) (c c' ϖ : K) (μ : PowerSeries K)
    (U : MvPowerSeries (Bool × EV ν r0 r1) K), p.Prime →
    ‖(p : K)‖ = (p : ℝ)⁻¹ → ϖ ^ (p ^ 2 - 1) = (p : K) → OmOK p ν om oms → ‖c‖ ≤ 1 → ‖c'‖ ≤ 1 →
    PowerSeries.constantCoeff μ = 0 →
    (PowerSeries.subst μ (lamF p ϖ) : PowerSeries K) = PowerSeries.X → Integral U →
    ∃ V : MvPowerSeries (ZV ν r0 r1) K, Integral V ∧
      MvPowerSeries.subst (fun x => MvPowerSeries.C ϖ * sSub om oms μ x)
          (mvExp (-(Gtot (E := EV ν r0 r1) p c c' 1)) * U) =
        mvExp (-(MvPowerSeries.C (ϖ ^ (p + 1) / (p : K)) * hhS p (uS c c'))) * V

def atPlace {K Pl : Type} [Field K] {ι : Pl → Type} (v : Pl) (f : MvPowerSeries (ι v) K) :
    MvPowerSeries (Σ v, ι v) K :=
  MvPowerSeries.subst (fun i : ι v => (MvPowerSeries.X ⟨v, i⟩ : MvPowerSeries (Σ v, ι v) K)) f

def PlacesAdd : Prop :=
  ∀ (K Pl : Type) [NormedField K] [IsUltrametricDist K] [Fintype Pl] [DecidableEq Pl]
    (ι : Pl → Type) [∀ v, Fintype (ι v)] (P : ∀ v, MvPolynomial (ι v) K)
    (f : ∀ v, MvPowerSeries (ι v) K) (ρ : Pl → ℝ),
    (∀ v, ∀ Uv : MvPowerSeries (ι v) K, Integral Uv → ‖jetPair (P v) (f v * Uv)‖ ≤ ρ v) →
    ∀ U : MvPowerSeries (Σ v, ι v) K, Integral U →
      ‖jetPair (∏ v, MvPolynomial.rename (Sigma.mk v) (P v)) ((∏ v, atPlace v (f v)) * U)‖ ≤
        ∏ v, ρ v

end Formalism.InvariantFactorPaths.G7
