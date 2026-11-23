import Mathlib
import Formalism.ThetaLogCoordinates.UniformThetaSubstitution.StatementH
import Formalism.ThetaLogCoordinates.UniformThetaSubstitution.ThmSUniform

noncomputable section

open scoped BigOperators
open Finset

namespace Formalism.InvariantFactorPaths.G7

open Formalism.DworkPowerSeriesWeights (Integral mvExp frameJet)
open Formalism.GrowthSums (gamP rhoP gainG excessGain)

def thetaLog {K : Type} [Field K] {ν r0 r1 : ℕ} [NeZero ν] (om oms : Fin ν → ZMod (2 * ν) → K)
    (ϖ : K) (μ : PowerSeries K) (Tht : MvPowerSeries (Bool × EV ν r0 r1) K) :
    MvPowerSeries (ZV ν r0 r1) K :=
  MvPowerSeries.subst
    (fun x => MvPowerSeries.C ϖ⁻¹ * (MvPowerSeries.X x : MvPowerSeries (ZV ν r0 r1) K))
    (MvPowerSeries.subst (fun x => MvPowerSeries.C ϖ * sSub om oms μ x) Tht)

def KernelBoundsOfUnramifiedExponent : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (K0 : Type) [NormedField K0] [IsUltrametricDist K0] [CharZero K0]
    [CompleteSpace K0] (σ : K0 →+* K0), UnrOK K0 p σ → (∃ ζ : K0, IsPrimitiveRoot ζ (p ^ 2 - 1)) →
    ∀ F : MvPowerSeries (Fin 2) K0, IsLawOfLog p F →
    ∀ be : MvPowerSeries (Fin 2) K0, BetaHyp p F be →
    ∀ (j : K0 →+* ℂ_[p]) (ν r0 r1 : ℕ) [NeZero ν], (∀ a, ‖j a‖ = ‖a‖) →
    ∀ (om oms : Fin ν → ZMod (2 * ν) → ℂ_[p]) (ϖ : ℂ_[p]) (μ : PowerSeries ℂ_[p])
      (U0 Φ : MvPowerSeries (Bool × EV ν r0 r1) ℂ_[p]),
      ϖ ^ (p ^ 2 - 1) = (p : ℂ_[p]) → OmOK p ν om oms →
      PowerSeries.constantCoeff μ = 0 →
      (PowerSeries.subst μ (lamF p ϖ) : PowerSeries ℂ_[p]) = PowerSeries.X → Integral U0 →
      MvPowerSeries.constantCoeff Φ = 0 →
      Simeq Φ (∑ e : EV ν r0 r1, MvPowerSeries.subst
        (fun a : Fin 2 => (MvPowerSeries.X (if a = 0 then (false, e) else (true, e)) :
          MvPowerSeries (Bool × EV ν r0 r1) ℂ_[p])) (MvPowerSeries.map j be)) →
    ∀ (TT : Finset (ZMod (2 * ν))) (colN : ZMod (2 * ν) → ℕ) (hts : ∀ s, Fin (colN s) → ℕ)
      (hp : ∀ s c, hts s c ≤ r0) (I : ∀ s c, Fin (hts s c) → Fin r1) n,
      ‖MvPolynomial.coeff n (frameJet colN hts hp I (thetaLog om oms ϖ μ (mvExp (-Φ) * U0)))‖ ≤
          (p : ℝ) ^ (-(excessGain (p : ℝ) TT (dSet TT) (fun s => (alG TT colN hts s : ℝ))
            (fun s => (capG TT colN hts s : ℝ))
            (deLoss p r0 r1 TT (alG TT colN hts) (lsG TT colN hts)))) ∧
      ‖MvPolynomial.coeff n (frameJet colN hts hp I (thetaLog om oms ϖ μ (mvExp (-Φ) * U0)))‖ ≤
          (p : ℝ) ^ (-(gainG (p : ℝ) TT (oddT TT) (fun s => (alG TT colN hts s : ℝ))
            (fun s => (capG TT colN hts s : ℝ))
            (deLoss p r0 r1 TT (alG TT colN hts) (lsG TT colN hts)) -
            ∑ s ∈ TT \ oddT TT, (alG TT colN hts s : ℝ))) ∧
      ∀ i : ℕ, 1 ≤ i →
        ‖(p : ℂ_[p]) ^ (∑ s : ZMod (2 * ν), ∑ c : Fin (colN s),
            (if s.val % 2 = 0 then
              min (hts s c) i -
                ((univ.image (I s c)) ∩ univ.filter (fun b : Fin r1 => b.val < i)).card
            else ((univ.image (I s c)) ∩ univ.filter (fun b : Fin r1 => b.val < i)).card)) *
          MvPolynomial.coeff n
            (frameJet colN hts hp I (thetaLog om oms ϖ μ (mvExp (-Φ) * U0)))‖ ≤
          (p : ℝ) ^ (-(gainG (p : ℝ) TT (oddT TT) (fun s => (alG TT colN hts s : ℝ))
            (fun s => (capG TT colN hts s : ℝ))
            (deLoss p r0 r1 TT (alG TT colN hts) (lsG TT colN hts))))

def ThetaLogCoord : Prop :=
  ∀ (K : Type) [Field K] (p ν r0 r1 : ℕ) [NeZero ν] (om oms : Fin ν → ZMod (2 * ν) → K) (ϖ : K)
    (μ : PowerSeries K) (x : Bool × EV ν r0 r1), 2 ≤ p → (p : K) ≠ 0 → ϖ ≠ 0 →
    PowerSeries.constantCoeff μ = 0 →
    (PowerSeries.subst μ (lamF p ϖ) : PowerSeries K) = PowerSeries.X →
    PowerSeries.subst (MvPowerSeries.subst
        (fun y => MvPowerSeries.C ϖ⁻¹ * (MvPowerSeries.X y : MvPowerSeries (ZV ν r0 r1) K))
        (MvPowerSeries.C ϖ * sSub om oms μ x)) (lgF K p) = zLin om oms x

end Formalism.InvariantFactorPaths.G7
