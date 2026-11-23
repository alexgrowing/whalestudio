import Mathlib
import Formalism.ThetaLogCoordinates.UniformThetaSubstitution.StatementE
import Formalism.GaussJetBounds.StatementP

noncomputable section

open scoped BigOperators
open Finset

namespace Formalism.InvariantFactorPaths.G7

open Formalism.DworkPowerSeriesWeights (Integral frameJet)
open Formalism.GrowthSums (gamP rhoP gainG excessGain)

section Shape

variable {ν : ℕ}

def alG (TT : Finset (ZMod (2 * ν))) (colN : ZMod (2 * ν) → ℕ) (hts : ∀ s, Fin (colN s) → ℕ)
    (s : ZMod (2 * ν)) : ℕ :=
  if s ∈ TT then (univ.filter (fun c => hts s c = 1)).card else 0

def capG (TT : Finset (ZMod (2 * ν))) (colN : ZMod (2 * ν) → ℕ) (hts : ∀ s, Fin (colN s) → ℕ)
    (s : ZMod (2 * ν)) : ℕ :=
  colN s - alG TT colN hts s

def lsG (TT : Finset (ZMod (2 * ν))) (colN : ZMod (2 * ν) → ℕ) (hts : ∀ s, Fin (colN s) → ℕ)
    (s : ZMod (2 * ν)) : ℕ :=
  ∑ c, hts s c - alG TT colN hts s

end Shape

def FrameJetExcessBound : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (ν r0 r1 : ℕ) [NeZero ν] (u : ZMod (2 * ν) → ℂ_[p])
    (F : MvPowerSeries (ZV ν r0 r1) ℂ_[p]) (TT : Finset (ZMod (2 * ν))) (colN : ZMod (2 * ν) → ℕ)
    (hts : ∀ s, Fin (colN s) → ℕ) (hp : ∀ s c, hts s c ≤ r0) (I : ∀ s c, Fin (hts s c) → Fin r1),
    2 < p → (∀ s, ‖u s‖ ≤ 1) → InClass (p : ℂ_[p]) (hhS p u) F →
    ∀ n, ‖MvPolynomial.coeff n (frameJet colN hts hp I F)‖ ≤
      (p : ℝ) ^ (-(excessGain (p : ℝ) TT (dSet TT) (fun s => (alG TT colN hts s : ℝ))
          (fun s => (capG TT colN hts s : ℝ))
          (deLoss p r0 r1 TT (alG TT colN hts) (lsG TT colN hts)) +
        rhoP p * ∑ s, ((alG TT colN hts s : ℝ) + lsG TT colN hts s)))

def FrameJetCappedBound : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (ν r0 r1 : ℕ) [NeZero ν] (u : ZMod (2 * ν) → ℂ_[p])
    (F : MvPowerSeries (ZV ν r0 r1) ℂ_[p]) (TT : Finset (ZMod (2 * ν))) (colN : ZMod (2 * ν) → ℕ)
    (hts : ∀ s, Fin (colN s) → ℕ) (hp : ∀ s c, hts s c ≤ r0) (I : ∀ s c, Fin (hts s c) → Fin r1),
    2 < p → (∀ s, ‖u s‖ ≤ 1) → InClass (p : ℂ_[p]) (hhS p u) F →
    ∀ n, ‖MvPolynomial.coeff n (frameJet colN hts hp I F)‖ ≤
      (p : ℝ) ^ (-(gainG (p : ℝ) TT (oddT TT) (fun s => (alG TT colN hts s : ℝ))
          (fun s => (capG TT colN hts s : ℝ))
          (deLoss p r0 r1 TT (alG TT colN hts) (lsG TT colN hts)) -
        ∑ s ∈ TT \ oddT TT, (alG TT colN hts s : ℝ) +
        rhoP p * ∑ s, ((alG TT colN hts s : ℝ) + lsG TT colN hts s)))

def GaussB : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (ν r0 r1 i : ℕ) [NeZero ν] (u : ZMod (2 * ν) → ℂ_[p])
    (F : MvPowerSeries (ZV ν r0 r1) ℂ_[p]) (TT : Finset (ZMod (2 * ν))) (colN : ZMod (2 * ν) → ℕ)
    (hts : ∀ s, Fin (colN s) → ℕ) (hp : ∀ s c, hts s c ≤ r0) (I : ∀ s c, Fin (hts s c) → Fin r1),
    2 < p → 1 ≤ i → (∀ s, ‖u s‖ ≤ 1) → InClass (p : ℂ_[p]) (hhS p u) F →
    ∀ n, ‖(p : ℂ_[p]) ^ (∑ s : ZMod (2 * ν), ∑ c : Fin (colN s),
          (if s.val % 2 = 0 then
            min (hts s c) i - ((univ.image (I s c)) ∩ univ.filter (fun b : Fin r1 => b.val < i)).card
          else ((univ.image (I s c)) ∩ univ.filter (fun b : Fin r1 => b.val < i)).card)) *
        MvPolynomial.coeff n (frameJet colN hts hp I F)‖ ≤
      (p : ℝ) ^ (-(gainG (p : ℝ) TT (oddT TT) (fun s => (alG TT colN hts s : ℝ))
          (fun s => (capG TT colN hts s : ℝ))
          (deLoss p r0 r1 TT (alG TT colN hts) (lsG TT colN hts)) +
        rhoP p * ∑ s, ((alG TT colN hts s : ℝ) + lsG TT colN hts s)))

end Formalism.InvariantFactorPaths.G7
