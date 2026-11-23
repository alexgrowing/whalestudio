import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NontrivialIsomClassInt
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsTypeIsRealConst

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points

namespace GlobalTheory

structure HeightPairing {X : Scheme.{0}} (p : X ⟶ Sp ℤ) where

  CH : Type

  [ring : CommRing CH]

  c1 : HermLB p → CH

  firstChernCongr : ∀ L M, L.Isometric M → c1 L = c1 M

  firstChernTensor : ∀ L M, c1 (L.tens M) = c1 L + c1 M

  pair : CH →+ (X → ℝ)

  pair_one : ∀ x : X, IsClosed ({x} : Set X) → pair 1 x = Real.log (Nat.card (X.residueField x))

  pairingMulFirstChern : ∀ (Y : Scheme.{0}) (i : Y ⟶ X) [IsClosedImmersion i] [IsIntegral Y] [IsLocallyNoetherian Y] (e : ℕ),
    topologicalKrullDim Y = (e + 1 : ℕ) → ∀ (M N : HermLB p) (r : (M.restr i).B.ι → Y.functionFieldˣ)
    (hr : IsRatSec (M.restr i).B r), pair (c1 N ^ e * c1 M) (i (genericPoint Y)) =
      ∑ᶠ z, (((M.restr i).div hr).mult z : ℝ) * pair (c1 N ^ e) (i z) - (N.restr i).archInt (M.restr i) e hr

attribute [instance] HeightPairing.ring

def Published.HeightPairingExists : Prop :=
  ∀ (X : Scheme.{0}) (p : X ⟶ Sp ℤ) (D : ℕ), CxForm.IsRegVar p D → Nonempty (HeightPairing p)

end GlobalTheory
