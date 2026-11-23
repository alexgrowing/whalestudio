import Formalism.LocalToGlobal.Divisibility.JetBounds.IsExpansion

open scoped BigOperators

noncomputable section

namespace Formalism.L2.DIV

open Formalism.DworkPowerSeriesWeights Formalism.DworkPowerSeriesWeights.OddLevelGainBounds Formalism.IncomingBounds

def minorProductsLattice {k : Type} [NormedField k] [IsUltrametricDist k] {N0 C : ℕ} (p : Fin C → ℕ) (hp : ∀ c, p c ≤ N0) :
    Submodule (unitBall k) (MvPolynomial (Fin N0 × Fin N0) k) :=
  Submodule.span (unitBall k) {P | ∃ A : ∀ c, Fin (p c) → Fin N0, P = minorProd
    (fun (i a : Fin N0) => (MvPolynomial.X (i, a) : MvPolynomial (Fin N0 × Fin N0) k)) p hp A}

def OrbSys.ap {k : Type} [NormedField k] (S : OrbSys k) (δ : MvPolynomial S.σ k →ₗ[k] k) : OrbSys k where
  ι := S.ι
  σ := Empty
  g := S.g
  E := S.E
  P := ∑ κ ∈ S.P.support, MvPolynomial.monomial κ (MvPolynomial.C (δ (MvPolynomial.coeff κ S.P)))

def sysF (l : ℕ) [Fact l.Prime] (d N0 N1 : ℕ) [NeZero d]
    (g : ZV d N0 N1 → MvPowerSeries (ZV d N0 N1) ℂ_[l]) (E : MvPowerSeries (ZV d N0 N1) ℂ_[l]) (colN : ZMod d → ℕ)
    (p : ∀ s, Fin (colN s) → ℕ) (hp : ∀ s c, p s c ≤ N0) (I : ∀ s c, Fin (p s c) → Fin N1) : OrbSys ℂ_[l] where
  ι := ZV d N0 N1
  σ := ZMod d × Fin N0 × Fin N0
  g := g
  E := E
  P := ∏ s : ZMod d, minorProd
        (fun (i : Fin N0) (b : Fin N1) =>
          (∑ a : Fin N0, MvPolynomial.C (MvPolynomial.X (s, i, a)) * MvPolynomial.X (s, a, b) :
            MvPolynomial (ZV d N0 N1) (MvPolynomial (ZMod d × Fin N0 × Fin N0) ℂ_[l])))
        (p s) (hp s) (I s)

inductive IsSysW (l : ℕ) [Fact l.Prime] (Q : OrbSys ℂ_[l] → ℝ → Prop) : OrbSys ℂ_[l] → ℝ → Prop
  | caseA (d N0 N1 : ℕ) [NeZero d] (h3 : 3 ≤ l) (h2 : 2 ≤ d) (he : Even d) (hN0 : 0 < N0) (K0 : Subfield ℂ_[l])
      (hK : Unram l K0) (ζ : ℂ_[l]) (hζ : IsPrimitiveRoot ζ (l ^ d - 1)) (be : MvPowerSeries (ZMod d) ℂ_[l])
      (hb : BHyp l d K0 ζ be) (g : ZV d N0 N1 → MvPowerSeries (ZV d N0 N1) ℂ_[l])
      (hg0 : ∀ y, MvPowerSeries.constantCoeff (g y) = 0)
      (hg : ∀ y, MvPowerSeries.subst g (entLog (K := ℂ_[l]) l y) = MvPowerSeries.X y)
      (ε : ℂ_[l]) (hε : ε = 1 ∨ ε = -1)
      (TT : Finset (ZMod d)) (colN : ZMod d → ℕ) (p : ∀ s, Fin (colN s) → ℕ)
      (hp : ∀ s c, p s c ≤ N0) (hp1 : ∀ s c, 1 ≤ p s c) (I : ∀ s c, Fin (p s c) → Fin N1)
      (nu1 nu2 size : ZMod d → ℕ) (h1 : ∀ s, nu1 s = colN s)
      (h22 : ∀ s, nu2 s = (Finset.univ.filter (fun c => 2 ≤ p s c)).card)
      (hs : ∀ s, size s = ∑ c, p s c)
      (hJ : ∀ s, JnumOneLetter l d TT nu1 size s + (if s ∈ TT then 1 else 0) ≤ N0)
      (δ : MvPolynomial (ZMod d × Fin N0 × Fin N0) ℂ_[l] →ₗ[ℂ_[l]] ℂ_[l])
      (hδ : ∀ R ∈ nablaO (K := ℂ_[l]) colN p hp, ‖δ R‖ ≤ 1) :
      IsSysW l Q ((sysA l d N0 N1 be g ε colN p hp I).ap δ) (expA l d N0 N1 TT nu1 nu2 size)
  | caseB (N0 N1 C : ℕ) (h3 : 3 ≤ l)
      (K0 : Subfield ℂ_[l]) (hK : Unram l K0) (ζ : ℂ_[l]) (hζ : IsPrimitiveRoot ζ (l ^ 2 - 1))
      (be : MvPowerSeries (ZMod 2) ℂ_[l]) (hb : BHyp l 2 K0 ζ be) (ep : ℂ_[l]) (hep : ‖ep‖ = 1)
      (g : Fin N0 × Fin N1 → MvPowerSeries (Fin N0 × Fin N1) ℂ_[l])
      (hg0 : ∀ y, MvPowerSeries.constantCoeff (g y) = 0)
      (hg : ∀ y, MvPowerSeries.subst g (oneLog (K := ℂ_[l]) l y) = MvPowerSeries.X y)
      (sgn : ℂ_[l]) (hsg : sgn = 1 ∨ sgn = -1)
      (p : Fin C → ℕ) (hp : ∀ c, p c ≤ N0) (I : ∀ c, Fin (p c) → Fin N1)
      (δ : MvPolynomial (Fin N0 × Fin N0) ℂ_[l] →ₗ[ℂ_[l]] ℂ_[l])
      (hδ : ∀ R ∈ minorProductsLattice (k := ℂ_[l]) p hp, ‖δ R‖ ≤ 1) :
      IsSysW l Q ((sysB l N0 N1 C be ep g sgn p hp I).ap δ) (expB l N0 N1 C p)
  | knownA (d N0 N1 : ℕ) [NeZero d] (g : ZV d N0 N1 → MvPowerSeries (ZV d N0 N1) ℂ_[l])
      (E : MvPowerSeries (ZV d N0 N1) ℂ_[l])
      (colN : ZMod d → ℕ) (p : ∀ s, Fin (colN s) → ℕ) (hp : ∀ s c, p s c ≤ N0) (I : ∀ s c, Fin (p s c) → Fin N1) (β : ℝ)
      (hq : Q (sysF l d N0 N1 g E colN p hp I) β)
      (δ : MvPolynomial (ZMod d × Fin N0 × Fin N0) ℂ_[l] →ₗ[ℂ_[l]] ℂ_[l])
      (hδ : ∀ R ∈ nablaO (K := ℂ_[l]) colN p hp, ‖δ R‖ ≤ 1) :
      IsSysW l Q ((sysF l d N0 N1 g E colN p hp I).ap δ) β
  | mon {S : OrbSys ℂ_[l]} {β : ℝ} (hS : IsSys7 l Q S β) (δ : MvPolynomial S.σ ℂ_[l] →ₗ[ℂ_[l]] ℂ_[l]) (hδ : MonInt δ) :
      IsSysW l Q (S.ap δ) β
  | mul {S₁ S₂ : OrbSys ℂ_[l]} {β₁ β₂ : ℝ} (h₁ : IsSysW l Q S₁ β₁) (h₂ : IsSysW l Q S₂ β₂) :
      IsSysW l Q (S₁.mul S₂) (β₁ + β₂)

def ApJet : Prop :=
  ∀ (k : Type) [NormedField k] (S : OrbSys k) (δ : MvPolynomial S.σ k →ₗ[k] k) (Th : MvPowerSeries S.ι k),
    jetPairPoly (S.ap δ).P Th = MvPolynomial.C (δ (jetPairPoly S.P Th))

def OneWeyl : Prop :=
  ∀ (k : Type) [NormedField k] [IsUltrametricDist k] (N0 N1 C : ℕ) (p : Fin C → ℕ) (hp : ∀ c, p c ≤ N0)
    (I : ∀ c, Fin (p c) → Fin N1) (Th : MvPowerSeries (Fin N0 × Fin N1) k)
    (δ : MvPolynomial (Fin N0 × Fin N0) k →ₗ[k] k), (∀ Q ∈ minorProductsLattice (k := k) p hp, ‖δ Q‖ ≤ 1) →
    ∀ B : ℝ, (∀ n, ‖MvPolynomial.coeff n (frameJetOne p hp I Th)‖ ≤ B) → ‖δ (frameJetOne p hp I Th)‖ ≤ B

def AWeyl : Prop :=
  ∀ (k : Type) [NormedField k] [IsUltrametricDist k] (d N0 N1 : ℕ) [NeZero d] (colN : ZMod d → ℕ)
    (p : ∀ s, Fin (colN s) → ℕ) (hp : ∀ s c, p s c ≤ N0) (I : ∀ s c, Fin (p s c) → Fin N1)
    (Th : MvPowerSeries (ZV d N0 N1) k) (δ : MvPolynomial (ZMod d × Fin N0 × Fin N0) k →ₗ[k] k),
    (∀ Q ∈ nablaO (K := k) colN p hp, ‖δ Q‖ ≤ 1) →
    ∀ B : ℝ, (∀ n, ‖MvPolynomial.coeff n (frameJet colN p hp I Th)‖ ≤ B) → ‖δ (frameJet colN p hp I Th)‖ ≤ B

def SysWBound : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (Q : OrbSys ℂ_[l] → ℝ → Prop), KnownOk l Q → ∀ (S : OrbSys ℂ_[l]) (β : ℝ), IsSysW l Q S β →
    HasJetBound S.g S.E S.P (‖(l : ℂ_[l])‖ ^ β)

end Formalism.L2.DIV
