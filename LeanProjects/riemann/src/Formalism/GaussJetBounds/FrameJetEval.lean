import Formalism.GaussJetBounds.StatementP

noncomputable section
open scoped BigOperators

namespace Formalism.DworkPowerSeriesWeights

open Formalism.IncomingBounds

def TransferB : Prop :=
  ∀ (F K : Type) [NormedField F] [CharZero F] [NormedField K] [CharZero K] (φ : F →+* K),
    (∀ z, ‖φ z‖ = ‖z‖) →
    ∀ (l d N0 N1 : ℕ) [NeZero d] (K0 : Subfield F) (ζ : F) (be : MvPowerSeries (ZMod d) F),
      (Unram l K0 → Unram l (K0.map φ)) ∧
      (BHyp l d K0 ζ be → BHyp l d (K0.map φ) (φ ζ) (MvPowerSeries.map φ be)) ∧
      (∀ g : ZV d N0 N1 → MvPowerSeries (ZV d N0 N1) F,
        (∀ y, MvPowerSeries.constantCoeff (g y) = 0) →
        (∀ y, MvPowerSeries.subst g (entLog (K := F) l y) = MvPowerSeries.X y) →
        (∀ y, MvPowerSeries.constantCoeff (MvPowerSeries.map φ (g y)) = 0) ∧
        ∀ y, MvPowerSeries.subst (fun y' => MvPowerSeries.map φ (g y')) (entLog (K := K) l y) =
          MvPowerSeries.X y) ∧
      (∀ U : MvPowerSeries (ZV d N0 N1) F, Integral U → Integral (MvPowerSeries.map φ U))

def FrameJetEval : Prop :=
  ∀ (F K : Type) [NormedField F] [CharZero F] [NormedField K] [CharZero K] (φ : F →+* K)
    (d N0 N1 : ℕ) [NeZero d] (g : ZV d N0 N1 → MvPowerSeries (ZV d N0 N1) F)
    (U : MvPowerSeries (ZV d N0 N1) F) (ε : F) (be : MvPowerSeries (ZMod d) F),
    (∀ y, MvPowerSeries.constantCoeff (g y) = 0) → MvPowerSeries.constantCoeff be = 0 →
    ∀ (colN : ZMod d → ℕ) (p : ∀ s, Fin (colN s) → ℕ) (hp : ∀ s c, p s c ≤ N0)
      (I : ∀ s c, Fin (p s c) → Fin N1) (x : ZMod d × Fin N0 × Fin N0 → K),
      MvPolynomial.eval₂ φ x (frameJet colN p hp I (thetaZ g U ε be)) =
        jetPair (∏ s : ZMod d, minorProd
            (fun (i : Fin N0) (b : Fin N1) => (MvPolynomial.X (s, i, b) : MvPolynomial (ZV d N0 N1) K))
            (p s) (hp s) (I s))
          (MvPowerSeries.subst (linSub (frameM (N1 := N1) x))
              (MvPowerSeries.subst (fun y => MvPowerSeries.map φ (g y)) (MvPowerSeries.map φ U)) *
            mvExp (φ ε • bSum (frameM (N1 := N1) x) (MvPowerSeries.map φ be)))

def LabelsExist : Prop :=
  ∀ (l d N0 : ℕ) [NeZero d], 2 ≤ l → ∀ (TT : Finset (ZMod d)) (nu1 size : ZMod d → ℕ) (a : ℕ),
    1 ≤ a → (∀ s, nu1 s ≤ a) → (∀ s, size s ≤ a) → 2 * Real.logb l a + 2 ≤ (N0 : ℝ) - 1 →
    ∃ (J : ZMod d → ℕ) (lab : ∀ s, Fin (J s) → ZMod d × ℤ) (m : ℕ),
      (∀ s, Function.Injective (lab s)) ∧
      (∀ (s s0 : ZMod d) (j : ℤ), (∃ i, lab s i = (s0, j)) ↔
        (s0 ∈ TT ∧ Odd j ∧ s = s0 + (j : ZMod d) ∧ (0 < j → l ^ j.toNat ≤ nu1 s0) ∧
          (j < 0 → l ^ (-j).toNat ≤ size s))) ∧
      (∀ s, J s + (if s ∈ TT then 1 else 0) ≤ N0) ∧ (∀ s i, (-(lab s i).2).toNat ≤ m)

def GaussPow : Prop :=
  ∀ (F K : Type) [NormedField F] [NormedField K] (φ : F →+* K) (σ : Type) (Y : σ → K),
    (∀ P : MvPolynomial σ F, ‖MvPolynomial.eval₂ φ Y P‖ = ⨆ n : σ →₀ ℕ, ‖MvPolynomial.coeff n P‖) →
    ∀ (k : σ → ℕ), (∀ y, k y ≠ 0) → ∀ (P : MvPolynomial σ F) (n : σ →₀ ℕ),
      ‖MvPolynomial.coeff n P‖ ≤ ‖MvPolynomial.eval₂ φ (fun y => Y y ^ k y) P‖

end Formalism.DworkPowerSeriesWeights
