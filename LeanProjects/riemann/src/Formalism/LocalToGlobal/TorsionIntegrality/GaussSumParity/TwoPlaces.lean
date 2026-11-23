import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.RelativeThetaFactorization

noncomputable section
open scoped BigOperators

namespace Formalism.L2.Th1.D

open Formalism.DworkPowerSeriesWeights (Integral mvExp entLog bSum idM ZV serAlong)
open Formalism.InvariantFactorPaths.G7 (Simeq UnrOK IsLawOfLog)
open MvPowerSeries

abbrev PV (ι : Type) (N0 N1 : ℕ) := Bool × ι × Fin N0 × Fin N1

def TwoPlaces : Prop :=
  ∀ (K0 K : Type) [NormedField K0] [IsUltrametricDist K0] [CharZero K0] [NormedField K]
    [IsUltrametricDist K] [CharZero K] (l d₁ d₂ N0 N1 : ℕ) [NeZero d₁] [NeZero d₂]
    (σ : K0 →+* K0) (j : K0 →+* K),
    UnrOK K0 l σ → (∀ a, ‖j a‖ = ‖a‖) → 2 ≤ d₁ → Even d₁ → 2 ≤ d₂ → Even d₂ →
    ∀ F : MvPowerSeries (Fin 2) K0, IsLawOfLog l F → ∀ be0 : MvPowerSeries (Fin 2) K0, F1 F be0 →
    F2 l σ be0 →
    ∀ (ι₁ ι₂ : Type) [Fintype ι₁] [DecidableEq ι₁] [Fintype ι₂] [DecidableEq ι₂]
      (om₁ oms₁ : ι₁ → K0) (om₂ oms₂ : ι₂ → K0),
      OwOK d₁ σ om₁ oms₁ → TrDual d₁ σ om₁ oms₁ → OwOK d₂ σ om₂ oms₂ → TrDual d₂ σ om₂ oms₂ →
    ∀ ζ₁ ζ₂ : K0, IsPrimitiveRoot ζ₁ (l ^ d₁ - 1) → IsPrimitiveRoot ζ₂ (l ^ d₂ - 1) →
    ∀ (U0 Φ : MvPowerSeries (PV ι₁ N0 N1 ⊕ PV ι₂ N0 N1) K), Integral U0 → constantCoeff Φ = 0 →
      Simeq Φ (serAlong Sum.inl (sumE (map j be0)) + serAlong Sum.inr (sumE (map j be0))) →
      ∃ U : MvPowerSeries (ZV d₁ N0 N1 ⊕ ZV d₂ N0 N1) K, Integral U ∧
        ∀ (g₁ : ZV d₁ N0 N1 → MvPowerSeries (ZV d₁ N0 N1) K)
          (g₂ : ZV d₂ N0 N1 → MvPowerSeries (ZV d₂ N0 N1) K),
          (∀ y, constantCoeff (g₁ y) = 0) → (∀ y, subst g₁ (entLog (K := K) l y) = X y) →
          (∀ y, constantCoeff (g₂ y) = 0) → (∀ y, subst g₂ (entLog (K := K) l y) = X y) →
          subst (Sum.elim (fun x => serAlong Sum.inl (xOfZ (d := d₁) l j σ om₁ oms₁ x))
              (fun x => serAlong Sum.inr (xOfZ (d := d₂) l j σ om₂ oms₂ x))) (mvExp (-Φ) * U0) =
            subst (Sum.elim (fun x => serAlong Sum.inl (g₁ x)) (fun x => serAlong Sum.inr (g₂ x))) U *
              (serAlong Sum.inl (mvExp (-(bSum (idM : ZV d₁ N0 N1 → ZV d₁ N0 N1 → K)
                  (map j (beMean l σ be0 om₁ oms₁ ζ₁))))) *
               serAlong Sum.inr (mvExp (-(bSum (idM : ZV d₂ N0 N1 → ZV d₂ N0 N1 → K)
                  (map j (beMean l σ be0 om₂ oms₂ ζ₂))))))

end Formalism.L2.Th1.D
