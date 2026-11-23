import Formalism.LocalToGlobal.TorsionIntegrality.SecondCoefficientNorms.IsotropicVanish

noncomputable section
open scoped BigOperators

namespace Formalism.L2.Th1.C

def EndIntClosed : Prop :=
  ∀ (K : Type) [Field K] [TopologicalSpace K] [IsTopologicalRing K] (R : Subring K),
    IsClosed (R : Set K) → ∀ l linv : PowerSeries K, PowerSeries.constantCoeff l = 0 →
      IsClosed {a : K | EndInt R l linv a}

def BinomClosed : Prop :=
  ∀ (K : Type) [Field K] [TopologicalSpace K] [IsTopologicalRing K] (R : Subring K),
    IsClosed (R : Set K) → IsClosed {z : K | IsBinomScalar R z}

def PhNormClosed : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] [TopologicalSpace K] [IsTopologicalRing K] (R : Subring K),
    IsClosed (R : Set K) → ∀ l linv ph : PowerSeries K, PowerSeries.constantCoeff l = 0 →
      PowerSeries.constantCoeff linv = 0 → PowerSeries.constantCoeff ph = 0 →
      IsClosed {p : K × K | PhNormAt R l linv ph p.1 p.2}

def ZLinClosed : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] [TopologicalSpace K] [IsTopologicalRing K] (R : Subring K),
    IsClosed (R : Set K) → ∀ l linv ph : PowerSeries K, PowerSeries.constantCoeff l = 0 →
      PowerSeries.constantCoeff linv = 0 → PowerSeries.constantCoeff ph = 0 →
      IsClosed {z : K | ZLinAt R l linv ph z}

def ZLinInt : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (R : Subring K) (l linv ph : PowerSeries K),
    Frame R l linv ph → F1 R l linv ph → ∀ n : ℤ, ZLinAt R l linv ph (n : K)

def EndoAll : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] [TopologicalSpace K] [IsTopologicalRing K] (R : Subring K),
    IsClosed (R : Set K) → ∀ l linv ph : PowerSeries K, Frame R l linv ph → F1 R l linv ph →
    ∀ (O : Type) [CommRing O] [StarRing O] [TopologicalSpace O] (τ : O →+* K),
    Continuous τ → Continuous (star : O → O) →
    (∀ z : O, star z = z → τ z ∈ closure (Set.range (fun n : ℤ => (n : K)))) →
    (2 : K)⁻¹ ∈ R → IsUnit (2 : O) → (∀ α : O, ∃ u v : Oˣ, α = u + v) →
    ∀ Dn : Set O, (∀ α : Oˣ, (α : O) ∈ closure Dn) →
    (∀ α ∈ Dn, EndInt R l linv (τ α) ∧ PhNormAt R l linv ph (τ α) (τ (star α))) →
    ∀ α : O, EndInt R l linv (τ α) ∧ PhNormAt R l linv ph (τ α) (τ (star α)) ∧
      AdjAt R l linv ph (τ α) (τ (star α))

end Formalism.L2.Th1.C
