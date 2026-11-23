import Formalism.LocalToGlobal.TorsionIntegrality.SecondCoefficientNorms.IsotropicVanish

noncomputable section
open scoped BigOperators

namespace Formalism.L2.Th1.C

def GramFormula : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (R : Subring K) (l linv ph : PowerSeries K),
    Frame R l linv ph →
    ∀ (O : Type) [CommRing O] [StarRing O] (τ : O →+* K),
    (∀ α, EndInt R l linv (τ α)) →
    (∀ z : O, star z = z → IsBinomScalar R (τ z)) →
    F1 R l linv ph →
    (∀ α : O, PhNormAt R l linv ph (τ α) (τ (star α))) →
    (∀ α : O, AdjAt R l linv ph (τ α) (τ (star α))) →
    ∀ (n : Type) [Fintype n] (k : ℕ) (A : n → Fin k → O)
      (σ : Type) (u : Fin k → MvPowerSeries σ K), (∀ j, IsPt R (u j)) →
      Cong R (∑ i, PowerSeries.subst (flin l linv (fun j => τ (A i j)) u) ph)
        ((∑ j, τ (∑ i, star (A i j) * A i j) • PowerSeries.subst (u j) ph) +
          ∑ j, ∑ j' ∈ Finset.univ.filter (fun j' => j < j'),
            be0 l linv ph (fmul l linv (τ (∑ i, star (A i j') * A i j)) (u j)) (u j'))

def TraceDiag : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (R : Subring K) (l linv ph : PowerSeries K),
    Frame R l linv ph →
    ∀ (O : Type) [CommRing O] [StarRing O] (τ : O →+* K),
    (∀ α, EndInt R l linv (τ α)) →
    (∀ z : O, star z = z → IsBinomScalar R (τ z)) →
    (∀ z : O, star z = z → ZLinAt R l linv ph (τ z)) →
    F1 R l linv ph → (2 : K)⁻¹ ∈ R →
    PhNormAt R l linv ph 2 2 →
    ∀ γ : O, AdjAt R l linv ph (τ (star γ)) (τ γ) →
    ∀ (σ : Type) (u : MvPowerSeries σ K), IsPt R u →
      Cong R (be0 l linv ph u (fmul l linv (τ γ) u)) (τ (star γ + γ) • PowerSeries.subst u ph)

def DiagTwoPh : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (R : Subring K) (l linv ph : PowerSeries K),
    Frame R l linv ph → PhNormAt R l linv ph 2 2 →
    ∀ (σ : Type) (u : MvPowerSeries σ K), IsPt R u →
      Cong R (be0 l linv ph u u) ((2 : K) • PowerSeries.subst u ph)

def PhRational : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (K0 : Subfield K) (e l ph : PowerSeries K) (s2 : K),
    PowerSeries.constantCoeff l = 0 → PowerSeries.coeff 1 l = 1 → IsPh e s2 l ph →
    (∀ n, PowerSeries.coeff n e ∈ K0) → (∀ n, PowerSeries.coeff n l ∈ K0) → s2 ∈ K0 →
    ∀ n, PowerSeries.coeff n ph ∈ K0

def PhUnique : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (e l ph ph' : PowerSeries K) (s2 : K),
    IsPh e s2 l ph → IsPh e s2 l ph' → ph = ph'

end Formalism.L2.Th1.C
