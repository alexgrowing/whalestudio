import Mathlib
import Formalism.FrobeniusContraction.HighestWeightResidueAvoids

noncomputable section

open Classical

namespace Formalism.TruncatedSeriesCounting.tableLineDegreeTwo

open Formalism.WachCohomologyFacts

def LowN (G : Bool) (h η : ℕ) (U : Multiset ℤ) : Multiset ℤ := U.filter (V2.InWinN G h η)

def WindowSmall (ℓ η : ℕ) (σ : ℤ) : Prop := (η : ℤ) + 4 * σ + 6 < ℓ

def WindowSeparated (G : Bool) (h η w t : ℕ) (σ : ℤ) (U : Multiset ℤ) : Prop :=
  ∀ x ∈ LowN G h η U, ∀ y ∈ Top.GlobalTheory w t, σ + 2 < |x - y|

def Slot (ℓ : ℕ) (G : Bool) (h η w t : ℕ) (σ : ℤ) (U : Multiset ℤ) : Prop :=
  0 ≤ σ ∧ 1 ≤ t ∧ (∀ x ∈ U, 1 ≤ x ∧ x ≤ (h : ℤ) - 1) ∧ w + t ≤ h ∧
    1 ≤ w ∧ (G = true → w + t - 1 ≤ η) ∧ (G = false → (h : ℤ) - η ≤ w) ∧
    WindowSmall ℓ η σ ∧ WindowSeparated G h η w t σ U ∧ V2.ResidueAvoidance ℓ G h η σ U

def Residues : Prop :=
  ∀ (ℓ : ℕ) (G : Bool) (h η w t : ℕ) (σ : ℤ) (U : Multiset ℤ), Slot ℓ G h η w t σ U →
    (∀ x ∈ U, ∀ e : ℤ, -σ - 1 ≤ e → e ≤ (t : ℤ) + σ →
      ((x : ℤ) : ZMod ℓ) ≠ (((w : ℤ) + e : ℤ) : ZMod ℓ)) ∧
    (G = false → ∀ u : ℤ, (u ∈ U ∨ u ∈ Top.GlobalTheory w t) → ∀ a : ℤ, 0 ≤ a → a ≤ (h : ℤ) - w →
      ((u - w - a : ℤ) : ZMod ℓ) = 0 → u - w - a = 0) ∧
    (G = true → ∀ x ∈ U, ∀ e : ℤ, 1 ≤ e → e ≤ σ → ((x + e : ℤ) : ZMod ℓ) ≠ 0) ∧
    (G = false → ∀ u : ℤ, (u ∈ U ∨ u ∈ Top.GlobalTheory w t) → ∀ e : ℤ, 1 ≤ e → e ≤ σ + 1 →
      ((u : ℤ) : ZMod ℓ) ≠ (((h : ℤ) + e : ℤ) : ZMod ℓ))

def resCount (ℓ : ℕ) (U : Multiset ℤ) (x : ZMod ℓ) : ℕ := U.countP (fun u => ((u : ℤ) : ZMod ℓ) = x)

def CountG : Prop :=
  ∀ (ℓ : ℕ) (h η w t : ℕ) (σ : ℤ) (U : Multiset ℤ), Slot ℓ true h η w t σ U →
    ∀ (S m : ZMod ℓ → ℕ),
      (∀ x, S x + m (x + 1) = resCount ℓ U x + m x) →
      (∀ x, m x ≠ 0 → ∃ u ∈ U, ∃ e : ℤ, 1 ≤ e ∧ e ≤ σ ∧ x = ((u + e : ℤ) : ZMod ℓ)) →
      ∑ n ∈ Finset.range w, S (n : ZMod ℓ) = U.countP (fun u => u < (w : ℤ))

def CountBd : Prop :=
  ∀ (ℓ : ℕ) (h η w t : ℕ) (σ : ℤ) (U : Multiset ℤ), Slot ℓ false h η w t σ U →
    ∀ (S m : ZMod ℓ → ℕ),
      (∀ x, S x + m (x + 1) = resCount ℓ U x + m x) →
      (∀ x, m x ≠ 0 → ∃ u ∈ U, ∃ e : ℤ, 1 ≤ e ∧ e ≤ σ ∧ x = ((u + e : ℤ) : ZMod ℓ)) →
      (∀ x, S x ≠ 0 → ∃ u : ℤ, (u ∈ U ∨ u ∈ Top.GlobalTheory w t) ∧ x = ((u : ℤ) : ZMod ℓ)) →
      ∑ n ∈ Finset.Icc (w : ℤ) (h : ℤ), S ((n : ℤ) : ZMod ℓ) =
        Multiset.card U - U.countP (fun u => u < (w : ℤ))

def KerCount : Prop :=
  ∀ (ℓ w : ℕ) (S : Multiset (ZMod ℓ)), 1 ≤ w → w < ℓ →
    Multiset.card ((S ×ˢ (Finset.Icc 1 w).val).filter
        (fun p : ZMod ℓ × ℕ => p.1 - (w : ZMod ℓ) + (p.2 : ZMod ℓ) = 0)) =
      S.countP (fun s => ∃ n < w, s = (n : ZMod ℓ))

def KerGr : Prop :=
  ∀ (k V : Type) [Field k] [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (f : V →ₗ[k] V) (m : ℕ) (F : ℕ → Submodule k V),
    F 0 = ⊥ → F m = ⊤ → (∀ i, F i ≤ F (i + 1)) → (∀ i, ∀ x ∈ F i, f x ∈ F i) →
    Module.finrank k (LinearMap.ker f) ≤
      ∑ i ∈ Finset.range m,
        (Module.finrank k ↥(F (i + 1) ⊓ (F i).comap f) - Module.finrank k ↥(F i))

def KerEig : Prop :=
  ∀ (k V : Type) [Field k] [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (g : V →ₗ[k] V),
    Module.finrank k (LinearMap.ker g) ≤ (LinearMap.charpoly g).rootMultiplicity 0

def Close : Prop :=
  (∀ (k V : Type) [Field k] [AddCommGroup V] [Module k V] [FiniteDimensional k V]
      (KK L N : Submodule k V) (r d : ℕ),
      L ≤ KK ⊓ N → Module.finrank k KK - Module.finrank k L ≤ r →
      Module.finrank k ↥(KK ⊓ N) - Module.finrank k L = r - d → d ≤ r →
      Module.finrank k KK - Module.finrank k ↥(KK ⊓ N) ≤ d) ∧
  (∀ (k V : Type) [Field k] [AddCommGroup V] [Module k V] [FiniteDimensional k V]
      (Hf adm : Submodule k V), Hf ≤ adm → Module.finrank k adm ≤ Module.finrank k Hf →
      adm = Hf)

def DepthSteps : Prop :=
  ∀ (f : ℕ) [NeZero f] (ℓ : ℕ) (h w : ZMod f → ℕ), 2 ≤ ℓ → ∀ i : ZMod f,
    V2.sgN f ℓ h i + 2 * ℓ < (ℓ : ℤ) * (V2.sgN f ℓ h (i - 1) + 3) - h i ∧
    (w i ≤ h i → ((h i : ℤ) - w i) + 2 < (ℓ : ℤ) * (V2.sgN f ℓ h (i - 1) + 3) - w i) ∧
    ∀ s : ℕ, V2.sgN f ℓ h i + 1 + ℓ * s ≤ (ℓ : ℤ) * (V2.sgN f ℓ h (i - 1) + 1 + s) - h i

def PsiPow : Prop :=
  ∀ (k : Type) [Field k] (ℓ : ℕ) [CharP k ℓ] (hℓ : ℓ.Prime)
    (ψ : PowerSeries k →+ PowerSeries k),
    (∀ a x : PowerSeries k, ψ (PowerSeries.expand ℓ hℓ.ne_zero a * x) = a * ψ x) →
    (∀ j < ℓ, ψ ((1 + PowerSeries.X) ^ j) = if j = 0 then 1 else 0) →
    (∀ j < ℓ, ψ (PowerSeries.X ^ j) = (-1) ^ j) ∧
    ∀ s : ℕ, ψ '' {x | PowerSeries.X ^ s ∣ x} = {y | PowerSeries.X ^ (s / ℓ) ∣ y}

def PsiExists : Prop :=
  ∀ (k : Type) [Field k] (ℓ : ℕ) [CharP k ℓ] (hℓ : ℓ.Prime),
    ∃ ψ : PowerSeries k →+ PowerSeries k,
      (∀ a x : PowerSeries k, ψ (PowerSeries.expand ℓ hℓ.ne_zero a * x) = a * ψ x) ∧
      (∀ j < ℓ, ψ ((1 + PowerSeries.X) ^ j) = if j = 0 then 1 else 0)

end Formalism.TruncatedSeriesCounting.tableLineDegreeTwo
