import Formalism.SharpRestriction.GrowthBounds.DiagonalSupport.TwiceValuationFactorialProduct

noncomputable section

open MvPolynomial Finset Classical

namespace Formalism.MainNotions.Proposition5Numerics

open Formalism.MainNotions.G

def ATL : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsPrincipalIdealRing O] (ι σ : Type) [Fintype ι] [Nonempty ι] (π : σ → ι)
    (X : ι → Submodule O (MvPolynomial σ O)),
    (∀ j, ∀ x ∈ X j, x ∈ supported O {v | π v = j}) →
    (∀ j, ∃ s : Finset (σ →₀ ℕ), ∀ x ∈ X j, x.support ⊆ s) →
    (∀ j (c : O) (x : MvPolynomial σ O), c ≠ 0 → c • x ∈ X j → x ∈ X j) →
    ∀ F : MvPolynomial σ O,
      (∀ j, F ∈ Submodule.span O {y | ∃ x ∈ X j, ∃ M ∈ supported O {v | π v ≠ j}, y = x * M}) →
      F ∈ Submodule.span O {y | ∃ x : ι → MvPolynomial σ O, (∀ j, x j ∈ X j) ∧ y = ∏ j, x j}

def ValSlice : Prop :=
  ∀ (R : Type) [CommRing R] [IsDomain R] (ι : Type) (n : ℕ) [NeZero n] (LL : Letters ι) (T : Set ι)
    (F : MvPolynomial (ι × Fin n) R),
    ∃ (s : Finset (ι × Fin n →₀ ℕ)) (c : (ι × Fin n →₀ ℕ) → MvPolynomial (ι × Fin n) R),
      (∀ M ∈ s, ∀ v ∈ M.support, v.1 ∉ T) ∧ (∀ M ∈ s, c M ∈ supported R {v : ι × Fin n | v.1 ∈ T}) ∧
      F = ∑ M ∈ s, c M * monomial M 1 ∧
      (∀ M ∈ s, ∀ mo ∈ (c M).support, mo + M ∈ F.support) ∧
      ∀ M ∈ s, ∀ S : Set ι, S ⊆ T → valS LL S F ≤ valS LL S (c M) ∧ lam1S LL S (c M) ≤ lam1S LL S F

def homComp {R : Type} [CommRing R] {ι : Type} {n : ℕ} (δ : ι → ℕ) (F : MvPolynomial (ι × Fin n) R) :
    MvPolynomial (ι × Fin n) R :=
  ∑ mo ∈ F.support.filter (fun mo => ∀ i, multideg mo i = δ i), monomial mo (F.coeff mo)

def ValComp : Prop :=
  ∀ (R : Type) [CommRing R] [IsDomain R] (ι : Type) (n : ℕ) [NeZero n] (LL : Letters ι) (S : Set ι)
    (F : MvPolynomial (ι × Fin n) R) (δ : ι → ℕ),
    valS LL S F ≤ valS LL S (homComp δ F) ∧ lam1S LL S (homComp δ F) ≤ lam1S LL S F

def ValRen : Prop :=
  ∀ (R : Type) [CommRing R] [IsDomain R] (ι κ : Type) (f : ι → κ) (n : ℕ) [NeZero n] (LL : Letters κ) (S : Set κ)
    (A : MvPolynomial (ι × Fin n) R),
    valS (⟨fun i => LL.vec (f i)⟩ : Letters ι) (f ⁻¹' S) A ≤ valS LL S (rename (fun v : ι × Fin n => (f v.1, v.2)) A) ∧
    lam1S LL S (rename (fun v : ι × Fin n => (f v.1, v.2)) A) ≤ lam1S (⟨fun i => LL.vec (f i)⟩ : Letters ι) (f ⁻¹' S) A

end Formalism.MainNotions.Proposition5Numerics
