import Mathlib

noncomputable section

open NumberField

namespace PositivityTheory.KB.SplitAffineSpectral

def dc {Y : Type} {m : ℕ} (F : (Fin (m + 1) → Y) → ℝ) : (Fin (m + 2) → Y) → ℝ :=
  fun y => ∑ i : Fin (m + 2), (-1 : ℝ) ^ (i : ℕ) * F fun j => y (i.succAbove j)

def InvS {P : Type} [Group P] (S : Set P) {m : ℕ} (F : (Fin m → P) → ℝ) : Prop :=
  ∀ g ∈ S, ∀ y, F (fun j => g * y j) = F y

def mapOp {A : Type} (φ : A → A) (m : ℕ) : Module.End ℝ ((Fin m → A) → ℝ) where
  toFun c y := c fun i => φ (y i)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def ColPoly {P Q : Type} [Group P] [Group Q] (pr : P →* Q) (s : Q →* P) (u : Q) (m : ℕ) : Prop :=
  ∀ q : ℕ, q + 1 ≤ m → ∃ f : Polynomial ℝ, f.eval 1 ≠ 0 ∧
    ∀ c : (Fin (q + 2) → P) → ℝ, InvS (pr.ker : Set P) c → dc c = 0 →
      ∃ e : (Fin (q + 1) → P) → ℝ, InvS (pr.ker : Set P) e ∧
        Polynomial.aeval (mapOp (fun y => (s u)⁻¹ * y * s u) (q + 2)) f c = dc e

def Core : Prop :=
  ∀ (P Q : Type) [Group P] [Group Q] (pr : P →* Q) (s : Q →* P), (∀ g, pr (s g) = g) →
    ∀ u : Q, (∀ g, g * u = u * g) → ∀ m : ℕ, ColPoly pr s u m →
    ∀ j : ℕ, j + 1 ≤ m → ∀ c : (Fin (j + 2) → P) → ℝ, InvS Set.univ c → dc c = 0 →
      (∀ y : Fin (j + 2) → Q, c (fun i => s (y i)) = 0) →
      ∃ e : (Fin (j + 1) → P) → ℝ, InvS Set.univ e ∧ c = dc e

def APoly (A : Type) [Group A] (φ : A → A) (m : ℕ) : Prop :=
  ∀ q : ℕ, q + 1 ≤ m → ∃ f : Polynomial ℝ, f.eval 1 ≠ 0 ∧
    ∀ c : (Fin (q + 2) → A) → ℝ, InvS Set.univ c → dc c = 0 →
      ∃ e : (Fin (q + 1) → A) → ℝ, InvS Set.univ e ∧ Polynomial.aeval (mapOp φ (q + 2)) f c = dc e

def Transfer : Prop :=
  ∀ (P Q A : Type) [Group P] [Group Q] [Group A] (pr : P →* Q) (s : Q →* P), (∀ g, pr (s g) = g) →
    ∀ u : Q, (∀ g, g * u = u * g) → ∀ (ι : A →* P), Function.Injective ι → (∀ x, pr x = 1 ↔ x ∈ ι.range) →
    ∀ φ : A →* A, (∀ a, ι (φ a) = (s u)⁻¹ * ι a * s u) → ∀ m : ℕ, APoly A φ m → ColPoly pr s u m

def cupH {A : Type} [Group A] {q : ℕ} (α : Fin q → (Additive A →+ ℝ)) (y : Fin (q + 1) → A) : ℝ :=
  ∏ i : Fin q, α i (Additive.ofMul ((y i.castSucc)⁻¹ * y i.succ))

def Span : Prop :=
  ∀ (A : Type) [CommGroup A] [Module.Free ℤ (Additive A)] [Module.Finite ℤ (Additive A)] (q : ℕ)
    (c : (Fin (q + 2) → A) → ℝ), InvS Set.univ c → dc c = 0 →
      ∃ (k : ℕ) (a : Fin k → ℝ) (α : Fin k → Fin (q + 1) → (Additive A →+ ℝ))
        (e : (Fin (q + 1) → A) → ℝ), InvS Set.univ e ∧ c = (∑ i, a i • cupH (α i)) + dc e

def Unit : Prop :=
  ∀ (L : Type) [Field L] [NumberField L], IsTotallyComplex L → ∀ m : ℕ, m < InfinitePlace.nrComplexPlaces L →
    ∃ v : (𝓞 L)ˣ, ∀ a : InfinitePlace L → ℕ, 0 < ∑ w, a w → ∑ w, a w ≤ m →
      ∏ w, (w (v : L)) ^ a w ≠ 1

def mulV {L : Type} [Field L] [NumberField L] (n r : ℕ) (v : 𝓞 L) :
    Multiplicative (Matrix (Fin n) (Fin r) (𝓞 L)) → Multiplicative (Matrix (Fin n) (Fin r) (𝓞 L)) :=
  fun B => Multiplicative.ofAdd (v • Multiplicative.toAdd B)

def Eigen : Prop :=
  ∀ (L : Type) [Field L] [NumberField L], IsTotallyComplex L → ∀ (m : ℕ) (v : (𝓞 L)ˣ),
    (∀ a : InfinitePlace L → ℕ, 0 < ∑ w, a w → ∑ w, a w ≤ m → ∏ w, (w (v : L)) ^ a w ≠ 1) →
    ∀ n r q : ℕ, q + 1 ≤ m → ∃ f : Polynomial ℝ, f.eval 1 ≠ 0 ∧
      ∀ α : Fin (q + 1) → (Additive (Multiplicative (Matrix (Fin n) (Fin r) (𝓞 L))) →+ ℝ),
        Polynomial.aeval (mapOp (mulV n r (v : 𝓞 L)) (q + 2)) f (cupH α) = 0

end PositivityTheory.KB.SplitAffineSpectral

end
