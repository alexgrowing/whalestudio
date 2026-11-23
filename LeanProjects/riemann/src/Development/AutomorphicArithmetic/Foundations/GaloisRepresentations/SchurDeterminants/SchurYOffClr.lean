import Mathlib
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.JacobiTrudi

noncomputable section

open Finset MvPolynomial

namespace UpperTheory.Gal.Schur

def sch {R : Type} [CommRing R] [Algebra ℚ R] {n : ℕ} (lam : Fin n → ℕ) (g : Fin n → R) : R :=
  aeval g (GroundTheory.Heights₂.Heights.RestTerms.schur (Fin n) lam)

def vdm {R : Type} [CommRing R] {n : ℕ} (g : Fin n → R) : R :=
  ∏ i : Fin n, ∏ j ∈ Finset.Ioi i, (g i - g j)

def altn {R : Type} [CommRing R] {n : ℕ} (e : Fin n → ℕ) (g : Fin n → R) : R :=
  (Matrix.of fun i j : Fin n => g j ^ e i).det

def altnZ {K : Type} [Field K] {n : ℕ} (e : Fin n → ℤ) (g : Fin n → K) : K :=
  (Matrix.of fun i j : Fin n => g j ^ e i).det

def shift {n : ℕ} (lam : Fin n → ℕ) : Fin n → ℕ := fun i => lam i + (n - 1 - (i : ℕ))

def scaleAt {R : Type} [CommRing R] {n : ℕ} (y : R) (i : Fin n) (g : Fin n → R) : Fin n → R :=
  fun k => if k = i then y * g k else g k

def scaleOff {R : Type} [CommRing R] {n : ℕ} (y : R) (i : Fin n) (g : Fin n → R) : Fin n → R :=
  fun k => if k = i then g k else y * g k

def detOne {R : Type} [CommRing R] {n : ℕ} (x : R) (g : Fin n → R) : R := ∏ j, (1 - x * g j)

def ZDense {K σ : Type} [CommRing K] (D : Set (σ → K)) : Prop :=
  ∀ Q : MvPolynomial σ K, (∀ a ∈ D, eval a Q = 0) → Q = 0

def pt {O K ι : Type} [CommRing O] [CommRing K] (τ : ι → (O →+* K)) {k : ℕ} (α : Fin k → O) :
    ι × Fin k → K := fun p => τ p.1 (α p.2)

def Comparison₂ : Prop :=
  ∀ (R : Type) [CommRing R] [Algebra ℚ R] (n : ℕ) (lam : Fin n → ℕ) (g : Fin n → R),
    sch lam g * vdm g = altn (shift lam) g

def SchurYClr : Prop :=
  ∀ (R : Type) [CommRing R] [Algebra ℚ R] (n : ℕ) (lam : Fin n → ℕ) (g : Fin n → R) (y : R),
    ∑ i, sch lam (scaleAt y i g) * vdm (scaleAt y i g) =
      sch lam g * vdm g * ∑ i : Fin n, y ^ (lam i + (n - 1 - (i : ℕ)))

def SchurY : Prop :=
  ∀ (R : Type) [CommRing R] [Algebra ℚ R] (n : ℕ) (lam : Fin n → ℕ) (g : Fin n → R) (y : R),
    (∀ i k, k ≠ i → IsUnit (g k - g i)) →
    ∑ i, sch lam (scaleAt y i g) * ∏ k ∈ univ.erase i, ((g k - y * g i) * Ring.inverse (g k - g i)) =
      sch lam g * ∑ i : Fin n, y ^ (lam i + (n - 1 - (i : ℕ)))

def SchurYOffClr : Prop :=
  ∀ (R : Type) [CommRing R] [Algebra ℚ R] (n : ℕ) (lam : Fin n → ℕ) (g : Fin n → R) (y : R),
    ∑ i, sch lam (scaleOff y i g) * vdm (scaleOff y i g) =
      sch lam g * vdm g * ∑ i : Fin n, y ^ (∑ k ∈ univ.erase i, (lam k + (n - 1 - (k : ℕ))))

def SchurYOff : Prop :=
  ∀ (R : Type) [CommRing R] [Algebra ℚ R] (n : ℕ) (lam : Fin n → ℕ) (g : Fin n → R) (y : R),
    (∀ i k, k ≠ i → IsUnit (g k - g i)) →
    ∑ i, sch lam (scaleOff y i g) * ∏ k ∈ univ.erase i, ((g i - y * g k) * Ring.inverse (g i - g k)) =
      sch lam g * ∑ i : Fin n, y ^ (∑ k ∈ univ.erase i, lam k + (i : ℕ))

def SchurYField : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (n : ℕ) (lam : Fin n → ℕ) (g : Fin n → K) (y : K),
    Function.Injective g →
    (∑ i, sch lam (scaleAt y i g) * ∏ k ∈ univ.erase i, (g k - y * g i) / (g k - g i) =
      sch lam g * ∑ i : Fin n, y ^ (lam i + (n - 1 - (i : ℕ)))) ∧
    (∑ i, sch lam (scaleOff y i g) * ∏ k ∈ univ.erase i, (g i - y * g k) / (g i - g k) =
      sch lam g * ∑ i : Fin n, y ^ (∑ k ∈ univ.erase i, lam k + (i : ℕ)))

def SchurHomog : Prop :=
  ∀ (R : Type) [CommRing R] [Algebra ℚ R] (n : ℕ) (lam : Fin n → ℕ) (g : Fin n → R) (y : R),
    sch lam (fun k => y * g k) = y ^ (∑ k, lam k) * sch lam g

def SchurDet : Prop :=
  ∀ (R : Type) [CommRing R] [Algebra ℚ R] (n : ℕ) (g : Fin n → R),
    sch (fun _ => 0) g = 1 ∧
    ∀ (lam : Fin n → ℕ) (m : ℕ), sch (fun i => lam i + m) g = (∏ k, g k) ^ m * sch lam g

def WeylTie : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (n : ℕ) (l : Fin n → ℤ) (m : ℕ) (lam : Fin n → ℕ) (g : Fin n → K),
    (∀ i, l i + m = lam i) → Function.Injective g → (∀ i, g i ≠ 0) →
    altnZ (fun i => l i + n - 1 - (i : ℕ)) g / vdm g = sch lam g / (∏ k, g k) ^ m

def SpanE : Prop :=
  ∀ (K : Type) [CommRing K] (n : ℕ) (P : MvPolynomial (Fin n) K), P.IsSymmetric →
    ∃ k₀, ∀ k, k₀ ≤ k → ∃ w : (Fin k → Fin (n + 1)) → K,
      P = ∑ m, w m • ∏ s, esymm (Fin n) K (m s)

def Extract : Prop :=
  ∀ (K σ A M : Type) [Field K] [Fintype σ] [Fintype M] (x : A → σ → K), ZDense (Set.range x) →
    ∀ e : M → σ → ℕ, Function.Injective e → ∀ w : M → K,
      ∃ c : A →₀ K, ∀ m, (c.sum fun a r => r * ∏ p, x a p ^ e m p) = w m

def DenseCoset : Prop :=
  ∀ (O K ι : Type) [CommRing O] [Field K] [CharZero K] [Fintype ι] (τ : ι → (O →+* K)),
    Function.Injective τ → ∀ (N : O), (∀ t, τ t N ≠ 0) → ∀ (k : ℕ) (a : Fin k → O)
      (Q : MvPolynomial (ι × Fin k) K), Q ≠ 0 →
      ZDense {x | ∃ α : Fin k → O, (∀ s, N ∣ α s - a s) ∧ eval (pt τ α) Q ≠ 0 ∧ x = pt τ α}

def Interp : Prop :=
  ∀ (O K ι : Type) [CommRing O] [Field K] [CharZero K] [Fintype ι] (τ : ι → (O →+* K)),
    Function.Injective τ → ∀ (n : ℕ) (P : ι → MvPolynomial (Fin n) K), (∀ t, (P t).IsSymmetric) →
    ∃ k₀, ∀ k, k₀ ≤ k → ∀ (N : O), (∀ t, τ t N ≠ 0) → ∀ (a : Fin k → O)
      (Q : MvPolynomial (ι × Fin k) K), Q ≠ 0 →
      ∃ c : (Fin k → O) →₀ K,
        (∀ α ∈ c.support, (∀ s, N ∣ α s - a s) ∧ eval (pt τ α) Q ≠ 0) ∧
        ∀ (R : Type) [CommRing R] [Algebra K R] (g : ι → Fin n → R),
          (c.sum fun α r => r • ∏ t, ∏ s, detOne (algebraMap K R (τ t (α s))) (g t)) =
            ∏ t, aeval (g t) (P t)

def resO {E K : Type} [Field E] [Field K] (τ : E →+* K) : NumberField.RingOfIntegers E →+* K :=
  τ.comp (algebraMap (NumberField.RingOfIntegers E) E)

def InterpNF : Prop :=
  ∀ (E K : Type) [Field E] [NumberField E] [Field K] [CharZero K] (n : ℕ)
    (lam : (E →+* K) → Fin n → ℕ), ∃ k₀, ∀ k, k₀ ≤ k →
    ∀ (N : NumberField.RingOfIntegers E), N ≠ 0 → ∀ B : Finset K,
      ∃ c : (Fin k → NumberField.RingOfIntegers E) →₀ K,
        (∀ α ∈ c.support, ∀ s, α s ≠ 0 ∧ N ∣ α s ∧ ∀ τ : E →+* K, ∀ b ∈ B, 1 - resO τ (α s) * b ≠ 0) ∧
        ∀ (R : Type) [CommRing R] [Algebra K R] [Algebra ℚ R] (g : (E →+* K) → Fin n → R),
          (c.sum fun α r => r • ∏ τ, ∏ s, detOne (algebraMap K R (resO τ (α s))) (g τ)) =
            ∏ τ, sch (lam τ) (g τ)

def twist {R ι : Type} [CommRing R] [DecidableEq ι] {n : ℕ} (t₀ t₁ : ι) (ε : ι → ℕ) (y : R) (i : Fin n)
    (g : ι → Fin n → R) : ι → Fin n → R := fun t =>
  if t = t₀ then scaleAt y i (g t) else if t = t₁ then scaleOff y i (g t) else fun k => y ^ ε t * g t k

def Fibre : Prop :=
  ∀ (R ι : Type) [CommRing R] [Algebra ℚ R] [Fintype ι] [DecidableEq ι] (n : ℕ) (t₀ t₁ : ι), t₀ ≠ t₁ →
    ∀ (ε : ι → ℕ) (lam : ι → Fin n → ℕ) (m : ℕ), (∀ i, lam t₁ i = m) → ∀ (g : ι → Fin n → R) (y : R),
    (∀ i k, k ≠ i → IsUnit (g t₀ k - g t₀ i)) →
    ∑ i, (∏ t, sch (lam t) (twist t₀ t₁ ε y i g t)) *
        ∏ k ∈ univ.erase i, ((g t₀ k - y * g t₀ i) * Ring.inverse (g t₀ k - g t₀ i)) =
      (∏ t, sch (lam t) (g t)) *
        (y ^ ((n - 1) * m + ∑ t ∈ (univ.erase t₀).erase t₁, ε t * ∑ i, lam t i) *
          ∑ i : Fin n, y ^ (lam t₀ i + (n - 1 - (i : ℕ))))

def FibreOff : Prop :=
  ∀ (R ι : Type) [CommRing R] [Algebra ℚ R] [Fintype ι] [DecidableEq ι] (n : ℕ) (t₀ t₁ : ι), t₀ ≠ t₁ →
    ∀ (ε : ι → ℕ) (lam : ι → Fin n → ℕ) (m : ℕ), (∀ i, lam t₀ i = m) → ∀ (g : ι → Fin n → R) (y : R),
    (∀ i k, k ≠ i → IsUnit (g t₁ k - g t₁ i)) →
    ∑ i, (∏ t, sch (lam t) (twist t₀ t₁ ε y i g t)) *
        ∏ k ∈ univ.erase i, ((g t₁ i - y * g t₁ k) * Ring.inverse (g t₁ i - g t₁ k)) =
      (∏ t, sch (lam t) (g t)) *
        (y ^ (m + ∑ t ∈ (univ.erase t₀).erase t₁, ε t * ∑ i, lam t i) *
          ∑ i : Fin n, y ^ (∑ k ∈ univ.erase i, lam t₁ k + (i : ℕ)))

end UpperTheory.Gal.Schur
