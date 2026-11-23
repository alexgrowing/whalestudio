import Mathlib

set_option autoImplicit false

noncomputable section

open TensorProduct

namespace CrystallineSemistableComparison.D

structure Pf (p : ℕ) (A : Type) [CommRing A] : Prop where
  char : (p : A) = 0
  bij : Function.Bijective fun x : A => x ^ p

def IsRt (p : ℕ) {A : Type} [CommRing A] (r : ℕ → A) : Prop := ∀ k, r (k + 1) ^ p = r k

def Good (p : ℕ) {A : Type} [CommRing A] (r : ℕ → A) {K₁ K₀ : Type} [AddCommGroup K₁] [Module A K₁] [AddCommGroup K₀] [Module A K₀]
    (d : K₁ →ₗ[A] K₀) : Prop :=
  ∀ (C : Type) [CommRing C] [Algebra A C], Pf p C → ∀ w : C ⊗[A] K₁, d.lTensor C w = 0 →
    ∀ k, r k • w ∈ LinearMap.range ((LinearMap.ker d).subtype.lTensor C)

def Cov (p : ℕ) {A : Type} [CommRing A] (r : ℕ → A) (B : Type) [CommRing B] [Algebra A B] : Prop :=
  ∀ (K₁ K₀ : Type) [CommRing K₁] [Algebra A K₁] [CommRing K₀] [Algebra A K₀], Pf p K₁ → Pf p K₀ →
    ∀ d : K₁ →ₗ[A] K₀, Good p r d → ∀ z : K₀, ((1 : B) ⊗ₜ[A] z) ∈ LinearMap.range (d.lTensor B) →
      ∀ k, r k • z ∈ LinearMap.range d

def Solv {A : Type} [CommRing A] (B : Type) [CommRing B] [Algebra A B] {m n : ℕ} (a : Fin m → Fin n → A) (c : Fin m → A) : Prop :=
  ∃ y : Fin n → B, ∀ i, ∑ j, a i j • y j = algebraMap A B (c i)

structure PQ (p : ℕ) {S T : Type} [CommRing S] [CommRing T] (i : S →+* T) (I : Ideal S) : Prop where
  pf : Pf p T
  pow : ∀ y : T, ∃ (k : ℕ) (x : S), y ^ p ^ k = i x
  ker : ∀ x : S, i x = 0 ↔ ∃ k : ℕ, x ^ p ^ k ∈ I

def AICm {A B : Type} [CommRing A] [CommRing B] (φ : A →+* B) : Prop :=
  ∀ P : Polynomial A, P.Monic → 0 < P.natDegree → ∃ x, (P.map φ).IsRoot x

def VALm {A B : Type} [CommRing A] [CommRing B] (π : A) (φ : A →+* B) : Prop :=
  ∀ f g : A, (∃ N : ℕ, π ^ N ∈ Ideal.span {f, g}) →
    ∃ e : B, IsIdempotentElem e ∧ e * φ f ∈ Ideal.span {φ g} ∧ (1 - e) * φ g ∈ Ideal.span {φ f}

def AIC (A : Type) [CommRing A] : Prop := ∀ P : Polynomial A, P.Monic → 0 < P.natDegree → ∃ x, P.IsRoot x

def VAL {A : Type} [CommRing A] (π : A) : Prop :=
  ∀ f g : A, (∃ N : ℕ, π ^ N ∈ Ideal.span {f, g}) →
    ∃ e : A, IsIdempotentElem e ∧ e * f ∈ Ideal.span {g} ∧ (1 - e) * g ∈ Ideal.span {f}

def Splits (p : ℕ) {A B : Type} [CommRing A] [CommRing B] (π : A) (φ : A →+* B) : Prop :=
  ∀ (T : Type) [CommRing T] (x : A →+* T), Pf p T → AIC T → VAL (x π) → ∃ y : B →+* T, y.comp φ = x

structure IsCompl {B T : Type} [CommRing B] [CommRing T] (π : B) (g : B →+* T) : Prop where
  compl : IsAdicComplete (Ideal.span {g π}) T
  surj : ∀ (M : ℕ) (y : T), ∃ x, y - g x ∈ Ideal.span {g π ^ M}
  inj : ∀ (M : ℕ) (x : B), g x ∈ Ideal.span {g π ^ M} → x ∈ Ideal.span {π ^ M}

structure IsWP {A B K : Type} [CommRing A] [CommRing B] [CommRing K] [Algebra A B] [Algebra A K] {n : ℕ}
    (ι : Fin n → (B →ₐ[A] K)) : Prop where
  ex : ∀ (T : Type) [CommRing T] (x : A →+* T) (y : Fin n → (B →+* T)), (∀ i, (y i).comp (algebraMap A B) = x) →
    ∃ z : K →+* T, z.comp (algebraMap A K) = x ∧ ∀ i, z.comp (ι i : B →+* K) = y i
  uniq : ∀ (T : Type) [CommRing T] (z z' : K →+* T), z.comp (algebraMap A K) = z'.comp (algebraMap A K) →
    (∀ i, z.comp (ι i : B →+* K) = z'.comp (ι i : B →+* K)) → z = z'

def alt {A K K' : Type} [CommRing A] [CommRing K] [CommRing K'] [Algebra A K] [Algebra A K'] {n : ℕ}
    (δ : Fin (n + 1) → (K →ₐ[A] K')) : K →ₗ[A] K' := ∑ k : Fin (n + 1), (-1 : ℤ) ^ (k : ℕ) • (δ k).toLinearMap

def Pt {A B : Type} [CommRing A] [CommRing B] (φ : A →+* B) (E : Set (MvPolynomial (Fin 3) A)) : Prop :=
  ∃ y : Fin 3 → B, ∀ q ∈ E, MvPolynomial.eval₂ φ y q = 0

def tr {A : Type} [CommRing A] {G : ℕ → Type} [∀ n, CommRing (G n)] [∀ n, Algebra A (G n)] (f : ∀ n, G n →ₐ[A] G (n + 1)) (n : ℕ) :
    ∀ k, G n →ₐ[A] G (n + k)
  | 0 => AlgHom.id A (G n)
  | k + 1 => (f (n + k)).comp (tr f n k)

structure IsColim {A : Type} [CommRing A] {G : ℕ → Type} [∀ n, CommRing (G n)] [∀ n, Algebra A (G n)] (f : ∀ n, G n →ₐ[A] G (n + 1))
    {L : Type} [CommRing L] [Algebra A L] (ι : ∀ n, G n →ₐ[A] L) : Prop where
  comm : ∀ n x, ι (n + 1) (f n x) = ι n x
  surj : ∀ (m : ℕ) (x : Fin m → L), ∃ (n : ℕ) (y : Fin m → G n), ∀ i, ι n (y i) = x i
  ker : ∀ (n m : ℕ) (y : Fin m → G n), (∀ i, ι n (y i) = 0) → ∃ k, ∀ i, tr f n k (y i) = 0

end CrystallineSemistableComparison.D
