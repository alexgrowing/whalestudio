import Mathlib

set_option autoImplicit false

noncomputable section

namespace CrystallineSemistableComparison.Onto

variable (K : Type) [CommRing K] {A B : Type} [CommRing A] [CommRing B] [Algebra K A] [Algebra K B]

variable (A) in

abbrev Om (a : ℕ) : Type := ⋀[A]^a Ω[A⁄K]

def form {a : ℕ} (g₀ : A) (g : Fin a → A) : Om K A a :=
  g₀ • exteriorPower.ιMulti A a fun k => KaehlerDifferential.D K A (g k)

variable {K}

def omMap (φ : A →ₐ[K] B) (a : ℕ) : Om K A a →ₗ[K] Om K B a :=
  letI : Algebra A B := φ.toRingHom.toAlgebra
  haveI : IsScalarTower K A B := IsScalarTower.of_algHom φ
  (exteriorPower.alternatingMapLinearEquiv
    { ((exteriorPower.ιMulti B a (M := Ω[B⁄K])).toMultilinearMap.restrictScalars A).compLinearMap
        fun _ => KaehlerDifferential.map K K A B with
      map_eq_zero_of_eq' := fun v i j h hij =>
        (exteriorPower.ιMulti B a (M := Ω[B⁄K])).map_eq_zero_of_eq (fun k => KaehlerDifferential.map K K A B (v k))
          (congrArg _ h) hij } : Om K A a →ₗ[A] Om K B a).restrictScalars K

variable (K) in

def relOm (I : Ideal A) (a : ℕ) : Submodule A (Om K A a) :=
  Submodule.span A {ω | ∃ (g₀ : A) (g : Fin a → A), (g₀ ∈ I ∨ ∃ k, g k ∈ I) ∧ ω = form K g₀ g}

def FormLaws : Prop := ∀ (K A B : Type) [CommRing K] [CommRing A] [CommRing B] [Algebra K A] [Algebra K B] (a : ℕ),
  Submodule.span K {ω : Om K A a | ∃ g₀ g, ω = form K g₀ g} = ⊤ ∧
  ∀ φ : A →ₐ[K] B, (∀ g₀ (g : Fin a → A), omMap φ a (form K g₀ g) = form K (φ g₀) fun k => φ (g k)) ∧
    (∀ (c : A) ω, omMap φ a (c • ω) = φ c • omMap φ a ω) ∧
    (Function.Surjective φ → Function.Surjective (omMap φ a) ∧ ∀ ω, omMap φ a ω = 0 ↔ ω ∈ relOm K (RingHom.ker φ) a)

def DWedge : Prop := ∀ (K A : Type) [CommRing K] [CommRing A] [Algebra K A] (a : ℕ) (f : A),
  ∃ w : Om K A a →ₗ[A] Om K A (a + 1), ∀ g₀ (g : Fin a → A), w (form K g₀ g) = form K g₀ (Fin.cons f g)

def DLog : Prop := ∀ (K A : Type) [CommRing K] [CommRing A] [Algebra K A] (a : ℕ) (f : A),
  (∀ ω : Om K A (a + 1), f • ω = 0 → ω = 0) → ∀ w : Om K A a →ₗ[A] Om K A (a + 1),
  (∀ g₀ (g : Fin a → A), w (form K g₀ g) = form K g₀ (Fin.cons f g)) →
  ∀ ω ∈ relOm K (Ideal.span {f}) a, ∃! η, η ∈ relOm K (Ideal.span {f}) (a + 1) ∧ f • η = w ω

def OmKun : Prop := ∀ (K A B : Type) [Field K] [CommRing A] [CommRing B] [Algebra K A] [Algebra K B] (c : ℕ),
  ∃ e : (∀ a : Fin (c + 1), TensorProduct K (Om K A a) (Om K B (c - a))) ≃ₗ[K] Om K (TensorProduct K A B) c,
    ∀ (a : Fin (c + 1)) (g₀ : A) (g : Fin a → A) (h₀ : B) (h : Fin (c - a) → B),
      e (Pi.single a (form K g₀ g ⊗ₜ form K h₀ h)) = form K (g₀ ⊗ₜ h₀)
        (Fin.append (fun k => g k ⊗ₜ (1 : B)) (fun k => (1 : A) ⊗ₜ h k) ∘ Fin.cast (by have := a.2; omega))

end CrystallineSemistableComparison.Onto

end
