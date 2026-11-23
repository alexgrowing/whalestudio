import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.PrimitiveCrystalHodgeLiftClasses
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianLifting

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry DividedPowers
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham

namespace PositivityTheory.JLift

variable {R : Type} [CommRing R] {I : Ideal R} {X₀ : Scheme.{0}}

structure Pt (κ : DividedPowers I) (s₀ : X₀ ⟶ Sp R) (X : Over (Sp R)) (i : X₀ ⟶ X.left) : Type 1 where

  T : Thick κ s₀

  y : Sp T.B ⟶ X.left
  w : y ≫ X.hom = spMap (algebraMap R T.B)
  red : spMap T.π ≫ y = T.x ≫ i

variable {κ : DividedPowers I} {s₀ : X₀ ⟶ Sp R} {X : Over (Sp R)} {i : X₀ ⟶ X.left}

def Pt.IsChart (a : Pt κ s₀ X i) : Prop :=
  a.T.J = I.map (algebraMap R a.T.B) ∧ IsOpenImmersion a.y

def TrivBy (z : Z1 (O κ s₀)) (t : ∀ a : Pt κ s₀ X i, a.T.B) : Prop :=
  ∀ (a b : Pt κ s₀ X i) (φ : a.T ⟶ b.T), spMap (φ.φ : a.T.B →+* b.T.B) ≫ a.y = b.y → ev z φ = t b - φ.φ (t a)

def Triv (X : Over (Sp R)) (i : X₀ ⟶ X.left) (z : Z1 (O κ s₀)) : Prop :=
  ∃ t : ∀ a : Pt κ s₀ X i, a.T.B, TrivBy z t

def IsSqIdeal (T : Thick κ s₀) (K : Ideal T.B) : Prop :=
  K ≤ T.J ∧ (∀ a ∈ K, ∀ b ∈ K, a * b = 0) ∧ ∀ n, 2 ≤ n → ∀ a ∈ K, T.δ.dpow n a = 0

def IsConn (z : Z1 (O κ s₀)) (T : Thick κ s₀) (η : Ω[T.B⁄R]) : Prop :=
  ∀ (T' : Thick κ s₀) (K : Ideal T'.B), IsSqIdeal T' K → ∀ (ψ ψ' : T ⟶ T') (D : Ω[T.B⁄R] →+ T'.B),
    (∀ (b : T.B) (ω : Ω[T.B⁄R]), D (b • ω) = ψ.φ b * D ω) →
    (∀ b : T.B, D (KaehlerDifferential.D R T.B b) = ψ'.φ b - ψ.φ b) → (∀ b : T.B, ψ'.φ b - ψ.φ b ∈ K) →
    ev z ψ' - ev z ψ = D η

def OmFrame {R' : Type} [CommRing R'] (σ : R →+* R') (J : Ideal R') (B : Type) [CommRing B] [Algebra R' B]
    {P : Type 1} [AddCommGroup P] [Module R P] (θ : P → Ω[B⁄R']) : Prop :=
  ∀ (M : Type) [AddCommGroup M] [Module B M], (∀ r ∈ J, ∀ m : M, algebraMap R' B r • m = 0) →
    ∀ l : P →+ M, (∀ (r : R) (p : P), l (r • p) = algebraMap R' B (σ r) • l p) →
      ∃! D : Ω[B⁄R'] →ₗ[B] M, ∀ p, D (θ p) = l p

def CoFrame {R' : Type} [CommRing R'] (σ : R →+* R') {Y : Scheme.{0}} (s : Y ⟶ Sp R')
    {P : Type 1} [AddCommGroup P] [Module R P] (ω : P → Form s) : Prop :=
  ∀ (B : Type) [CommRing B] [Algebra R' B] (x : Sp B ⟶ Y) (hx : x ≫ s = spMap (algebraMap R' B)),
    IsOpenImmersion x → OmFrame σ ⊥ B fun p ↦ connForm (ω p).1 x hx

def LocFrame (J : Ideal R) {P : Type 1} [AddCommGroup P] [Module R P] (z : P → Z1 (O κ s₀)) (T : Thick κ s₀)
    (ζ : P → T.B) : Prop :=
  ∀ (T' : Thick κ s₀) (ψ₀ : T ⟶ T') (l : P →ₗ[R] T'.B), (∀ p, l p ∈ J.map (algebraMap R T'.B)) →
    ∃! ψ : T ⟶ T', (∀ b : T.B, ψ.φ b - ψ₀.φ b ∈ J.map (algebraMap R T'.B)) ∧
      ∀ p, ev (z p) ψ + ψ.φ (ζ p) = ev (z p) ψ₀ + ψ₀.φ (ζ p) + l p

def Frame (J : Ideal R) {P : Type 1} [AddCommGroup P] [Module R P] (z : P → Z1 (O κ s₀))
    (t : P → ∀ a : Pt κ s₀ X i, a.T.B) : Prop :=
  ∀ x : X.left, ∃ a : Pt κ s₀ X i, a.IsChart ∧ x ∈ Set.range a.y ∧ LocFrame J z a.T fun p ↦ t p a

theorem redIsMor (κ : DividedPowers I) (w : i ≫ X.hom = s₀) :
    IsMor (dp0 R) (X.hom ≫ 𝟙 _) κ s₀ (RingHom.id R) i :=
  IsMor.of_dividedPowersZeroIdeal κ (by rw [GlobalTheory.Cris.spMap_id, Category.comp_id, Category.comp_id, w])

def PreChart {R₁ : Type} [CommRing R₁] {I₁ : Ideal R₁} {κ₁ : DividedPowers I₁} {s₁ : X₀ ⟶ Sp R₁} {ρ : R →+* R₁}
    (M : IsMor κ s₀ κ₁ s₁ ρ (𝟙 X₀)) {X₁ : Over (Sp R₁)} {i₁ : X₀ ⟶ X₁.left} (a₁ : Pt κ₁ s₁ X₁ i₁)
    (T : Thick κ s₀) (r : T ⟶ M.obj a₁.T) : Prop :=
  a₁.IsChart ∧ Function.Surjective r.φ ∧
    (∀ b : T.B, r.φ b = 0 ↔ b ∈ (RingHom.ker ρ).map (algebraMap R T.B)) ∧
    T.J = I.map (algebraMap R T.B) ∧ Algebra.Smooth R T.B

end PositivityTheory.JLift
