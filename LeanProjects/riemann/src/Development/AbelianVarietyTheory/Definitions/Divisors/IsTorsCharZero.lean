import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDatNeZero

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap)
open GlobalTheory.DeRham GlobalTheory.PDiv

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PtExt

variable {R : Type} [CommRing R]

abbrev RootFn (X : Over (Sp R)) (D : Type) [CommRing D] [Algebra R D] : Type 1 :=
  ∀ (D' : Type) [CommRing D'] [Algebra R D'], (D →ₐ[R] D') → Pt X D' → D'

variable {A : Over (Sp R)} [GrpObj A]

variable (A) in

def HasRoots (n : ℕ) : Prop :=
  ∀ (D : Type) [CommRing D] [Algebra R D] (x : Pt A D), ∃ (D' : Type) (_ : CommRing D') (_ : Algebra R D')
    (ψ : D →ₐ[R] D') (z : Pt A D'), (ψ : D →+* D').FaithfullyFlat ∧ z ^ n = spOver ψ ≫ x

def IsTorsChar (n : ℕ) (b : Fn0 A) : Prop :=
  (∀ (D : Type) [CommRing D] [Algebra R D] (D' : Type) [CommRing D'] [Algebra R D'] (φ : D →ₐ[R] D') (w : Pt A D),
    w ^ n = 1 → b D' (spOver φ ≫ w) = φ (b D w)) ∧
  ∀ (D : Type) [CommRing D] [Algebra R D] (w w' : Pt A D), w ^ n = 1 → w' ^ n = 1 → b D (w * w') = b D w + b D w'

def IsSec (n : ℕ) (b : Fn0 A) {D : Type} [CommRing D] [Algebra R D] (x : Pt A D) (s : RootFn A D) : Prop :=
  (∀ (D' : Type) [CommRing D'] [Algebra R D'] (D'' : Type) [CommRing D''] [Algebra R D''] (φ : D →ₐ[R] D')
    (ψ : D' →ₐ[R] D'') (z : Pt A D'), z ^ n = spOver φ ≫ x → s D'' (ψ.comp φ) (spOver ψ ≫ z) = ψ (s D' φ z)) ∧
  ∀ (D' : Type) [CommRing D'] [Algebra R D'] (φ : D →ₐ[R] D') (z w : Pt A D'),
    z ^ n = spOver φ ≫ x → w ^ n = 1 → s D' φ (z * w) = s D' φ z + b D' w

abbrev SecFam (X : Over (Sp R)) : Type 1 := ∀ (D : Type) [CommRing D] [Algebra R D], Pt X D → RootFn X D

def IsSecDiff (n : ℕ) (S : SecFam A) (u : Fn1 A) : Prop :=
  ∀ (D : Type) [CommRing D] [Algebra R D] (D' : Type) [CommRing D'] [Algebra R D'] (φ : D →ₐ[R] D') (x : Pt A D)
    (E : Type) [CommRing E] [Algebra R E] (ψ : D' →ₐ[R] E) (z : Pt A E), z ^ n = spOver ψ ≫ spOver φ ≫ x →
    ψ (u D D' φ x) = S D' (spOver φ ≫ x) E ψ z - S D x E (ψ.comp φ) z

def IsSecAdd (n : ℕ) (S : SecFam A) (g : Fn2 A) : Prop :=
  ∀ (D : Type) [CommRing D] [Algebra R D] (x y : Pt A D) (E : Type) [CommRing E] [Algebra R E] (ψ : D →ₐ[R] E)
    (z w : Pt A E), z ^ n = spOver ψ ≫ x → w ^ n = spOver ψ ≫ y →
    ψ (g D x y) = S D (x * y) E ψ (z * w) - S D x E ψ z - S D y E ψ w

theorem hasRoots_one : HasRoots A 1 := fun D _ _ x ↦
  ⟨D, inferInstance, inferInstance, AlgHom.id R D, x, RingHom.FaithfullyFlat.of_bijective Function.bijective_id, by
    rw [pow_one, spOver_id, Category.id_comp]⟩

theorem isTorsChar_zero (n : ℕ) : IsTorsChar (A := A) n fun _ _ _ _ ↦ 0 :=
  ⟨fun _ _ _ _ _ _ φ _ _ ↦ (map_zero φ).symm, fun _ _ _ _ _ _ _ ↦ (add_zero _).symm⟩

theorem isSec_zero (n : ℕ) {D : Type} [CommRing D] [Algebra R D] (x : Pt A D) :
    IsSec n (fun _ _ _ _ ↦ 0) x fun _ _ _ _ _ ↦ 0 :=
  ⟨fun _ _ _ _ _ _ _ ψ _ _ ↦ (map_zero ψ).symm, fun _ _ _ _ _ _ _ _ ↦ (add_zero _).symm⟩

variable (R) in

def diagSum (D : Type) [CommRing D] [Bialgebra R D] [Coalgebra.IsCocomm R D] (m : ℕ) : D ⊗[R] D →ₗ[R] D :=
  ∑ i ∈ Finset.range m, (Algebra.TensorProduct.lift (mulBy R D i : D →ₐ[R] D) (AlgHom.id R D)
    fun _ _ ↦ Commute.all _ _).toLinearMap

theorem diagSum_tmul (D : Type) [CommRing D] [Bialgebra R D] [Coalgebra.IsCocomm R D] (m : ℕ) (a b : D) :
    diagSum R D m (a ⊗ₜ b) = ∑ i ∈ Finset.range m, mulBy R D i a * b := by
  simp [diagSum, LinearMap.sum_apply]

end GlobalTheory.PtExt
