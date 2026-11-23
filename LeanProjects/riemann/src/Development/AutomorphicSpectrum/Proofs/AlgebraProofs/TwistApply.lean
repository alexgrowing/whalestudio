import Mathlib
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsSplitGaussChars
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.EigenProjectorsSplitAction

noncomputable section

open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.Ar.Flat.DegCurve

open GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Crv.SplitProj

def act (k : Type) {K V O : Type} [Field K] [AddCommGroup V] [Module K V] [CommRing O] [Field k]
    [Algebra k K] (ρ : O →+* Module.End K V) : TensorProduct ℤ k O →+* Module.End K V :=
  (actMap (k := k) ρ).toRingHom

theorem act_tmul (k : Type) {K V O : Type} [Field K] [AddCommGroup V] [Module K V] [CommRing O]
    [Field k] [Algebra k K] (ρ : O →+* Module.End K V) (c : k) (a : O) :
    act k ρ (c ⊗ₜ[ℤ] a) = algebraMap k K c • ρ a :=
  actMap_tmul ρ c a

def toEnd {K O : Type} [Field K] [CommRing O] {d : ℕ} (ρ : O →+* Matrix (Fin d) (Fin d) K) :
    O →+* Module.End K (Fin d → K) :=
  (Matrix.toLinAlgEquiv' (R := K) (n := Fin d)).toAlgHom.toRingHom.comp ρ

theorem toEnd_apply {K O : Type} [Field K] [CommRing O] {d : ℕ}
    (ρ : O →+* Matrix (Fin d) (Fin d) K) (a : O) (v : Fin d → K) :
    toEnd ρ a v = (ρ a).mulVec v := rfl

def twist {K O : Type} [Field K] [CommRing O] {d : ℕ} (p : ℕ) [Fact p.Prime] [CharP K p]
    (ρ : O →+* Matrix (Fin d) (Fin d) K) : O →+* Matrix (Fin d) (Fin d) K :=
  (frobenius K p).mapMatrix.comp ρ

theorem twist_apply {K O : Type} [Field K] [CommRing O] {d : ℕ} (p : ℕ) [Fact p.Prime] [CharP K p]
    (ρ : O →+* Matrix (Fin d) (Fin d) K) (a : O) : twist p ρ a = (ρ a).map (· ^ p) := rfl

def conjT {K O : Type} [Field K] [CommRing O] [StarRing O] {d : ℕ}
    (ρ : O →+* Matrix (Fin d) (Fin d) K) : O →+* Matrix (Fin d) (Fin d) K where
  toFun a := (ρ (star a)).transpose
  map_one' := by simp
  map_mul' a b := by
    rw [star_mul, map_mul, Matrix.transpose_mul]
  map_zero' := by simp
  map_add' a b := by simp [star_add]

theorem conjT_apply {K O : Type} [Field K] [CommRing O] [StarRing O] {d : ℕ}
    (ρ : O →+* Matrix (Fin d) (Fin d) K) (a : O) : conjT ρ a = (ρ (star a)).transpose := rfl

def frobT (k O : Type) [Field k] [CommRing O] (p : ℕ) [Fact p.Prime] [CharP k p] :
    TensorProduct ℤ k O →+* TensorProduct ℤ k O :=
  (Algebra.TensorProduct.map (frobenius k p).toIntAlgHom (AlgHom.id ℤ O)).toRingHom

theorem frobT_tmul (k O : Type) [Field k] [CommRing O] (p : ℕ) [Fact p.Prime] [CharP k p] (c : k)
    (a : O) : frobT k O p (c ⊗ₜ[ℤ] a) = (c ^ p) ⊗ₜ[ℤ] a := by
  simp [frobT, frobenius_def]

def chiT {k O : Type} [Field k] [CommRing O] (χ : O →+* k) : TensorProduct ℤ k O →ₐ[k] k :=
  Algebra.TensorProduct.lift (AlgHom.id k k) χ.toIntAlgHom (fun _ _ => Commute.all _ _)

theorem chiT_tmul {k O : Type} [Field k] [CommRing O] (χ : O →+* k) (c : k) (a : O) :
    chiT χ (c ⊗ₜ[ℤ] a) = c * χ a := by
  simp [chiT]

def idealV {K A V : Type} [Field K] [CommRing A] [AddCommGroup V] [Module K V]
    (τ : A →+* Module.End K V) (J : Ideal A) : Submodule K V :=
  ⨆ a : J, LinearMap.range (τ a)

def FreeAt {K : Type} [Field K] (C : ACurve K) (k : Type) {A V : Type} [Field k] [Algebra k K]
    [CommRing A] [Algebra k A] [AddCommGroup V] [Module K V] (τ : A →+* Module.End K V)
    (L : C.I → AddSubgroup V) (r : ℕ) (i : C.I) : Prop :=
  ∃ (x : Fin r → V) (Θ : (A →ₗ[k] k) → Fin r → (V →ₗ[K] K)),
    (∀ s, x s ∈ L i) ∧
    (∀ l s s' a, Θ l s (τ a (x s')) = if s = s' then algebraMap k K (l a) else 0) ∧
    (∀ l s y, y ∈ L i → C.v i (Θ l s y) ≤ 1) ∧
    ∀ y : V, y ∈ Submodule.span K (Set.range fun q : A × Fin r => τ q.1 (x q.2))

end GlobalTheory.CompanionTheory.Ar.Flat.DegCurve
