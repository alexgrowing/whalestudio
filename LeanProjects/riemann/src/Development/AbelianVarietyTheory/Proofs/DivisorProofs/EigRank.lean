import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasDefect
import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidChart
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis

noncomputable section

open AlgebraicGeometry NumberField
open scoped Matrix

namespace GlobalTheory.BalProj

def eigSp {O k : Type} [Field k] {n : ℕ} (B : O → Matrix (Fin n) (Fin n) k) (χ : O → k) :
    Submodule k (Fin n → k) where
  carrier := {c | ∀ a, c ᵥ* B a = χ a • c}
  zero_mem' := fun a => by simp
  add_mem' := fun {c d} hc hd a => by rw [Matrix.add_vecMul, hc a, hd a, smul_add]
  smul_mem' := fun r c hc a => by rw [Matrix.smul_vecMul, hc a, smul_comm]

def eigRank {O R k : Type} [CommRing R] [Field k] (φ : R →+* k) {n : ℕ} (A : O → Matrix (Fin n) (Fin n) R)
    (χ : O → R) : ℕ :=
  Module.finrank k (eigSp (fun a => (A a).map φ) (fun a => φ (χ a)))

def embR {E : Type} [Field E] (F : IntermediateField ℚ ℂ) (hF : ∀ (τ : E →+* ℂ) (a : E), τ a ∈ F) {R : Type}
    [CommRing R] (ι : F →+* R) (τ : E →+* ℂ) (a : 𝓞 E) : R :=
  ι ⟨τ (a : E), hF τ a⟩

def fnHom {K : Type} [CommRing K] {X : Scheme.{0}} (s : X ⟶ Spec (CommRingCat.of K)) (U : X.Opens) : K →+* Γ(X, U) :=
  (s.appLE ⊤ U (fun _ _ => trivial)).hom.comp (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom

end GlobalTheory.BalProj
