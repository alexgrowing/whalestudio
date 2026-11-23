import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenFibMapAlgebraMap

open CategoryTheory Limits TensorProduct

noncomputable section

namespace GlobalTheory.TorsorColim

def bcAct (S : Type) {R A G : Type} [CommRing R] [CommRing S] [CommRing A] [Algebra R S]
    [Algebra R A] [Monoid G] (act : G →* (A ≃ₐ[R] A)) : G →* (S ⊗[R] A ≃ₐ[S] S ⊗[R] A) where
  toFun g := Algebra.TensorProduct.congr AlgEquiv.refl (act g)
  map_one' := by
    ext x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul s a => simp
    | add x y hx hy => rw [map_add, hx, hy, map_add]
  map_mul' g h := by
    ext x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul s a => simp
    | add x y hx hy => rw [map_add, hx, hy, map_add]

@[simp]
theorem bcAct_tmul (S : Type) {R A G : Type} [CommRing R] [CommRing S] [CommRing A] [Algebra R S]
    [Algebra R A] [Monoid G] (act : G →* (A ≃ₐ[R] A)) (g : G) (s : S) (a : A) :
    bcAct S act g (s ⊗ₜ[R] a) = s ⊗ₜ[R] act g a := rfl

def prodMapOf (B D : Type) [CommRing B] [CommRing D] [Algebra B D] (q : ℕ)
    (act : Multiplicative (ZMod q) →* (D ≃ₐ[B] D)) :
    D ⊗[B] D →ₐ[B] (Multiplicative (ZMod q) → D) :=
  Algebra.TensorProduct.productMap
    (Pi.algHom B (fun _ : Multiplicative (ZMod q) => D) (fun _ => AlgHom.id B D))
    (Pi.algHom B (fun _ : Multiplicative (ZMod q) => D) (fun g => (act g).toAlgHom))

@[simp]
theorem prodMapOf_tmul (B D : Type) [CommRing B] [CommRing D] [Algebra B D] (q : ℕ)
    (act : Multiplicative (ZMod q) →* (D ≃ₐ[B] D)) (x y : D) (g : Multiplicative (ZMod q)) :
    prodMapOf B D q act (x ⊗ₜ[B] y) g = x * act g y := by
  simp [prodMapOf]

theorem eventually_and {J : Type} [Category J] [IsFiltered J] {j : J}
    (P Q : ∀ k : J, (j ⟶ k) → Prop)
    (hP : ∃ (k₀ : J) (f₀ : j ⟶ k₀), ∀ (k : J) (f : k₀ ⟶ k), P k (f₀ ≫ f))
    (hQ : ∃ (k₀ : J) (f₀ : j ⟶ k₀), ∀ (k : J) (f : k₀ ⟶ k), Q k (f₀ ≫ f)) :
    ∃ (k₀ : J) (f₀ : j ⟶ k₀), ∀ (k : J) (f : k₀ ⟶ k), P k (f₀ ≫ f) ∧ Q k (f₀ ≫ f) := by
  obtain ⟨k₁, f₁, h₁⟩ := hP
  obtain ⟨k₂, f₂, h₂⟩ := hQ
  let a := IsFiltered.leftToMax k₁ k₂
  let b := IsFiltered.rightToMax k₁ k₂
  let e := IsFiltered.coeqHom (f₁ ≫ a) (f₂ ≫ b)
  have he : (f₁ ≫ a) ≫ e = (f₂ ≫ b) ≫ e := IsFiltered.coeq_condition _ _
  refine ⟨IsFiltered.coeq (f₁ ≫ a) (f₂ ≫ b), (f₁ ≫ a) ≫ e, fun k f => ⟨?_, ?_⟩⟩
  · have := h₁ k (a ≫ e ≫ f)
    simpa only [Category.assoc] using this
  · have := h₂ k (b ≫ e ≫ f)
    rw [he]
    simpa only [Category.assoc] using this

end GlobalTheory.TorsorColim
