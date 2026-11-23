import Mathlib

open scoped TensorProduct

namespace GlobalTheory.EtaleFibre

theorem finrank_baseChange_field (A M L : Type*) [CommRing A] [IsDomain A] [AddCommGroup M]
    [Module A M] [Module.Finite A M] [Module.Flat A M] [Field L] [Algebra A L] :
    Module.finrank L (L ⊗[A] M) = Module.finrank A M := by
  have h := Module.rankAtStalk_baseChange (R := A) (M := M) (S := L) (⊥ : PrimeSpectrum L)
  rw [Module.rankAtStalk_eq_finrank_of_free, Module.rankAtStalk_eq,
    Ideal.finrank_fiber_eq_finrank] at h
  exact h

theorem card_algHom (A B L : Type*) [CommRing A] [IsDomain A] [CommRing B] [Algebra A B]
    [Module.Finite A B] [Algebra.Etale A B] [Field L] [IsSepClosed L] [Algebra A L] :
    Finite (B →ₐ[A] L) ∧ Nat.card (B →ₐ[A] L) = Module.finrank A B := by
  have : IsArtinianRing (L ⊗[A] B) := .of_finite L _
  have := Fintype.ofFinite (PrimeSpectrum (L ⊗[A] B))
  have e : (B →ₐ[A] L) ≃ PrimeSpectrum (L ⊗[A] B) :=
    (AlgHom.liftEquiv A L B L).trans
      (Algebra.IsFiniteSplit.algHomEquivPrimeSpectrum L (L ⊗[A] B))
  refine ⟨Finite.of_equiv _ e.symm, ?_⟩
  rw [Nat.card_congr e, ← finrank_baseChange_field A B L,
    (Algebra.FormallyEtale.equivPiOfIsSepClosed L (L ⊗[A] B)).toLinearEquiv.finrank_eq,
    Module.finrank_fintype_fun_eq_card, Nat.card_eq_fintype_card]

theorem encard_points_eq_finrank : ∀ (A B : Type) [CommRing A] [IsDomain A] [CommRing B] (f : A →+* B), f.Finite → f.Etale → ∀ φ : A →+* ℂ, {ψ : B →+* ℂ | ψ.comp f = φ}.encard = (letI := f.toAlgebra; Module.finrank A B : ℕ) := by
  intro A B _ _ _ f hf he φ
  letI := f.toAlgebra
  letI := φ.toAlgebra
  haveI : Module.Finite A B := hf
  haveI : Algebra.Etale A B := he
  obtain ⟨hfin, hcard⟩ := card_algHom A B ℂ
  let e : {ψ : B →+* ℂ | ψ.comp f = φ} ≃ (B →ₐ[A] ℂ) :=
    { toFun := fun ψ => { ψ.1 with commutes' := fun a => RingHom.congr_fun ψ.2 a }
      invFun := fun ψ => ⟨ψ.toRingHom, RingHom.ext fun a => ψ.commutes a⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have hs : {ψ : B →+* ℂ | ψ.comp f = φ}.Finite := Finite.of_equiv _ e.symm
  rw [← hs.cast_ncard_eq, ← Nat.card_coe_set_eq, Nat.card_congr e, hcard]

end GlobalTheory.EtaleFibre
