import Mathlib

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cmp

open Matrix NumberField IsDedekindDomain
open scoped TensorProduct

section General

variable {R : Type} [CommRing R] {N : ℕ}

def uGrp (σ : R →+* R) (J : Matrix (Fin N) (Fin N) R) : Subgroup (GL (Fin N) R) where
  carrier := {g | (g : Matrix (Fin N) (Fin N) R)ᵀ * J * (g : Matrix (Fin N) (Fin N) R).map σ = J}
  one_mem' := by simp
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq, Units.val_mul, Matrix.transpose_mul, Matrix.map_mul] at *
    calc _ = (b : Matrix (Fin N) (Fin N) R)ᵀ * ((a : Matrix (Fin N) (Fin N) R)ᵀ * J *
          (a : Matrix (Fin N) (Fin N) R).map σ) * (b : Matrix (Fin N) (Fin N) R).map σ := by
            simp only [Matrix.mul_assoc]
      _ = J := by rw [ha, hb]
  inv_mem' := by
    intro a ha
    simp only [Set.mem_setOf_eq] at *
    calc _ = ((a⁻¹ : GL (Fin N) R) : Matrix (Fin N) (Fin N) R)ᵀ * ((a : Matrix (Fin N) (Fin N) R)ᵀ * J *
          (a : Matrix (Fin N) (Fin N) R).map σ) * ((a⁻¹ : GL (Fin N) R) : Matrix (Fin N) (Fin N) R).map σ := by
            rw [ha]
      _ = ((a : Matrix (Fin N) (Fin N) R) * ((a⁻¹ : GL (Fin N) R) : Matrix (Fin N) (Fin N) R))ᵀ * J *
          ((a : Matrix (Fin N) (Fin N) R) * ((a⁻¹ : GL (Fin N) R) : Matrix (Fin N) (Fin N) R)).map σ := by
            simp only [Matrix.transpose_mul, Matrix.map_mul, Matrix.mul_assoc]
      _ = J := by rw [Units.mul_inv]; simp

def suGrp (σ : R →+* R) (J : Matrix (Fin N) (Fin N) R) : Subgroup (GL (Fin N) R) :=
  uGrp σ J ⊓ (Matrix.GeneralLinearGroup.det : GL (Fin N) R →* Rˣ).ker

def congGrp (Λ Λ' : AddSubgroup (Fin N → R)) : Subgroup (GL (Fin N) R) where
  carrier := {g | (∀ x, x ∈ Λ ↔ (g : Matrix (Fin N) (Fin N) R) *ᵥ x ∈ Λ) ∧
    ∀ x ∈ Λ, (g : Matrix (Fin N) (Fin N) R) *ᵥ x - x ∈ Λ'}
  one_mem' := by simp
  mul_mem' := by
    rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    refine ⟨fun x => ?_, fun x hx => ?_⟩
    · rw [Units.val_mul, ← Matrix.mulVec_mulVec, ← ha, ← hb]
    · have h := Λ'.add_mem (ha' _ ((hb x).1 hx)) (hb' x hx)
      rw [Units.val_mul, ← Matrix.mulVec_mulVec]
      simpa using h
  inv_mem' := by
    rintro a ⟨ha, ha'⟩
    have e : ∀ x, (a : Matrix (Fin N) (Fin N) R) *ᵥ
        (((a⁻¹ : GL (Fin N) R) : Matrix (Fin N) (Fin N) R) *ᵥ x) = x := fun x => by
      rw [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]
    refine ⟨fun x => ?_, fun x hx => ?_⟩
    · rw [ha (((a⁻¹ : GL (Fin N) R) : Matrix (Fin N) (Fin N) R) *ᵥ x), e]
    · have hy : ((a⁻¹ : GL (Fin N) R) : Matrix (Fin N) (Fin N) R) *ᵥ x ∈ Λ := by rw [ha, e]; exact hx
      have h := Λ'.neg_mem (ha' _ hy)
      rw [e] at h
      simpa using h

end General

section NumberFields

variable (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {N : ℕ}

abbrev Adf : Type := FiniteAdeleRing (𝓞 F) F ⊗[F] E

def inclAd : E →+* Adf F E := (Algebra.TensorProduct.includeRight : E →ₐ[F] Adf F E).toRingHom

variable {F E}

def sigAd (c : E ≃ₐ[F] E) : Adf F E →+* Adf F E :=
  (Algebra.TensorProduct.map (AlgHom.id F (FiniteAdeleRing (𝓞 F) F)) c.toAlgHom).toRingHom

variable (F)

def hatLat (Λ : AddSubgroup (Fin N → E)) : AddSubgroup (Fin N → Adf F E) :=
  AddSubgroup.closure {y | ∃ a : FiniteAdeleRing (𝓞 F) F,
    (∀ v : HeightOneSpectrum (𝓞 F), a v ∈ v.adicCompletionIntegers F) ∧ ∃ x ∈ Λ, y = fun i => a ⊗ₜ[F] x i}

variable {F}

def levelGrp (σ : E →+* E) (J : Matrix (Fin N) (Fin N) E) (Λ : Submodule (𝓞 E) (Fin N → E))
    (𝔞 : Ideal (𝓞 E)) : Subgroup (GL (Fin N) E) :=
  uGrp σ J ⊓ congGrp Λ.toAddSubgroup (𝔞 • Λ).toAddSubgroup

def adLevelGrp (c : E ≃ₐ[F] E) (J : Matrix (Fin N) (Fin N) E) (Λ : Submodule (𝓞 E) (Fin N → E))
    (𝔞 : Ideal (𝓞 E)) : Subgroup (GL (Fin N) (Adf F E)) :=
  suGrp (sigAd c) (J.map (inclAd F E)) ⊓
    congGrp (hatLat F Λ.toAddSubgroup) (hatLat F (𝔞 • Λ).toAddSubgroup)

structure IsSelfDualLat (σ : E →+* E) (ξ : E) (J : Matrix (Fin N) (Fin N) E)
    (Λ : Submodule (𝓞 E) (Fin N → E)) : Prop where
  fg : Λ.FG
  span : Submodule.span E (Λ : Set (Fin N → E)) = ⊤
  dual : ∀ x : Fin N → E, x ∈ Λ ↔
    ∀ y ∈ Λ, ∃ k : ℤ, Algebra.trace ℚ E (ξ * ∑ i, ∑ j, x i * J i j * σ (y j)) = k

def AdGenus (c : E ≃ₐ[F] E) (J : Matrix (Fin N) (Fin N) E) (Λ Λ' : Submodule (𝓞 E) (Fin N → E)) : Prop :=
  ∃ g ∈ uGrp (sigAd c) (J.map (inclAd F E)), ∀ x,
    x ∈ hatLat F Λ.toAddSubgroup ↔ (g : Matrix (Fin N) (Fin N) (Adf F E)) *ᵥ x ∈ hatLat F Λ'.toAddSubgroup

end NumberFields

end GlobalTheory.CompanionTheory.Ar.Cmp
