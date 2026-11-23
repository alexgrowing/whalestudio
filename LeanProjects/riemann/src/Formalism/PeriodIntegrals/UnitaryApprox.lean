import Mathlib

noncomputable section

open Matrix TensorProduct NumberField IsDedekindDomain

namespace PI

section Group

variable {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n]

def UnitaryApproxDefs.cT (σ : A →+* A) {m p : Type} (M : Matrix m p A) : Matrix p m A := (M.map σ)ᵀ

def UnitaryApproxDefs.IsHerm (σ : A →+* A) (J : Matrix n n A) : Prop := UnitaryApproxDefs.cT σ J = J

theorem UnitaryApproxDefs.cT_mul (σ : A →+* A) {m p q : Type} [Fintype p] (M : Matrix m p A) (N : Matrix p q A) :
    UnitaryApproxDefs.cT σ (M * N) = UnitaryApproxDefs.cT σ N * UnitaryApproxDefs.cT σ M := by
  simp [UnitaryApproxDefs.cT, Matrix.map_mul, Matrix.transpose_mul]

theorem UnitaryApproxDefs.cT_one (σ : A →+* A) : UnitaryApproxDefs.cT σ (1 : Matrix n n A) = 1 := by
  unfold UnitaryApproxDefs.cT
  rw [Matrix.map_one σ (map_zero σ) (map_one σ), Matrix.transpose_one]

def UnitaryApproxDefs.UJ (σ : A →+* A) (J : Matrix n n A) : Subgroup (GL n A) where
  carrier := {g | UnitaryApproxDefs.cT σ (g : Matrix n n A) * J * (g : Matrix n n A) = J}
  one_mem' := by simp [UnitaryApproxDefs.cT_one]
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_ofPred_eq, Units.val_mul] at *
    calc UnitaryApproxDefs.cT σ ((a : Matrix n n A) * (b : Matrix n n A)) * J * ((a : Matrix n n A) * (b : Matrix n n A))
        = UnitaryApproxDefs.cT σ (b : Matrix n n A) * (UnitaryApproxDefs.cT σ (a : Matrix n n A) * J * (a : Matrix n n A)) * (b : Matrix n n A) := by
          rw [UnitaryApproxDefs.cT_mul]; simp only [Matrix.mul_assoc]
      _ = J := by rw [ha, hb]
  inv_mem' := by
    intro g hg
    simp only [Set.mem_ofPred_eq] at *
    calc UnitaryApproxDefs.cT σ ((g⁻¹ : GL n A) : Matrix n n A) * J * ((g⁻¹ : GL n A) : Matrix n n A)
        = UnitaryApproxDefs.cT σ ((g⁻¹ : GL n A) : Matrix n n A) * (UnitaryApproxDefs.cT σ (g : Matrix n n A) * J * (g : Matrix n n A))
            * ((g⁻¹ : GL n A) : Matrix n n A) := by rw [hg]
      _ = UnitaryApproxDefs.cT σ ((g : Matrix n n A) * ((g⁻¹ : GL n A) : Matrix n n A)) * J
            * ((g : Matrix n n A) * ((g⁻¹ : GL n A) : Matrix n n A)) := by
          rw [UnitaryApproxDefs.cT_mul]; simp only [Matrix.mul_assoc]
      _ = J := by rw [Units.mul_inv, UnitaryApproxDefs.cT_one, Matrix.one_mul, Matrix.mul_one]
end Group

section Points

variable {F E : Type} [Field F] [CommRing E] [Algebra F E] {n : Type} [Fintype n] [DecidableEq n]

def UnitaryApproxDefs.sigR (σ : E →ₐ[F] E) (R : Type) [CommRing R] [Algebra F R] : E ⊗[F] R →+* E ⊗[F] R :=
  (Algebra.TensorProduct.map σ (AlgHom.id F R)).toRingHom

def UnitaryApproxDefs.inclE (R : Type) [CommRing R] [Algebra F R] : E →+* E ⊗[F] R :=
  Algebra.TensorProduct.includeLeftRingHom

def UnitaryApproxDefs.UPts (σ : E →ₐ[F] E) (J : Matrix n n E) (R : Type) [CommRing R] [Algebra F R] :
    Subgroup (GL n (E ⊗[F] R)) := UnitaryApproxDefs.UJ (UnitaryApproxDefs.sigR σ R) (J.map (UnitaryApproxDefs.inclE (F := F) R))

def UnitaryApproxDefs.tensInt (R : Type) [CommRing R] [Algebra F R] (S₁ : Subring E) (S₂ : Subring R) :
    Subring (E ⊗[F] R) :=
  Subring.closure (Set.range (fun x : S₁ => (x : E) ⊗ₜ[F] (1 : R)) ∪
    Set.range (fun y : S₂ => (1 : E) ⊗ₜ[F] (y : R)))

def UnitaryApproxDefs.intOE (E : Type) [Field E] [NumberField E] : Subring E := (algebraMap (𝓞 E) E).range

end Points

def UnitaryApprox : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (n : Type) [Fintype n] [DecidableEq n] (σ : E →ₐ[F] E) (J : Matrix n n E),
    (∀ e, σ (σ e) = e) → (∃ θ, σ θ ≠ θ) → UnitaryApproxDefs.IsHerm (σ : E →+* E) J → IsUnit J.det →
    ∀ (v : HeightOneSpectrum (𝓞 F)), ∀ g ∈ UnitaryApproxDefs.UPts σ J (v.adicCompletion F), ∀ D : 𝓞 F, D ≠ 0 →
    ∃ γ ∈ UnitaryApproxDefs.UJ (σ : E →+* E) J, ∀ i j,
      ∃ s ∈ UnitaryApproxDefs.tensInt (F := F) (v.adicCompletion F) (UnitaryApproxDefs.intOE E) (v.adicCompletionIntegers F).toSubring,
        (g : Matrix n n (E ⊗[F] v.adicCompletion F)) i j -
            UnitaryApproxDefs.inclE (F := F) (v.adicCompletion F) ((γ : Matrix n n E) i j) =
          UnitaryApproxDefs.inclE (F := F) (v.adicCompletion F) (algebraMap F E (D : F)) * s

end PI

end
