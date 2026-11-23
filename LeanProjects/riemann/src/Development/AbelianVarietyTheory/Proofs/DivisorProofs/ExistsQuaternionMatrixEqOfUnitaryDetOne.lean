import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EmbUnitary
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published GlobalTheory.QSA GlobalTheory.PlaneSU
open scoped TensorProduct Quaternion

noncomputable section

namespace GlobalTheory.PlaneSU

section Form

variable {F E : Type} [Field F] [Field E] [Algebra F E] {R : Type} [CommRing R] [Algebra F R]

theorem tensor_decomp (b : Module.Basis (Fin 2) F E) (hb0 : b 0 = 1) (z : R ⊗[F] E) :
    ∃ r₀ r₁ : R, z = algebraMap R (R ⊗[F] E) r₀ + algebraMap R (R ⊗[F] E) r₁ * ((1 : R) ⊗ₜ[F] b 1) := by
  let B := Algebra.TensorProduct.basis R b
  have hB : ∀ i, B i = 1 ⊗ₜ[F] b i := fun i => Algebra.TensorProduct.basis_apply b i
  have hz := B.sum_repr z
  rw [Fin.sum_univ_two, hB, hB, hb0, Algebra.smul_def, Algebra.smul_def, ← Algebra.TensorProduct.one_def,
    mul_one] at hz
  exact ⟨B.repr z 0, B.repr z 1, hz.symm⟩

theorem sigR_algebraMap (σ : E →ₐ[F] E) (r : R) :
    sigR R σ (algebraMap R (R ⊗[F] E) r) = algebraMap R (R ⊗[F] E) r := by
  show sigR R σ (r ⊗ₜ[F] 1) = r ⊗ₜ[F] 1
  simp [sigR]

theorem sigR_theta (σ : E →ₐ[F] E) (e : E) (he : σ e = -e) :
    sigR R σ ((1 : R) ⊗ₜ[F] e) = -((1 : R) ⊗ₜ[F] e) := by
  simp [sigR, he, TensorProduct.tmul_neg]

theorem cT_mul_eq_mul_adjugate {A : Type} [CommRing A] (c : A →+* A) (H X : Matrix (Fin 2) (Fin 2) A)
    (hX : Formalism.UG.cT c X * H * X = H) (hd : X.det = 1) : Formalism.UG.cT c X * H = H * X.adjugate := by
  calc Formalism.UG.cT c X * H = Formalism.UG.cT c X * H * (X * X.adjugate) := by
        rw [Matrix.mul_adjugate, hd, one_smul, Matrix.mul_one]
    _ = H * X.adjugate := by rw [← Matrix.mul_assoc, hX]

end Form
end GlobalTheory.PlaneSU

theorem GlobalTheory.PlaneSU.exists_qm_eq_of_unitary : ∀ (F E : Type) [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) (δ : F) (b : Module.Basis (Fin 2) F E), b 0 = 1 → σ (b 1) = -b 1 → b 1 * b 1 = algebraMap F E δ → ∀ f₁ f₂ : F, f₁ ≠ 0 → f₂ ≠ 0 → ∀ (R : Type) [CommRing R] [Algebra F R] (X : Matrix (Fin 2) (Fin 2) (R ⊗[F] E)), Formalism.UG.cT (sigR R σ) X * Matrix.diagonal ![algebraMap F (R ⊗[F] E) f₁, algebraMap F (R ⊗[F] E) f₂] * X = Matrix.diagonal ![algebraMap F (R ⊗[F] E) f₁, algebraMap F (R ⊗[F] E) f₂] → X.det = 1 → ∃ x : ℍ[R, algebraMap F R δ, algebraMap F R (-(f₂ / f₁))], qm (algebraMap R (R ⊗[F] E)) ((1 : R) ⊗ₜ[F] b 1) x = X := by
  intro F E _ _ _ σ δ b hb0 hσ _ f₁ f₂ hf₁ _ R _ _ X hX hd
  set ι := algebraMap R (R ⊗[F] E) with hιdef
  set θ : R ⊗[F] E := (1 : R) ⊗ₜ[F] b 1 with hθdef
  set c := sigR R σ with hcdef
  set h₁ := algebraMap F (R ⊗[F] E) f₁ with hh₁
  set h₂ := algebraMap F (R ⊗[F] E) f₂ with hh₂
  set u := algebraMap F (R ⊗[F] E) f₁⁻¹ with hudef
  have key := GlobalTheory.PlaneSU.cT_mul_eq_mul_adjugate c _ X hX hd
  have k00 : c (X 0 0) * h₁ = h₁ * X 1 1 := by
    have := congrFun (congrFun key 0) 0
    simpa [Formalism.UG.cT, Matrix.adjugate_fin_two, Matrix.mul_apply, Fin.sum_univ_two] using this
  have k01 : c (X 1 0) * h₂ = -(h₁ * X 0 1) := by
    have := congrFun (congrFun key 0) 1
    simpa [Formalism.UG.cT, Matrix.adjugate_fin_two, Matrix.mul_apply, Fin.sum_univ_two] using this
  have hcθ : c θ = -θ := GlobalTheory.PlaneSU.sigR_theta σ (b 1) hσ
  have hcι : ∀ r, c (ι r) = ι r := GlobalTheory.PlaneSU.sigR_algebraMap σ
  have hu : h₁ * u = 1 := by
    rw [hh₁, hudef, ← map_mul, mul_inv_cancel₀ hf₁, map_one]
  have hb : ι (algebraMap F R (-(f₂ / f₁))) = -(h₂ * u) := by
    rw [hιdef, ← IsScalarTower.algebraMap_apply, div_eq_mul_inv, map_neg, map_mul]
  obtain ⟨r₀, r₁, hα⟩ := GlobalTheory.PlaneSU.tensor_decomp (R := R) b hb0 (X 0 0)
  obtain ⟨s₀, s₁, hβ⟩ := GlobalTheory.PlaneSU.tensor_decomp (R := R) b hb0 (X 1 0)
  have hcα : c (X 0 0) = ι r₀ - ι r₁ * θ := by rw [hα, map_add, map_mul, hcι, hcι, hcθ]; ring
  have hcβ : c (X 1 0) = ι s₀ - ι s₁ * θ := by rw [hβ, map_add, map_mul, hcι, hcι, hcθ]; ring
  have e00 : ι r₀ + ι r₁ * θ = X 0 0 := hα.symm
  have e10 : ι s₀ - ι (-s₁) * θ = X 1 0 := by rw [hβ, map_neg]; ring
  have e11 : ι r₀ - ι r₁ * θ = X 1 1 := by
    linear_combination (-1 : R ⊗[F] E) * hcα + u * k00 + (X 1 1 - c (X 0 0)) * hu
  have e01 : ι (algebraMap F R (-(f₂ / f₁))) * (ι s₀ + ι (-s₁) * θ) = X 0 1 := by
    rw [hb, map_neg]
    linear_combination (-u) * k01 + X 0 1 * hu + h₂ * u * hcβ
  refine ⟨⟨r₀, r₁, s₀, -s₁⟩, ?_⟩
  show !![ι r₀ + ι r₁ * θ, ι (algebraMap F R (-(f₂ / f₁))) * (ι s₀ + ι (-s₁) * θ);
    ι s₀ - ι (-s₁) * θ, ι r₀ - ι r₁ * θ] = X
  rw [e00, e01, e10, e11]
  exact (Matrix.eta_fin_two X).symm
