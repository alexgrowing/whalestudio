import Mathlib
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped TensorProduct

namespace GlobalTheory.QuadNormBase

theorem norm_of_basis {R A : Type} [CommRing R] [CommRing A] [Algebra R A]
    (B : Module.Basis (Fin 2) R A) (d : R) (h0 : B 0 = 1) (h1 : B 1 * B 1 = d • B 0) (x y : R) :
    Algebra.norm R (x • B 0 + y • B 1) = x ^ 2 - d * y ^ 2 := by
  have e0 : (x • B 0 + y • B 1) * B 0 = x • B 0 + y • B 1 := by rw [h0, mul_one]
  have e1 : (x • B 0 + y • B 1) * B 1 = (y * d) • B 0 + x • B 1 := by
    rw [add_mul, smul_mul_assoc, smul_mul_assoc, h1, smul_smul, add_comm]
    congr 1
    rw [h0, one_mul]
  rw [Algebra.norm_eq_matrix_det B, Matrix.det_fin_two]
  simp only [Algebra.leftMulMatrix_eq_repr_mul, e0, e1]
  simp
  ring

theorem exists_basis (F E : Type) [Field F] [CharZero F] [Field E] [Algebra F E] (σ : E →ₐ[F] E)
    (hr : Module.finrank F E = 2) (hσ : ∀ x, σ (σ x) = x) (hne : ∃ x, σ x ≠ x) :
    ∃ (δ : F) (b : Module.Basis (Fin 2) F E), ¬ IsSquare δ ∧ b 0 = 1 ∧ σ (b 1) = - b 1 ∧
      b 1 * b 1 = algebraMap F E δ := by
  haveI : CharZero E := charZero_of_injective_algebraMap (algebraMap F E).injective
  obtain ⟨x0, hx0⟩ := hne
  have hsm : ∀ (c : F) (e : E), σ (c • e) = c • σ e := fun c e => by
    rw [Algebra.smul_def, Algebra.smul_def, map_mul, AlgHom.commutes]
  set θ : E := x0 - σ x0 with hθ
  have hθ0 : θ ≠ 0 := sub_ne_zero.2 hx0.symm
  have hσθ : σ θ = -θ := by rw [hθ, map_sub, hσ]; ring
  have hli : LinearIndependent F ![(1 : E), θ] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    have h2 := congrArg σ hst
    rw [map_add, hsm, hsm, map_one, hσθ, map_zero, smul_neg] at h2
    have h3 : (2 : E) * (t • θ) = 0 := by linear_combination hst - h2
    have h4 : t • θ = 0 := by simpa only [mul_eq_zero, two_ne_zero, false_or] using h3
    have ht : t = 0 := (smul_eq_zero.1 h4).resolve_right hθ0
    subst ht
    exact ⟨by simpa using hst, rfl⟩
  let b : Module.Basis (Fin 2) F E :=
    basisOfLinearIndependentOfCardEqFinrank hli (by simp [hr])
  have hb0 : b 0 = 1 := by simp [b]
  have hb1 : b 1 = θ := by simp [b]
  have hrep := b.sum_repr (θ * θ)
  rw [Fin.sum_univ_two, hb0, hb1] at hrep
  set s := b.repr (θ * θ) 0
  set t := b.repr (θ * θ) 1
  have h2 := congrArg σ hrep
  rw [map_add, hsm, hsm, map_one, map_mul, hσθ, smul_neg] at h2
  have h3 : (2 : E) * (t • θ) = 0 := by linear_combination hrep - h2
  have h4 : t • θ = 0 := by simpa only [mul_eq_zero, two_ne_zero, false_or] using h3
  have hsq : θ * θ = algebraMap F E s := by
    rw [← hrep, h4, add_zero, Algebra.algebraMap_eq_smul_one]
  refine ⟨s, b, ?_, hb0, by rw [hb1, hσθ], by rw [hb1, hsq]⟩
  rintro ⟨r, hr⟩
  rw [hr, map_mul, mul_self_eq_mul_self_iff] at hsq
  have hfix : σ θ = θ := by
    rcases hsq with h | h
    · rw [h, AlgHom.commutes]
    · rw [h, map_neg, AlgHom.commutes]
  have h5 : (2 : E) * θ = 0 := by linear_combination hσθ - hfix
  exact hθ0 (by simpa only [mul_eq_zero, two_ne_zero, false_or] using h5)

theorem norm_form : ∀ (F E : Type) [Field F] [CharZero F] [Field E] [Algebra F E] (σ : E →ₐ[F] E), Module.finrank F E = 2 → (∀ x, σ (σ x) = x) → (∃ x, σ x ≠ x) → ∃ δ : F, ¬ IsSquare δ ∧ ∀ (R : Type) [CommRing R] [Algebra F R], (∀ z : R ⊗[F] E, ∃ x y : R, Algebra.norm R z = x ^ 2 - algebraMap F R δ * y ^ 2 ∧ z * sigR R σ z = algebraMap R (R ⊗[F] E) (x ^ 2 - algebraMap F R δ * y ^ 2)) ∧ ∀ x y : R, ∃ z : R ⊗[F] E, z * sigR R σ z = algebraMap R (R ⊗[F] E) (x ^ 2 - algebraMap F R δ * y ^ 2) := by
  intro F E _ _ _ _ σ hr hσ hne
  obtain ⟨δ, b, hδ, hb0, hb1, hsq⟩ := exists_basis F E σ hr hσ hne
  refine ⟨δ, hδ, ?_⟩
  intro R _ _
  let B := Algebra.TensorProduct.basis R b
  have hB : ∀ i, B i = 1 ⊗ₜ[F] b i := fun i => Algebra.TensorProduct.basis_apply b i
  have h0 : B 0 = 1 := by rw [hB, hb0]; rfl
  have h1 : B 1 * B 1 = algebraMap F R δ • B 0 := by
    rw [hB, hB, Algebra.TensorProduct.tmul_mul_tmul, hsq, hb0, Algebra.algebraMap_eq_smul_one (A := E),
      TensorProduct.tmul_smul, one_mul, algebraMap_smul]
  have hs : ∀ (r : R) (e : E), sigR R σ (r ⊗ₜ[F] e) = r ⊗ₜ[F] σ e := fun r e => rfl
  have key : ∀ x y : R, (x • B 0 + y • B 1) * sigR R σ (x • B 0 + y • B 1) =
      algebraMap R (R ⊗[F] E) (x ^ 2 - algebraMap F R δ * y ^ 2) := by
    intro x y
    have e : sigR R σ (x • B 0 + y • B 1) = x • B 0 - y • B 1 := by
      rw [map_add, hB, hB, TensorProduct.smul_tmul', TensorProduct.smul_tmul', hs, hs, hb1, hb0,
        map_one, TensorProduct.tmul_neg, sub_eq_add_neg]
    rw [e]
    rw [h0] at h1 ⊢
    generalize algebraMap F R δ = d at h1 ⊢
    simp only [Algebra.smul_def, mul_one, map_sub, map_mul, map_pow] at h1 ⊢
    linear_combination (-(algebraMap R (R ⊗[F] E) y) ^ 2) * h1
  refine ⟨fun z => ?_, fun x y => ⟨_, key x y⟩⟩
  have hz := B.sum_repr z
  rw [Fin.sum_univ_two] at hz
  refine ⟨B.repr z 0, B.repr z 1, ?_, ?_⟩
  · rw [← norm_of_basis B _ h0 h1, hz]
  · rw [← key, hz]

end GlobalTheory.QuadNormBase
