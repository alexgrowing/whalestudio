import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnifAt
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitLemmaGroup
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsAevalEqOfSeparable
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SesqAsym
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AntidiagTwistedNorm
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.GramChange

open GlobalTheory.UnitLemma

theorem herm_sum_sum (K : UQ) (B : InvAlg K) (β : B.A) {a : ℕ} (b : Fin a → B.A)
    (M : Matrix (Fin a) (Fin a) K.E) (i j : Fin a) :
    B.herm β (∑ k, M k i • b k) (∑ l, M l j • b l) =
      ∑ k, ∑ l, M k i * B.herm β (b k) (b l) * K.c (M l j) := by
  have hσ : ∀ (r : K.E) (y : B.A), B.σ (r • y) = K.c r • B.σ y := by
    intro r y
    rw [Algebra.smul_def, map_mul, B.σ_alg, ← Algebra.smul_def]
  unfold InvAlg.herm
  simp only [map_sum, hσ, Finset.mul_sum, Finset.sum_mul, mul_smul_comm, smul_mul_assoc,
    LinearMap.map_smul, smul_eq_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  ring

theorem gram_of_sum (K : UQ) (B : InvAlg K) (L : Type) [Field L] (e : K.E ≃+* L) (c : L →+* L)
    (he : ∀ x, e (K.c x) = c (e x)) {a : ℕ} (β : B.A) (b v : Fin a → B.A)
    (M : Matrix (Fin a) (Fin a) K.E) (hv : ∀ j, v j = ∑ i, M i j • b i) :
    (Matrix.of fun i j => e (B.herm β (v i) (v j))) =
      (M.map e)ᵀ * (Matrix.of fun i j => e (B.herm β (b i) (b j))) * (M.map e).map c := by
  ext i j
  simp only [Matrix.of_apply, hv, herm_sum_sum, Matrix.mul_apply, Matrix.transpose_apply,
    Matrix.map_apply, map_sum, map_mul, he, Finset.sum_mul]
  rw [Finset.sum_comm]

theorem gram_basis_change : ∀ (K : GlobalTheory.UnitLemma.UQ) (B : GlobalTheory.UnitLemma.InvAlg K) (L : Type) [Field L] (e : K.E ≃+* L) (c : L →+* L), (∀ x, e (K.c x) = c (e x)) → ∀ (a : ℕ) (β : B.A) (b : Module.Basis (Fin a) K.E B.A), (∀ P : GL (Fin a) L, ∃ b' : Module.Basis (Fin a) K.E B.A, (Matrix.of fun i j => e (B.herm β (b' i) (b' j))) = P.valᵀ * (Matrix.of fun i j => e (B.herm β (b i) (b j))) * P.val.map c) ∧ ∀ b' : Module.Basis (Fin a) K.E B.A, ∃ P : GL (Fin a) L, (Matrix.of fun i j => e (B.herm β (b' i) (b' j))) = P.valᵀ * (Matrix.of fun i j => e (B.herm β (b i) (b j))) * P.val.map c := by
  intro K B L _ e c he a β b
  refine ⟨fun P => ?_, fun b' => ?_⟩
  · set M : Matrix (Fin a) (Fin a) K.E := P.val.map e.symm with hM
    have hMe : M.map e = P.val := by
      ext i j; simp [hM]
    have hdet : IsUnit M.det := by
      have h1 : e M.det = P.val.det := by
        rw [← hMe]; exact RingHom.map_det (e : K.E →+* L) M
      have h2 : IsUnit P.val.det := (Matrix.isUnit_iff_isUnit_det _).mp P.isUnit
      rw [← h1] at h2
      exact (isUnit_map_iff e _).mp h2
    refine ⟨b.map (Matrix.toLinearEquiv b M hdet), ?_⟩
    rw [gram_of_sum K B L e c he β b _ M, hMe]
    intro j
    simp [Matrix.toLinearEquiv_apply, Matrix.toLin_self]
  · have hdet : IsUnit ((b.toMatrix b').map e).det := by
      have h1 : e (b.toMatrix b').det = ((b.toMatrix b').map e).det :=
        RingHom.map_det (e : K.E →+* L) _
      rw [← h1]
      exact (isUnit_map_iff e _).mpr (b.isUnit_det b')
    refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero _ hdet.ne_zero, ?_⟩
    rw [gram_of_sum K B L e c he β b b' (b.toMatrix b')]
    · rfl
    · intro j; rw [b.sum_toMatrix_smul_self]

end GlobalTheory.GramChange
