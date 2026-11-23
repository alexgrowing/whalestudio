import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BasisApply
open NumberField
open scoped TensorProduct

namespace GlobalTheory.UnitaryStd

theorem form_basis_basis {E : Type} [Field E] [NumberField E] {r : ℕ} (ρ : 𝓞 E →+* Matrix (Fin r) (Fin r) ℤ)
    (g : ℕ) (S : Matrix (Fin r) (Fin r) ℤ) (i j : Fin r) (a c : Fin g ⊕ Fin g) :
    form ρ g S (basis ρ g (j, c)) (basis ρ g (i, a)) =
      S j i * (Matrix.J (Fin g) ℤ) a c := by
  rw [form_apply, Matrix.J]
  simp only [basis_apply, dotProduct]
  rcases a with k | k <;> rcases c with l | l <;>
    simp [Pi.single_apply, Prod.ext_iff, Matrix.one_apply, Finset.sum_ite_eq, Finset.sum_ite_eq', eq_comm]
  all_goals simp [ite_and, Finset.mul_sum, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.sum_ite_irrel, mul_ite]
  all_goals (split_ifs <;> simp_all)

theorem toMatrix_basis_dualBasis_form {E : Type} [Field E] [NumberField E] {r : ℕ} (ρ : 𝓞 E →+* Matrix (Fin r) (Fin r) ℤ)
    (g : ℕ) (S : Matrix (Fin r) (Fin r) ℤ) :
    LinearMap.toMatrix (basis ρ g) (basis ρ g).dualBasis (form ρ g S) =
      Matrix.kroneckerMap (· * ·) S.transpose (Matrix.J (Fin g) ℤ) := by
  ext ⟨i, a⟩ ⟨j, c⟩
  rw [LinearMap.toMatrix_apply, Module.Basis.dualBasis_repr, form_basis_basis]
  rfl

theorem form_bijective_of_unimodular : ∀ {E : Type} [Field E] [NumberField E] {r : ℕ} (ρ : 𝓞 E →+* Matrix (Fin r) (Fin r) ℤ)
    (g : ℕ) (S : Matrix (Fin r) (Fin r) ℤ), IsUnit S.det → Function.Bijective (GlobalTheory.UnitaryStd.form ρ g S) := by
  intro E _ _ r ρ g S hS
  set b := basis ρ g
  set M := LinearMap.toMatrix b b.dualBasis (form ρ g S) with hMdef
  have hM : IsUnit M.det := by
    rw [hMdef, toMatrix_basis_dualBasis_form, Matrix.det_kronecker, Matrix.det_transpose]
    exact (hS.pow _).mul ((Matrix.isUnit_det_J (Fin g) ℤ).pow _)
  have h1 : M * M⁻¹ = 1 := Matrix.mul_nonsing_inv M hM
  have h2 : M⁻¹ * M = 1 := Matrix.nonsing_inv_mul M hM
  have hf : form ρ g S = Matrix.toLin b b.dualBasis M := by rw [hMdef, Matrix.toLin_toMatrix]
  set Ψ := Matrix.toLin b.dualBasis b M⁻¹
  have hl : ∀ x, Ψ (form ρ g S x) = x := fun x => by
    rw [hf, ← LinearMap.comp_apply, ← Matrix.toLin_mul, h2, Matrix.toLin_one, LinearMap.id_apply]
  have hr : ∀ f, form ρ g S (Ψ f) = f := fun f => by
    rw [hf, ← LinearMap.comp_apply, ← Matrix.toLin_mul, h1, Matrix.toLin_one, LinearMap.id_apply]
  exact ⟨Function.LeftInverse.injective hl, Function.RightInverse.surjective hr⟩

end GlobalTheory.UnitaryStd
