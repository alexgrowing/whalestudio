import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.FormsFiniteness.OrderedCechToCatCochainsOneApplyValueAtSubset
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.GenGlRelationsAndCommuteOfIsLie
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CapCommuteRtInfGL

open NumberField NumberField.mixedEmbedding Matrix MeasureTheory GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm UpperTheory.V.Af.Fin
open scoped TensorProduct
attribute [local instance 100] LieRing.ofAssociativeRing

private theorem semiconj_gen {R : Type} [CommRing R] [Algebra ℝ R] {ι : Type} [Fintype ι] {n : ℕ}
    {A : Type} [Ring A] [Algebra ℂ A] [Algebra ℝ A] [IsScalarTower ℝ ℂ A] (D : Idem R ι)
    (l : Matrix (Fin n) (Fin n) R →ₗ[ℝ] A) (T : A) (P Q : Matrix (Fin n) (Fin n) R)
    (h : ∀ X, T * l X = l (P * X * Q) * T) (τ : ι) (i j : Fin n) :
    T * gen D l τ i j = (∑ k, ∑ m, (D.ch τ (P k i) * D.ch τ (Q j m)) • gen D l τ k m) * T := by
  have ent : ∀ (k m : Fin n) (r : R), (P * Matrix.single i j r * Q) k m = P k i * Q j m * r := by
    intro k m r
    simp [Matrix.mul_apply, Matrix.single_apply, ite_and, Finset.sum_ite_eq, Finset.sum_ite_eq', ite_mul]
    ring
  have key : ∀ x : ℂ ⊗[ℝ] R, T * unitMap l i j x =
      (∑ k, ∑ m, unitMap l k m ((1 ⊗ₜ[ℝ] (P k i * Q j m)) * x)) * T := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul c r =>
      rw [unitMap_tmul, mul_smul_comm, h, Matrix.matrix_eq_sum_single (P * Matrix.single i j r * Q)]
      simp only [map_sum, Finset.sum_mul, Finset.smul_sum, Algebra.TensorProduct.tmul_mul_tmul, one_mul,
        unitMap_tmul, ent, smul_mul_assoc]
    | add x y hx hy =>
      simp only [map_add, mul_add, hx, hy, Finset.sum_add_distrib, add_mul]
  show T * unitMap l i j (D.e τ) = _
  rw [key]
  congr 1
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun m _ => ?_
  rw [D.mul_e, map_smul, map_mul]
  rfl

private theorem rtInf_lam {K : Type} [Field K] [NumberField K] {n : ℕ} (a : archGroup K n)
    (y : GL (Fin n) (mixedSpace K)) (hy : y = a.1) (X : Matrix (Fin n) (Fin n) (mixedSpace K)) :
    rtInf a * lam K n X = lam K n (y.val * X * (y⁻¹).val) * rtInf a := by
  subst hy
  apply LinearMap.ext
  intro φ
  simp only [Module.End.mul_apply, lam_apply]
  rw [uAction_rtInf, IsExpLieAlgebra.AdU_ι]
  congr 4
  apply Subtype.ext
  simp [IsExpLieAlgebra.AdLie, IsExpLieAlgebra.Ad, toLie, IsExpLieAlgebra.toLie, IsExpLieAlgebra.ofLie,
    mul_assoc]
  show (show ArchMatrix K n from X) = ((↑(↑a : (ArchMatrix K n)ˣ)⁻¹ : ArchMatrix K n)) *
    ((((↑a : (ArchMatrix K n)ˣ) : ArchMatrix K n) * ((show ArchMatrix K n from X) *
      ((↑(↑a : (ArchMatrix K n)ˣ)⁻¹ : ArchMatrix K n)))) * ((↑a : (ArchMatrix K n)ˣ) : ArchMatrix K n))
  simp only [mul_assoc, Units.inv_mul_cancel_left]
  exact (Units.inv_mul_cancel_right (show ArchMatrix K n from X) (a : (ArchMatrix K n)ˣ)).symm

theorem UpperTheory.capOp_commute_rightTranslation :
    ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) (ι : Type) [Fintype ι] (D : Idem (mixedSpace K) ι) (τ : ι) (u : ℂ) (a : archGroup K n), Commute (capOp D n τ u) (rtInf a) := by
  intro K _ _ n ι _ D τ u a
  let y : GL (Fin n) (mixedSpace K) := a.1
  let P : Matrix (Fin n) (Fin n) ℂ := (D.ch τ).mapMatrix y.val
  let Q : Matrix (Fin n) (Fin n) ℂ := (D.ch τ).mapMatrix (y⁻¹).val
  have hQP : Q * P = 1 := by
    simp only [Q, P]
    rw [← map_mul, Units.inv_mul, map_one]
  have hsemi := semiconj_gen D (lam K n) (rtInf a) y.val (y⁻¹).val
    (fun X => rtInf_lam a y rfl X) τ
  have hq := GlobalTheory.CapAdInv.qdet_semiconj (gen D (lam K n) τ) _ (rtInf a) hsemi u
  have hGl := (UpperTheory.gen_glRelations_and_commute_of_isLie (mixedSpace K) ι n _ D (lam K n) (isLie_lam K n)).1 τ
  have had := GlobalTheory.CapAdInv.qdet_ad (gen D (lam K n) τ) hGl P Q hQP u
  show Formalism.REAL.qdet (gen D (lam K n) τ) u * rtInf a = rtInf a * Formalism.REAL.qdet (gen D (lam K n) τ) u
  rw [hq]
  congr 1
  exact had.symm
