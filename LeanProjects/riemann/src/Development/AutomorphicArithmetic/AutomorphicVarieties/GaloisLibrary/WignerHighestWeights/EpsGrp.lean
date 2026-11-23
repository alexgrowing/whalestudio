import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.WignerHighestWeights.IsAlgIsoRefl
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DualInfinitesimalCharacterRegular

open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.AlgRepEndIrreducible
open scoped TensorProduct

private def outL {n : ℕ} (w : Fin n → ℂ) : (Fin n → ℂ) →ₗ[ℂ] Matrix (Fin n) (Fin n) ℂ where
  toFun u := vecMulVec u w
  map_add' u u' := by ext; simp [vecMulVec_apply, add_mul]
  map_smul' c u := by ext; simp [vecMulVec_apply, mul_assoc]

private def outR {n : ℕ} (u : Fin n → ℂ) : (Fin n → ℂ) →ₗ[ℂ] Matrix (Fin n) (Fin n) ℂ where
  toFun w := vecMulVec u w
  map_add' w w' := by ext; simp [vecMulVec_apply, mul_add]
  map_smul' c w := by ext; simp [vecMulVec_apply, mul_left_comm]

private theorem eps_left_mul_eq_det_smul {M : Type} [AddCommGroup M] [Module ℂ M] {n : ℕ}
    (μ : MultilinearMap ℂ (fun _ : Fin n => Matrix (Fin n) (Fin n) ℂ) M) (g : Matrix (Fin n) (Fin n) ℂ) :
    eps (fun x => μ fun i => g * x i) = g.det • eps μ := by
  have hs : ∀ a b : Fin n, g * single a b (1 : ℂ) = ∑ c, g c a • single c b (1 : ℂ) := by
    intro a b
    ext i j
    by_cases hbj : b = j <;> simp [Matrix.mul_apply, Matrix.single_apply, Matrix.sum_apply, hbj]
  have hdet : ∀ c : Fin n → Fin n, ∑ σ : Equiv.Perm (Fin n),
      ((Equiv.Perm.sign σ : ℤ) : ℂ) * ∏ k, g (c k) (σ k) = (g.submatrix c id).det := by
    intro c
    rw [← Matrix.det_transpose, Matrix.det_apply']
    rfl
  have hsum : ∀ w : (Fin n → Fin n) → M, ∑ c, (g.submatrix c id).det • w c =
      ∑ α : Equiv.Perm (Fin n), (((Equiv.Perm.sign α : ℤ) : ℂ) * g.det) • w α := by
    intro w
    rw [← Finset.sum_subset (Finset.subset_univ
      (Finset.univ.image (fun α : Equiv.Perm (Fin n) => (⇑α : Fin n → Fin n))))]
    · rw [Finset.sum_image (fun α _ β _ h => Equiv.coe_fn_injective h)]
      refine Finset.sum_congr rfl fun α _ => ?_
      rw [Matrix.det_permute]
    · intro c _ hc
      have hni : ¬ Function.Injective c := by
        intro hinj
        apply hc
        exact Finset.mem_image.mpr
          ⟨Equiv.ofBijective c (Finite.injective_iff_bijective.mp hinj), Finset.mem_univ _, rfl⟩
      simp only [Function.Injective, not_forall] at hni
      obtain ⟨i, j, hij, hne⟩ := hni
      rw [Matrix.det_zero_of_row_eq hne (by ext k; simp [hij]), zero_smul]
  simp only [eps, Finset.smul_sum]
  refine Finset.sum_congr rfl fun τ _ => ?_
  have hμ : ∀ σ : Equiv.Perm (Fin n), μ (fun i => g * units σ τ i) =
      ∑ c : Fin n → Fin n, (∏ k, g (c k) (σ k)) • μ (fun k => single (c k) (τ k) (1 : ℂ)) := by
    intro σ
    simp only [units, hs]
    rw [MultilinearMap.map_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [MultilinearMap.map_smul_univ]
  have hc : ∀ c : Fin n → Fin n, ∑ σ : Equiv.Perm (Fin n),
      ((Equiv.Perm.sign τ : ℤ) * (Equiv.Perm.sign σ : ℤ)) • (∏ k, g (c k) (σ k)) •
        μ (fun k => single (c k) (τ k) (1 : ℂ)) =
      ((Equiv.Perm.sign τ : ℤ) : ℂ) • ((g.submatrix c id).det • μ (fun k => single (c k) (τ k) (1 : ℂ))) := by
    intro c
    simp only [← Int.cast_smul_eq_zsmul ℂ, smul_smul, ← Finset.sum_smul]
    congr 1
    rw [← hdet c, Finset.mul_sum]
    refine Finset.sum_congr rfl fun σ _ => ?_
    push_cast
    ring
  simp only [hμ, Finset.smul_sum]
  rw [Finset.sum_comm, Finset.sum_congr rfl fun c _ => hc c, ← Finset.smul_sum, hsum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  simp only [← Int.cast_smul_eq_zsmul ℂ, smul_smul]
  congr 1
  push_cast
  ring

theorem UpperTheory.V.AlgRepEndIrreducible.epsGrp :
    ∀ (M : Type) [AddCommGroup M] [Module ℂ M] (n : ℕ) (μ : MultilinearMap ℂ (fun _ : Fin n => Matrix (Fin n) (Fin n) ℂ) M) (g g' : Matrix (Fin n) (Fin n) ℂ), g' * g = 1 →
      eps (fun x => μ fun i => g * x i * g') = eps μ := by
  intro M _ _ n μ g g' h
  have hT : ∀ ν : (Fin n → Matrix (Fin n) (Fin n) ℂ) → M, eps (fun x => ν fun i => (x i)ᵀ) = eps ν := by
    intro ν
    simp only [eps, units, Matrix.transpose_single]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun τ _ => Finset.sum_congr rfl fun σ _ => ?_
    rw [mul_comm]
    rfl
  have e1 : eps (fun x => μ fun i => g * x i * g') = g.det • eps (fun x => μ fun i => x i * g') :=
    eps_left_mul_eq_det_smul (μ.compLinearMap (fun _ => LinearMap.mulRight ℂ g')) g
  have e2 : eps (fun x => μ fun i => (g'ᵀ * x i)ᵀ) = g'ᵀ.det • eps (fun x => μ fun i => (x i)ᵀ) :=
    eps_left_mul_eq_det_smul (μ.compLinearMap
      (fun _ => (Matrix.transposeLinearEquiv (Fin n) (Fin n) ℂ ℂ).toLinearMap)) g'ᵀ
  simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.det_transpose, hT] at e2
  have e3 : eps (fun x => μ fun i => x i * g') = g'.det • eps μ := by
    rw [← hT (fun x => μ fun i => x i * g')]
    exact e2
  rw [e1, e3, smul_smul, mul_comm, ← Matrix.det_mul, h, Matrix.det_one, one_smul]
