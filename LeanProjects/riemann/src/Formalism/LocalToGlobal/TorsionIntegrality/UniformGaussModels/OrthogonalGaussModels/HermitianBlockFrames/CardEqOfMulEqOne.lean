import Formalism.LocalToGlobal.TorsionIntegrality.UniformGaussModels.OrthogonalGaussModels.HermitianBlockFrames.InsSuccAbove

open Matrix

namespace Formalism.L2.Th1.Top.FrP.UnitaryGroupMassFormula.HermFrame.Jac
namespace JSetup

variable {K : Type*} [Field K] (S : JSetup K)

private theorem mulVec_comp_equiv_apply {ι : Type*} [Fintype ι] {m : ℕ} (Γ : Matrix ι ι K) (e : ι ≃ Fin m)
    (x : Fin m → K) (i : ι) :
    (Γ *ᵥ (x ∘ e)) i = (Γ.submatrix e.symm e.symm *ᵥ x) (e i) := by
  simp only [mulVec, dotProduct, submatrix_apply, Equiv.symm_apply_apply, Function.comp]
  exact Fintype.sum_equiv e _ _ (fun j => by simp)

private theorem vecMul_comp_equiv_apply {ι : Type*} [Fintype ι] {m : ℕ} (Γ : Matrix ι ι K) (e : ι ≃ Fin m)
    (x : Fin m → K) (j : ι) :
    ((x ∘ e) ᵥ* Γ) j = (x ᵥ* Γ.submatrix e.symm e.symm) (e j) := by
  simp only [vecMul, dotProduct, submatrix_apply, Equiv.symm_apply_apply, Function.comp]
  exact Fintype.sum_equiv e _ _ (fun i => by simp)

theorem jac {ι : Type*} [Fintype ι] [DecidableEq ι] (Γ : Matrix ι ι K) (hΓ : S.IntM Γ) (hH : S.Herm Γ)
    (hU : S.UM Γ) :
    ∃ (k : ℕ) (v : Fin k → ι → K), (∀ c, S.IntV (v c)) ∧
      (∀ c c', S.hf Γ (v c) (v c') = if c = c' then 1 else 0) ∧
      ∑ c, Matrix.vecMulVec (Γ *ᵥ v c) (S.cv (v c) ᵥ* Γ) = Γ := by
  classical
  set e : ι ≃ Fin (Fintype.card ι) := Fintype.equivFin ι with he
  have hU' : S.UM (Γ.submatrix e.symm e.symm) := by
    intro x hx hxd
    obtain ⟨x', hx', hxx'⟩ := hU (x ∘ e) (fun i => hx (e i)) (fun i => by
      rw [mulVec_comp_equiv_apply Γ e x i]; exact hxd (e i))
    refine ⟨x' ∘ e.symm, fun s => hx' (e.symm s), ?_⟩
    funext s
    have h1 := mulVec_comp_equiv_apply Γ e x (e.symm s)
    have h2 := mulVec_comp_equiv_apply Γ e (x' ∘ e.symm) (e.symm s)
    rw [Equiv.apply_symm_apply] at h1 h2
    have h3 : (x' ∘ e.symm) ∘ e = x' := by funext i; simp
    rw [h3] at h2
    rw [Pi.smul_apply, ← h1, ← h2, hxx', Pi.smul_apply]
  obtain ⟨k, v, hv, hort, hsum⟩ := S.jac_fin (Fintype.card ι) (Γ.submatrix e.symm e.symm)
    (fun s t => hΓ _ _) (fun s t => hH _ _) hU'
  have hconj : ∀ x : Fin (Fintype.card ι) → K, S.cv (x ∘ e) = S.cv x ∘ e := fun x => rfl
  refine ⟨k, fun c => v c ∘ e, fun c i => hv c (e i), fun c c' => ?_, ?_⟩
  · rw [← hort c c']
    simp only [hf, hconj, dotProduct]
    exact Fintype.sum_equiv e _ _ (fun i => by
      simp only [Function.comp, mulVec_comp_equiv_apply Γ e (v c') i])
  · ext i j
    have h := congrFun (congrFun hsum (e i)) (e j)
    simp only [Matrix.sum_apply, vecMulVec_apply, submatrix_apply, Equiv.symm_apply_apply] at h
    simp only [Matrix.sum_apply, vecMulVec_apply, hconj, mulVec_comp_equiv_apply Γ e _ i,
      vecMul_comp_equiv_apply Γ e _ j]
    exact h

end JSetup

theorem card_eq_of_mul_eq_one {K : Type*} [Field K] {n : Type*} [Fintype n] [DecidableEq n] {k : ℕ}
    (V : Matrix n (Fin k) K) (W : Matrix (Fin k) n K) (h1 : V * W = 1) (h2 : W * V = 1) :
    Fintype.card n = k := by
  have e : (Fin k → K) ≃ₗ[K] (n → K) :=
    LinearEquiv.ofLinear (Matrix.toLin' V) (Matrix.toLin' W)
      (by rw [← Matrix.toLin'_mul, h1, Matrix.toLin'_one])
      (by rw [← Matrix.toLin'_mul, h2, Matrix.toLin'_one])
  have h := e.finrank_eq
  simp only [Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at h
  omega

end Formalism.L2.Th1.Top.FrP.UnitaryGroupMassFormula.HermFrame.Jac
