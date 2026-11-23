import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnivOfNotLinearIndependent
open Matrix Formalism.IndefR.Datum GlobalTheory.ExportSeries

namespace GlobalTheory

theorem dU_eq_const_mul_det_topL_translate :
  ∀ (k : Type) [Field k] (r n : ℕ) (β : DetBases k r n) (U : Planes k r n),
  ∃ (g : GL (Fin n) k) (c : kˣ), ∀ y : Matrix (Fin r) (Fin n) k,
    dU β U y = (c : k) * (topL r (y * (g : Matrix (Fin n) (Fin n) k))).det := by
  intro k _ r n β U
  have hrn : r ≤ n := by have := U.2; omega
  let b := Module.finBasisOfFinrankEq k _ (finrank_quot U)
  have hU : Module.finrank k U.1 = n - r := by have := U.2; omega
  let bU := Module.finBasisOfFinrankEq k U.1 hU
  obtain ⟨lam, hlam⟩ := LinearMap.exists_extend (bU.equivFun.toLinearMap)
  let φ : (Fin n → k) →ₗ[k] (Fin n → k) := LinearMap.pi fun j =>
    if h : j.val < r then (LinearMap.proj (⟨j.val, h⟩ : Fin r)) ∘ₗ b.equivFun.toLinearMap ∘ₗ U.1.mkQ
    else (LinearMap.proj (⟨j.val - r, by have := j.2; omega⟩ : Fin (n - r))) ∘ₗ lam
  have hφ1 : ∀ v (i : Fin r), φ v ⟨i.val, by omega⟩ = b.repr (U.1.mkQ v) i := by
    intro v i
    simp [φ, i.2]
  have hφ2 : ∀ v (i : Fin (n - r)), φ v ⟨r + i.val, by omega⟩ = lam v i := by
    intro v i
    simp [φ]
  have hφ : Function.Injective φ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro v hv
    have h1 : U.1.mkQ v = 0 := by
      apply b.repr.injective
      ext i
      have := hφ1 v i
      rw [hv] at this
      simpa using this.symm
    have hvU : v ∈ U.1 := by simpa using h1
    have h2 : bU.equivFun ⟨v, hvU⟩ = 0 := by
      have e : lam v = bU.equivFun ⟨v, hvU⟩ := by
        have := LinearMap.congr_fun hlam ⟨v, hvU⟩
        simpa using this
      rw [← e]
      ext i
      have := hφ2 v i
      rw [hv] at this
      simpa using this.symm
    have : (⟨v, hvU⟩ : U.1) = 0 := bU.equivFun.injective (by rw [h2, map_zero])
    simpa using congrArg Subtype.val this

  let ψ := LinearEquiv.ofInjectiveEndo φ hφ
  let A : Matrix (Fin n) (Fin n) k := (LinearMap.toMatrix' φ)ᵀ
  let B : Matrix (Fin n) (Fin n) k := (LinearMap.toMatrix' ψ.symm.toLinearMap)ᵀ
  have hAB : A * B = 1 := by
    have hc : ψ.symm.toLinearMap ∘ₗ φ = LinearMap.id := by
      refine LinearMap.ext fun v => ?_
      show ψ.symm (ψ v) = v
      exact ψ.symm_apply_apply v
    simp only [A, B, ← transpose_mul, ← LinearMap.toMatrix'_comp, hc, LinearMap.toMatrix'_id, transpose_one]
  have hBA : B * A = 1 := by
    have hc : φ ∘ₗ ψ.symm.toLinearMap = LinearMap.id := by
      refine LinearMap.ext fun v => ?_
      show ψ (ψ.symm v) = v
      exact ψ.apply_symm_apply v
    simp only [A, B, ← transpose_mul, ← LinearMap.toMatrix'_comp, hc, LinearMap.toMatrix'_id, transpose_one]
  let g : GL (Fin n) k := ⟨A, B, hAB, hBA⟩
  have hb : β.form U b ≠ 0 := fun h0 => β.ne U (by rw [(β.form U).eq_smul_basis_det b, h0, zero_smul])
  refine ⟨g, Units.mk0 _ hb, fun y => ?_⟩
  have key : ∀ i j, (y * A) i j = φ (y.row i) j := by
    intro i j
    rw [← congrFun (LinearMap.toMatrix'_mulVec φ (y.row i)) j]
    simp [A, Matrix.mul_apply, Matrix.mulVec, dotProduct, mul_comm, Matrix.row]
  have ht : topL r (y * (g : Matrix (Fin n) (Fin n) k)) = (b.toMatrix fun i => U.1.mkQ (y.row i))ᵀ := by
    ext i j
    have hj : j.val < n := by omega
    have e1 : topL r (y * (g : Matrix (Fin n) (Fin n) k)) i j = (y * A) i ⟨j.val, hj⟩ := by
      simp [topL, hj, g]
    rw [e1, key, hφ1 (y.row i) j, transpose_apply, Module.Basis.toMatrix_apply]
  rw [ht, det_transpose, ← Module.Basis.det_apply, dU]
  conv_lhs => rw [(β.form U).eq_smul_basis_det b]
  rfl

end GlobalTheory
