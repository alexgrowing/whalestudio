import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.GeometricLemmaFiltration
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HasFiniteLengthOfIsIrreducible
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.BernsteinUnitaryProductIrreducible
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SubSmulMemOfEquiv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.JacquetCharacteristicPolynomialRight
open GlobalTheory.PRep GlobalTheory.SmGL Matrix

noncomputable section

namespace GlobalTheory.DetProdCells

theorem cell_scalar_col_one {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (χ₁ χ₂ : kˣ →* ℂˣ) (u v : ℕ) (ϖ : kˣ) (B : SizeMatrix (Two (Fin (u + 1)) (Fin v)) (Two (Fin 1) (Fin (u + v))))
    (h00 : B.1 false false = 0) (h10 : B.1 true false = 1) (h11 : (B.1 true true : ℂ) = (v : ℂ) - 1)
    (f : ∀ i, (Σ j, Fin (B.1 i j)) ≃ Two (Fin (u + 1)) (Fin v) i)
    (g : ∀ j, (Σ i, Fin (B.1 i j)) ≃ Two (Fin 1) (Fin (u + v)) j) :
    cellFunctor f g ((extTensor (detRep (Fin (u + 1)) χ₁) (detRep (Fin v) χ₂)).comp
      (leviTwo k (Fin (u + 1)) (Fin v)).symm.toMonoidHom)
      (leviTwo k (Fin 1) (Fin (u + v)) (GeneralLinearGroup.scalar (Fin 1) ϖ, 1)) =
      (((χ₂ * absPow k ((1 - (v : ℂ)) / 2)) ϖ : ℂˣ) : ℂ) • LinearMap.id := by
  let s : Bool → kˣ := fun j => cond j 1 ϖ
  have hZ : ∀ j, (leviTwo k (Fin 1) (Fin (u + v)) (GeneralLinearGroup.scalar (Fin 1) ϖ, 1)) j =
      GeneralLinearGroup.scalar (Two (Fin 1) (Fin (u + v)) j) (s j) := by
    intro j
    cases j
    · rfl
    · exact (map_one (GeneralLinearGroup.scalar (n := Fin (u + v)) (R := k))).symm
  have hmem : leviTwo k (Fin 1) (Fin (u + v)) (GeneralLinearGroup.scalar (Fin 1) ϖ, 1) ∈ relParab k g := by
    intro j _
    rw [hZ j]
    exact GlobalTheory.ScalRight.scalar_mem_parab _ _
  have hc : ∀ x : Levi k (Two (Fin 1) (Fin (u + v))),
      x * leviTwo k (Fin 1) (Fin (u + v)) (GeneralLinearGroup.scalar (Fin 1) ϖ, 1) =
        leviTwo k (Fin 1) (Fin (u + v)) (GeneralLinearGroup.scalar (Fin 1) ϖ, 1) * x := by
    intro x
    funext j
    rw [Pi.mul_apply, Pi.mul_apply, hZ j]
    exact (GeneralLinearGroup.scalar_commute _ _).symm
  have hP : relProj k g ⟨_, hmem⟩ = fun j i => GeneralLinearGroup.scalar (Fin (B.1 i j)) (s j) := by
    funext j
    exact GlobalTheory.ScalRight.leviProj_eq_scalar (g j) (s j) _ (hZ j)
  refine GlobalTheory.ScalRight.relInd_eq_smul g _ _ hmem hc _ ?_
  rw [hP]
  have hdet : ∀ i, GeneralLinearGroup.det
      (relEmb k f (fun i j => GeneralLinearGroup.scalar (Fin (B.1 i j)) (s j)) i) = ϖ ^ B.1 i false := by
    intro i
    rw [relEmb_apply, det_leviEmb, Fintype.prod_bool]
    show GeneralLinearGroup.det (GeneralLinearGroup.scalar (Fin (B.1 i true)) 1) *
      GeneralLinearGroup.det (GeneralLinearGroup.scalar (Fin (B.1 i false)) ϖ) = _
    rw [GlobalTheory.ScalRight.det_scalar_gl, GlobalTheory.ScalRight.det_scalar_gl, one_pow, one_mul, Fintype.card_fin]
  have hJ := GlobalTheory.ScalRight.relJac_eq_smul (k := k) f
    ((extTensor (detRep (Fin (u + 1)) χ₁) (detRep (Fin v) χ₂)).comp (leviTwo k (Fin (u + 1)) (Fin v)).symm.toMonoidHom)
    (fun i j => GeneralLinearGroup.scalar (Fin (B.1 i j)) (s j))
    ((χ₁ (ϖ ^ B.1 false false) : ℂ) * (χ₂ (ϖ ^ B.1 true false) : ℂ))
    (by
      rw [MonoidHom.comp_apply, GlobalTheory.ScalRight.extTensor_detRep_eq]
      show ((χ₁ (GeneralLinearGroup.det (relEmb k f _ false)) : ℂ) *
        (χ₂ (GeneralLinearGroup.det (relEmb k f _ true)) : ℂ)) • LinearMap.id = _
      rw [hdet, hdet])
  show _ • relJac f _ (fun i j => GeneralLinearGroup.scalar (Fin (B.1 i j)) (s j)) = _
  rw [hJ, smul_smul]
  congr 1
  clear hJ hP hc hmem hZ hdet
  simp only [relDeltaHalf_apply, deltaHalf_apply, GlobalTheory.ScalRight.det_scalar_gl, Fintype.card_fin, Fintype.prod_bool]
  simp only [s, cond_true, cond_false, one_pow, map_one, GlobalTheory.ScalRight.modExp_bool_true,
    GlobalTheory.ScalRight.modExp_bool_false, one_mul, mul_one, h00, h10, pow_zero, pow_one]
  simp only [Int.cast_natCast, h11, Nat.cast_zero, neg_zero, Int.cast_zero, zero_div,
    GlobalTheory.ScalRight.absPow_zero_apply, Units.val_one, one_mul]
  rw [MonoidHom.mul_apply, show (1 - (v : ℂ)) / 2 = -(((v : ℂ) - 1) / 2) by ring, absPow_neg,
    MonoidHom.inv_apply, Units.val_mul, Units.val_inv_eq_inv_val, mul_comm]

theorem cellSecond_scalar : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (χ₁ χ₂ : kˣ →* ℂˣ) (u v : ℕ) (hv : 1 ≤ v) (ϖ : kˣ), ∃ (f : ∀ i, (Σ j, Fin ((GlobalTheory.DetProdCells.cellSecond u v hv).1 i j)) ≃ Two (Fin (u + 1)) (Fin v) i) (g : ∀ j, (Σ i, Fin ((GlobalTheory.DetProdCells.cellSecond u v hv).1 i j)) ≃ Two (Fin 1) (Fin (u + v)) j), ∀ w, cellFunctor f g ((extTensor (detRep (Fin (u + 1)) χ₁) (detRep (Fin v) χ₂)).comp (leviTwo k (Fin (u + 1)) (Fin v)).symm.toMonoidHom) (leviTwo k (Fin 1) (Fin (u + v)) (GeneralLinearGroup.scalar (Fin 1) ϖ, 1)) w = (((χ₂ * absPow k ((1 - (v : ℂ)) / 2)) ϖ : ℂˣ) : ℂ) • w := by
  intro k _ _ _ _ χ₁ χ₂ u v hv ϖ
  have h11 : ((cellSecond u v hv).1 true true : ℂ) = (v : ℂ) - 1 := by
    rw [show (cellSecond u v hv).1 true true = v - 1 from rfl, Nat.cast_sub hv, Nat.cast_one]
  exact ⟨(cellSecond u v hv).nonempty_rows.some, (cellSecond u v hv).nonempty_cols.some, fun w =>
    LinearMap.congr_fun (cell_scalar_col_one χ₁ χ₂ u v ϖ (cellSecond u v hv) rfl rfl h11 _ _) w⟩

end GlobalTheory.DetProdCells
