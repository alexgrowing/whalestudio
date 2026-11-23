import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemRelParabColEq
open GlobalTheory.PRep GlobalTheory.SmGL Matrix GlobalTheory.CellDetFirst
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.CellDetFirst

theorem sigmaC_mk_scalar : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (χ₁ χ₂ : kˣ →* ℂˣ) (u v : ℕ) (p : relParab k (colEq u v)) (w : ℂ ⊗[ℂ] ℂ),
    sigmaC χ₁ χ₂ u v p (Submodule.Quotient.mk w) =
    (((χ₂ * absPow k ((v : ℂ) / 2)) (GeneralLinearGroup.det (p.1 true)) *
      deltaHalf k (Two (Fin u) (Fin v))
        (leviProj k (two (stdSum (rfl : u + v = u + v))) ⟨p.1 false, (mem_relParab_colEq _).1 p.2⟩) *
      (χ₁ (GeneralLinearGroup.det (leviProj k (two (stdSum (rfl : u + v = u + v)))
          ⟨p.1 false, (mem_relParab_colEq _).1 p.2⟩ false)) *
        (χ₂ * absPow k (-(1 / 2))) (GeneralLinearGroup.det (leviProj k (two (stdSum (rfl : u + v = u + v)))
          ⟨p.1 false, (mem_relParab_colEq _).1 p.2⟩ true))) : ℂˣ) : ℂ) • Submodule.Quotient.mk w := by
  intro k _ _ _ _ χ₁ χ₂ u v p w
  have hb : ¬ (true < false) := by decide
  have m1 : modExp (fun i => Fin ((sizeFirst u v).1 i true)) true = 0 := by simp [modExp, Finset.sum_filter, sizeFirst, hb] <;> exact (Fintype.card_congr' rfl).trans (Fintype.card_fin _)
  have m2 : modExp (fun i => Fin ((sizeFirst u v).1 i true)) false = 1 := by simp [modExp, Finset.sum_filter, sizeFirst, hb] <;> exact (Fintype.card_congr' rfl).trans (Fintype.card_fin _)
  have m3 : modExp (fun i => Fin ((sizeFirst u v).1 i false)) true = -(u : ℤ) := by simp [modExp, Finset.sum_filter, sizeFirst, hb] <;> exact (Fintype.card_congr' rfl).trans (Fintype.card_fin _)
  have m4 : modExp (fun i => Fin ((sizeFirst u v).1 i false)) false = v := by simp [modExp, Finset.sum_filter, sizeFirst, hb] <;> exact (Fintype.card_congr' rfl).trans (Fintype.card_fin _)
  have m5 : modExp (fun j => Fin ((sizeFirst u v).1 true j)) true = -(v : ℤ) := by simp [modExp, Finset.sum_filter, sizeFirst, hb] <;> exact (Fintype.card_congr' rfl).trans (Fintype.card_fin _)
  have m6 : modExp (fun j => Fin ((sizeFirst u v).1 true j)) false = 1 := by simp [modExp, Finset.sum_filter, sizeFirst, hb] <;> exact (Fintype.card_congr' rfl).trans (Fintype.card_fin _)
  have m7 : modExp (fun j => Fin ((sizeFirst u v).1 false j)) true = -(u : ℤ) := by simp [modExp, Finset.sum_filter, sizeFirst, hb] <;> exact (Fintype.card_congr' rfl).trans (Fintype.card_fin _)
  have m8 : modExp (fun j => Fin ((sizeFirst u v).1 false j)) false = 0 := by simp [modExp, Finset.sum_filter, sizeFirst, hb] <;> exact (Fintype.card_congr' rfl).trans (Fintype.card_fin _)
  have m9 : modExp (Two (Fin u) (Fin v)) false = v := by simp [modExp, Finset.sum_filter]
  have m10 : modExp (Two (Fin u) (Fin v)) true = -(u : ℤ) := by simp [modExp, Finset.sum_filter]
  have hs : ∀ i j, swapBlocks k (fun i j => Fin ((sizeFirst u v).1 i j)) (relProj k (colEq u v) p) i j =
      relProj k (colEq u v) p j i := fun _ _ => rfl
  have e0 : GeneralLinearGroup.det (relProj k (colEq u v) p true false) = 1 := by
    haveI : IsEmpty (Fin ((sizeFirst u v).1 false true)) := ⟨fun x => Fin.elim0 x⟩
    ext
    simp [Matrix.det_isEmpty]
  have d00 : GeneralLinearGroup.det (relProj k (colEq u v) p false false) =
      GeneralLinearGroup.det (leviProj k (two (stdSum (rfl : u + v = u + v)))
        ⟨p.1 false, (mem_relParab_colEq _).1 p.2⟩ false) := by
    first | exact congrArg GeneralLinearGroup.det (relProj_colEq_ff p) | (rw [relProj_colEq_ff] <;> rfl)
  have d01 : GeneralLinearGroup.det (relProj k (colEq u v) p false true) =
      GeneralLinearGroup.det (leviProj k (two (stdSum (rfl : u + v = u + v)))
        ⟨p.1 false, (mem_relParab_colEq _).1 p.2⟩ true) := by
    first | exact congrArg GeneralLinearGroup.det (relProj_colEq_ft p) | (rw [relProj_colEq_ft] <;> rfl)
  rw [MonoidHom.comp_apply, twist_apply, MonoidHom.comp_apply, relJac_mk, rhoM_apply, Submodule.Quotient.mk_smul,
    smul_smul, smul_smul]
  congr 1
  simp only [← Units.val_mul]
  congr 1
  rw [relDeltaHalf_apply, relDeltaHalf_apply, Fintype.prod_bool, Fintype.prod_bool]
  simp only [deltaHalf_apply, Fintype.prod_bool, relEmb_apply, det_leviEmb, m1, m2, m3, m4, m5, m6, m7, m8, m9, m10, hs,
    e0, d00, d01, det_relProj_tt, map_one, mul_one, one_mul, map_mul, MonoidHom.mul_apply, Int.cast_zero, zero_div,
    absPow_zero, MonoidHom.one_apply, Int.cast_one, Int.cast_neg, Int.cast_natCast]
  simp only [neg_div, absPow_neg, MonoidHom.inv_apply, mul_inv, inv_inv]
  have key : ∀ (x y z q d f e : ℂˣ), x * y * (z * q) * (d * (f * e)) = f * z * (x * y) * (d * (e * q)) := by
    intro x y z q d f e
    ac_rfl
  exact key _ _ _ _ _ _ _

end GlobalTheory.CellDetFirst
