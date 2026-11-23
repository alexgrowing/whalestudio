import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.GelfandKazhdanDual
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.PolarizedPairLineIff
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FinGLMemOfPow

noncomputable section

open NumberField IsDedekindDomain Matrix Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.ContraPair GlobalTheory.ContraPair.Model

namespace GlobalTheory.Published.InvTransposeModel

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}

theorem rank_one (π : CuspSub E 1) : Paired π π invTOp := by
  obtain ⟨χ, rfl⟩ := RankOne.exists_eq_twist π
  exact paired_invTOp le_rfl χ

theorem eq_triv (π : CuspSub E 0) : π = CuspSub.triv E (Nat.zero_le 1) := by
  refine CuspSub.ext (((CuspSub.triv E (Nat.zero_le 1)).irred π.V (fun φ _ => ?_) π.stable).resolve_left π.ne_bot)
  refine Submodule.mem_span_singleton.2 ⟨φ.1 1, Subtype.ext (funext fun g => ?_)⟩
  change φ.1 1 * 1 = φ.1 g
  rw [mul_one, show g = 1 from Units.ext (Subsingleton.elim _ _)]

theorem rank_zero (π : CuspSub E 0) : Paired π π invTOp := by
  have h := paired_invTOp (E := E) (Nat.zero_le 1) 1
  rw [line, CuspSub.twist_one] at h
  rw [eq_triv π]
  exact h

theorem twist {π : CuspSub E a} (h : Paired π π invTOp) (χ : HChar E) : Paired (π.twist χ) (π.twist χ) invTOp := by
  obtain ⟨B, h1, h2, h3, h4, h5⟩ := h
  let T := π.toTwist χ
  refine ⟨B.compl₁₂ T.symm.toLinearMap T.symm.toLinearMap, fun φ h => ?_, fun ψ h => ?_, fun k φ ψ => ?_,
    fun k φ ψ => ?_, fun X φ ψ => ?_⟩
  · exact T.symm.map_eq_zero_iff.1 (h1 _ fun ψ => by simpa using h (T ψ))
  · exact T.symm.map_eq_zero_iff.1 (h2 _ fun φ => by simpa using h (T φ))
  all_goals
    obtain ⟨φ, rfl⟩ := T.surjective φ
    obtain ⟨ψ, rfl⟩ := T.surjective ψ
    simp only [T, CuspSub.op_toTwist, LinearMap.compl₁₂_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
  · have e := h3 k φ ψ
    simp only [invTOp] at e ⊢
    simp only [opAdd, zero_smul, add_zero, map_smul, LinearMap.smul_apply, e, smul_smul, opMul, chiDet,
      MonoidHom.comp_apply, det_finGL, det_invT, map_inv]
    simp
  · have e := h4 k φ ψ
    simp only [invTOp] at e ⊢
    simp only [opAdd, zero_smul, add_zero, map_smul, LinearMap.smul_apply, e, smul_smul, opMul, chiDet,
      MonoidHom.comp_apply, det_infGL, toUnits_barK, det_invT, map_inv]
    simp
  · have e := h5 X φ ψ
    have e2 : opAdd χ (invTOp (.lie X)) = -opAdd χ (.lie X) := by
      change dchi χ (-(Matrix.of X)ᵀ).trace = -dchi χ _
      rw [Matrix.trace_neg, Matrix.trace_transpose, map_neg]
    have e3 : opMul χ (invTOp (.lie X)) = 1 := rfl
    have e4 : opMul χ (.lie X) = 1 := rfl
    rw [e2, e3, e4]
    simp only [Units.val_one, one_smul, map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul]
    linear_combination e

theorem not_paired_id {s : ℂ} (hs : s ≠ 0) :
    ¬ Paired (line le_rfl (CuspRep.Model.absC E s)) (line le_rfl (CuspRep.Model.absC E s)) id := fun h => by
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  have h3 := ((paired_line_iff _ _ _ _).1 h).2.2
  have h4 : ∀ z, dchi (CuspRep.Model.absC E s) z = 0 := fun z => by
    have := h3 fun _ _ => z
    simp only [id, sc, opTriv, opAdd, mul_zero, zero_add, Matrix.trace, Fin.sum_univ_one, Matrix.diag,
      Matrix.of_apply] at this
    linear_combination this / 2
  have := CuspRep.Model.expo_absC s τ
  rw [expo, h4, h4] at this
  exact hs (by simpa using this.symm)

omit [IsTotallyComplex E] in

theorem bracket (X Y : Matrix (Fin a) (Fin a) (Cinf E)) :
    -(X * Y - Y * X)ᵀ = (-Xᵀ) * (-Yᵀ) - (-Yᵀ) * (-Xᵀ) := by
  simp only [Matrix.transpose_sub, Matrix.transpose_mul, neg_mul_neg, neg_sub]

end GlobalTheory.Published.InvTransposeModel

end
