import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.SignatureIntegrality.SignatureTorusFixedPoints.Contract
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.SignatureIntegrality.HodgeTateFromSandwich

noncomputable section

open ValuativeRel Matrix Polynomial GlobalTheory.SmGL GlobalTheory.SplitWeil UpperTheory.V.Hi UpperTheory.V.AlgebraTools UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Sig UpperTheory.V.Z.Sym.Loc UpperTheory.V.Z.Sym.Glob

theorem UpperTheory.V.Z.Sym.Sig.suppZ : UpperTheory.V.Z.Sym.Sig.SuppZ := by
  intro k _ _ _ _ V ω d hd g hg
  classical
  have hex : ∃ z, ((GeneralLinearGroup.scalar (Fin 2)) z)⁻¹ * g ∈ V.DC d := by
    by_contra hn
    exact hg (by unfold Lev.fZ; rw [dif_neg hn])
  obtain ⟨z, hz⟩ := hex
  obtain ⟨j, -, w, hw, e⟩ := contract k V 2 (MonoidHom.id _) (pres_id V 2) d hd _ hz
  obtain ⟨c, hc, rfl⟩ := hw
  rw [MonoidHom.id_apply] at e
  have hsc : (GeneralLinearGroup.scalar (Fin 2)) z = diagT k (Fin 2) (fun _ => z) := by
    ext i l
    rw [val_diagT]
    simp [Matrix.diagonal_apply, Matrix.scalar_apply]
  have hcomm : (GeneralLinearGroup.scalar (Fin 2)) z * j⁻¹ = j⁻¹ * (GeneralLinearGroup.scalar (Fin 2)) z := by
    have hzc : (GeneralLinearGroup.scalar (Fin 2)) z ∈ Subgroup.center (GL (Fin 2) k) := by
      rw [GeneralLinearGroup.center_eq_range_scalar]
      exact ⟨z, rfl⟩
    exact ((Subgroup.mem_center_iff.mp hzc) j⁻¹).symm
  refine ⟨j, z * c 0 * d 0, z * c 1 * d 1, ?_, ?_⟩
  · have hdg : dg ![z * c 0 * d 0, z * c 1 * d 1] =
        (GeneralLinearGroup.scalar (Fin 2)) z * (diagT k (Fin 2) c * dg d) := by
      rw [hsc]
      unfold dg
      rw [← map_mul, ← map_mul]
      congr 1
      funext i
      fin_cases i <;> simp [mul_assoc]
    rw [hdg, ← e]
    set S := (GeneralLinearGroup.scalar (Fin 2)) z
    rw [show S * (j⁻¹ * (S⁻¹ * g) * j) = (S * j⁻¹) * (S⁻¹ * g) * j by group, hcomm]
    group
  · have hid : z * c 0 * d 0 / (z * c 1 * d 1) / (d 0 / d 1) = c 0 / c 1 := by
      rw [div_div_eq_mul_div, div_eq_div_iff_mul_eq_mul]
      simp only [div_eq_mul_inv]
      ext
      simp only [Units.val_mul, Units.val_inv_eq_inv_val]
      field_simp
    rw [hid]
    exact div_mem (hc 0 (Set.mem_univ _)) (hc 1 (Set.mem_univ _))

end
