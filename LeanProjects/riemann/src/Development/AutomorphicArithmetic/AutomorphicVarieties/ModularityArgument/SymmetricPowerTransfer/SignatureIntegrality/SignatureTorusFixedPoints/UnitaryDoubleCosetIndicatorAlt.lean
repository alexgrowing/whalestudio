import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.SignatureIntegrality.SignatureTorusFixedPoints.Contract
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.SignatureIntegrality.SignatureTorusFixedPoints.ThFacts
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.SignatureIntegrality.HodgeTateFromSandwich

noncomputable section

open ValuativeRel Matrix Polynomial GlobalTheory.SmGL GlobalTheory.SplitWeil UpperTheory.V.Hi UpperTheory.V.AlgebraTools UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Sig UpperTheory.V.Z.Sym.Loc UpperTheory.V.Z.Sym.Glob

theorem UpperTheory.V.Z.Sym.Sig.supp0 : UpperTheory.V.Z.Sym.Sig.Supp0 := by
  intro k _ _ _ _ V d hd g hg
  have hmem : g * (Phi k)⁻¹ ∈ V.DC d := by
    by_contra h
    exact hg (by simp [Lev.unitaryDoubleCosetIndicator, h])
  obtain ⟨hP, -, -, -, -, -, hcomm⟩ := thFacts k V
  obtain ⟨j, -, s, hs, hjs⟩ := contract k V 3 (th' k) hP d hd _ hmem
  obtain ⟨t, ht, rfl⟩ := Subgroup.mem_map.mp hs
  refine ⟨j, t 0 * d 0, t 1 * d 1, t 2 * d 2, ?_, ?_⟩
  · have h1 : dg ![t 0 * d 0, t 1 * d 1, t 2 * d 2] = diagT k (Fin 3) t * dg d := by
      rw [dg, ← map_mul]
      congr 1
      funext i
      fin_cases i <;> rfl
    rw [h1, ← hjs]
    have h2 : th' k j * Phi k = Phi k * th k 3 j := hcomm j
    symm
    calc j * (j⁻¹ * (g * (Phi k)⁻¹) * th' k j) * Phi k * (th k 3 j)⁻¹
        = g * (Phi k)⁻¹ * (th' k j * Phi k) * (th k 3 j)⁻¹ := by group
      _ = g := by rw [h2]; group
  · have h3 : t 0 * d 0 / (t 2 * d 2) / (d 0 / d 2) = t 0 / t 2 := by
      rw [mul_div_mul_comm, mul_div_cancel_right]
    rw [h3]
    exact div_mem (ht 0 trivial) (ht 2 trivial)

end
