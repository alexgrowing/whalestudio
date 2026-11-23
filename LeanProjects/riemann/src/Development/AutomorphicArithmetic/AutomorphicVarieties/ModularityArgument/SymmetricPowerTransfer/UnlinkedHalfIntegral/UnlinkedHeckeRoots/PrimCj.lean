import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.UnlinkedHalfIntegral.UnitFormC

namespace UpperTheory.V.Z.Sym.Unl

private theorem ker_cj {N : ℕ} (σ : ℂ ≃+* ℂ) (χ : DirichletCharacter ℂ N) :
    (cj σ χ).toUnitHom.ker = χ.toUnitHom.ker := by
  ext x
  simp only [MonoidHom.mem_ker, Units.ext_iff, MulChar.coe_toUnitHom, Units.val_one, cj, MulChar.ringHomComp_apply]
  exact map_eq_one_iff σ σ.injective

theorem primCj : PrimCj := by
  intro N _ χ σ hχ
  have key : ∀ d : ℕ, (cj σ χ).FactorsThrough d ↔ χ.FactorsThrough d := by
    intro d
    constructor
    · intro h
      rw [DirichletCharacter.factorsThrough_iff_ker_unitsMap h.dvd, ← ker_cj σ χ]
      exact (DirichletCharacter.factorsThrough_iff_ker_unitsMap h.dvd).mp h
    · intro h
      rw [DirichletCharacter.factorsThrough_iff_ker_unitsMap h.dvd, ker_cj σ χ]
      exact (DirichletCharacter.factorsThrough_iff_ker_unitsMap h.dvd).mp h
  have hc : (cj σ χ).conductor = χ.conductor := by
    unfold DirichletCharacter.conductor DirichletCharacter.conductorSet
    congr 1
    ext d
    exact key d
  unfold DirichletCharacter.IsPrimitive at hχ ⊢
  rw [hc]
  exact hχ

end UpperTheory.V.Z.Sym.Unl
