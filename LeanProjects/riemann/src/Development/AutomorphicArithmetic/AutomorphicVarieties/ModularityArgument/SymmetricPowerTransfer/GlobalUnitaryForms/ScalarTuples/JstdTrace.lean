import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GlobalUnitaryForms.HodgeTateFromSandwich
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.TraceFormulaEigenvalues.FormsFin
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.LocalOrbitCounts.DOrb
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.LocalOrbitCounts.GConj

open QuadraticAlgebra UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Loc UpperTheory.V.Z.Sym.Glob

private theorem jstd_trace {K : Type} [Field K] (τ : K) : (jstd τ ω).trace = τ := by
  simp [jstd, Matrix.trace_fin_two, Algebra.leftMulMatrix_eq_repr_mul, QuadraticAlgebra.basis_repr_apply,
    QuadraticAlgebra.basis, Module.Basis.coe_ofEquivFun]

private theorem toUnit_val {R : Type} [Monoid R] {x : R} (h : IsUnit x) : ((toUnit x : Rˣ) : R) = x := by
  simp [toUnit, h]

private theorem omega_unit {K : Type} [Field K] (τ : K) : IsUnit (ω : Etau K τ) := QuadraticAlgebra.isUnit_iff_norm_isUnit.mpr (by simp [QuadraticAlgebra.norm_def])

theorem UpperTheory.V.Z.Sym.Glob.locD :
    UpperTheory.V.Z.Sym.Glob.LocD := by
  intro O K _ _ _ _ _ Δ τ L hτ γ j hγ hj χ hχ z hz
  obtain ⟨j', hj'tr, hS, hK⟩ := dOrb O K Δ τ L hτ γ j hγ hj
  have hc := gConj O K Δ τ L hτ j' (jstd τ) hj'tr (jstd_trace τ)
  have hunr1 : Unr O (1 : Kˣ →* ℂˣ) := fun u => rfl
  have hzu : toUnit (1 + ω : Etau K τ) = z := by
    apply Units.ext
    rw [toUnit_val (by rw [← hz]; exact z.isUnit), hz]
  refine ⟨?_, ?_⟩
  · rw [← hc.2 1 hunr1]
    exact hS _ (toUnit_val (omega_unit τ))
  · rw [hzu, ← hc.2 χ hχ]
    exact hK χ hχ z
