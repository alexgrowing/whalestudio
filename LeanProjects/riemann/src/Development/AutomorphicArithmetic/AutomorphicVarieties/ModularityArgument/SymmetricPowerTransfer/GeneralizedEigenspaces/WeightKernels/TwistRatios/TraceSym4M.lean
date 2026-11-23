import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.WeightKernels.GoodSet
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.WeightKernels.SymmetricFourthPowerMatrix

noncomputable section

open NumberField IsDedekindDomain ValuativeRel Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.SplitWeil
open UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Dict
open UpperTheory.V.W (Plc Lp)
open scoped Matrix

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem trace_sym4M {k : Type} [Field k] (g : Matrix (Fin 2) (Fin 2) k) :
    Matrix.trace (UpperTheory.V.Z.Sym.Ga.symmetricFourthPowerMatrix k g) = g.trace ^ 4 - 3 * g.trace ^ 2 * g.det + g.det ^ 2 := by
  simp only [UpperTheory.V.Z.Sym.Ga.symmetricFourthPowerMatrix, MonoidHom.coe_mk, OneHom.coe_mk, Matrix.trace, Matrix.diag,
    Fin.sum_univ_five, Fin.sum_univ_two, Matrix.det_fin_two, Matrix.of_apply, Matrix.cons_val',
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, Matrix.empty_val',
    Matrix.cons_val_fin_one, Matrix.head_cons, Matrix.head_fin_const]
  ring

theorem UpperTheory.V.Z.Sym.Ga.trSym4 :
    ∀ (k : Type) [Field k] (Γ : Type) [Group Γ] (ρ : Γ →* GL (Fin 2) k) (s : Γ), Ga.tr (Ga.sym4 ρ s) = Ga.uf (ρ s) ^ 2 + Ga.uf (ρ s) - 1 := by
  intro k _ Γ _ ρ s
  have hD : ((ρ s : GL (Fin 2) k) : Matrix (Fin 2) (Fin 2) k).det ≠ 0 :=
    ((ρ s).isUnit.map Matrix.detMonoidHom).ne_zero
  simp only [Ga.tr, Ga.uf, Ga.sym4, UpperTheory.V.Af.tw_val, Matrix.trace_smul, Units.coe_map,
    MonoidHom.coe_comp, Function.comp_apply, MonoidHom.coe_coe, trace_sym4M]
  simp only [MonoidHom.pow_apply, MonoidHom.inv_apply, MonoidHom.comp_apply,
    Matrix.GeneralLinearGroup.val_det_apply, Units.val_pow_eq_pow_val, Units.val_inv_eq_inv_val,
    smul_eq_mul]
  field_simp
  ring
