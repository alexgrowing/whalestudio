import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.WeightKernels.GoodSet

noncomputable section

open NumberField IsDedekindDomain ValuativeRel Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.SplitWeil
open UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Dict
open UpperTheory.V.W (Plc Lp)
open scoped Matrix

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem infOfWeight_reflect_eq_weights (lam : DomWeight 2) : (infOfWeight lam).map (fun z => (((2 : ℕ) : ℂ) - 1) / 2 - z) = ({-lam.w 0, 1 - lam.w 1} : Multiset ℤ).map (fun k : ℤ => (k : ℂ)) := by
  simp only [infOfWeight, Multiset.map_map, Function.comp_def, Fin.univ_val_map]
  simp [List.ofFn_succ]
  rw [← Multiset.cons_coe, Multiset.coe_singleton]
  congr 2
  ring

theorem UpperTheory.V.Z.Sym.Ga.wtOf :
    ∀ (m : ℕ) (b : ℤ) (lam : DomWeight 2), ({b, b + m} : Multiset ℤ).map (fun k : ℤ => (k : ℂ)) = (infOfWeight lam).map (fun z => (((2 : ℕ) : ℂ) - 1) / 2 - z) → lam.w 0 - lam.w 1 = (m : ℤ) - 1 := by
  intro m b lam h
  rw [infOfWeight_reflect_eq_weights] at h
  have hz : ({b, b + m} : Multiset ℤ) = {-lam.w 0, 1 - lam.w 1} :=
    Multiset.map_injective Int.cast_injective h
  have hanti : lam.w 1 ≤ lam.w 0 := lam.anti (by decide)
  have hs := congrArg Multiset.sum hz
  simp at hs
  have hb : b ∈ ({-lam.w 0, 1 - lam.w 1} : Multiset ℤ) := by
    rw [← hz]; simp
  simp at hb
  rcases hb with hb | hb <;> omega
