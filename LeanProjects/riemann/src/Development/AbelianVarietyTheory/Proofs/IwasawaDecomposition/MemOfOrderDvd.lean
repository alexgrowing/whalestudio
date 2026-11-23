import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FixedCoefficientFieldInComplex
import Development.AbelianVarietyTheory.Definitions.HeightFunctions.JointQ
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CmQuadraticFormEqAlternatingForm
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsRationalUnitaryDeterminantMapRationalUnitaryTo
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousOfCongSet
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeCharacterFiniteIdeleValueMemFieldStatement

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Host GlobalTheory.NT GlobalTheory.Mem GlobalTheory.Mem.Fld GlobalTheory.FieldSize
open scoped IntermediateField

namespace GlobalTheory.Mem.ValFin

theorem locInf_eq_one {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] (χ : HChar E) {n : ℕ} (hn : 0 < n)
    (h : χ.OrderDvd n) (w : InfinitePlace E) (x : (w.Completion)ˣ) : χ.1 (ReciprocityTheory.Neutral.Bridge.HCFR.infIdele E w x) = 1 := by
  let e := InfinitePlace.Completion.ringEquivComplexOfIsComplex (IsTotallyComplex.isComplex w)
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq (e x) hn
  have hz' : (e.symm z) ^ n = x := by rw [← map_pow, hz, e.symm_apply_apply]
  have h0 : e.symm z ≠ 0 := fun h0 => x.ne_zero (by rw [← hz', h0, zero_pow hn.ne'])
  have hx : x = Units.mk0 _ h0 ^ n := Units.ext hz'.symm
  rw [hx, map_pow, map_pow]
  exact congrArg (fun χ : HChar E => χ.1 (ReciprocityTheory.Neutral.Bridge.HCFR.infIdele E w (Units.mk0 _ h0))) h

theorem inf_eq_one {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] (χ : HChar E) {n : ℕ} (hn : 0 < n)
    (h : χ.OrderDvd n) (k : Eˣ) : χ.inf k = 1 := by
  show χ.1 (infDiag k) = 1
  rw [infDiag, MonoidHom.finset_prod_apply, map_prod]
  exact Finset.prod_eq_one fun w _ => locInf_eq_one χ hn h w _

theorem mem_of_orderDvd : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (χ : HChar E) (M : IntermediateField ℚ ℂ), (∃ n : ℕ, 0 < n ∧ χ.OrderDvd n) → valueField χ 0 ≤ M → ∀ x, ((χ.1 x : ℂˣ) : ℂ) ∈ M := by
  intro E _ _ _ χ M hn hM x
  obtain ⟨n, hn0, hord⟩ := hn
  have hinf : ∀ k : Eˣ, ((χ.inf k : ℂˣ) : ℂ) ∈ M := fun k => by
    rw [inf_eq_one χ hn0 hord k, Units.val_one]
    exact one_mem M
  rw [← GlobalTheory.Mem.ReadEx.map_finPartI hn0 hord x]
  exact GlobalTheory.T.heckeCharacter_finiteIdele_value_mem_field E χ M hM hinf (GlobalTheory.Mem.Chr.finPartI E x) fun w => by
    rw [GlobalTheory.Mem.Chr.finPartI_fst]; rfl

end GlobalTheory.Mem.ValFin

end
