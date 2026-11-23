import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousMapPFin
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DefiniteUnitaryClassSetFinite

open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC Formalism.UG Formalism.BasicNotions GlobalTheory.DefU

namespace GlobalTheory.DefU

theorem exists_finU_mul_infU : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (g : UA E n),
    ∃ k ∈ finU E n, ∃ x ∈ infU E n, g = k * x := by
  intro E _ _ _ n g
  let k : UA E n := ⟨finGL E n (GeneralLinearGroup.map (pFin E) g.1), ClassFin.finGL_mem_UA _ (ClassFin.cT_pFin g)⟩
  have hk : k ∈ finU E n := pInf_finGL _
  refine ⟨k, hk, k⁻¹ * g, ?_, (mul_inv_cancel_left k g).symm⟩
  change GeneralLinearGroup.map (pFin E) (k⁻¹ * g).1 = 1
  have h : GeneralLinearGroup.map (pFin E) k.1 = GeneralLinearGroup.map (pFin E) g.1 := pFin_finGL _
  rw [Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_inv, h, inv_mul_cancel]

end GlobalTheory.DefU
