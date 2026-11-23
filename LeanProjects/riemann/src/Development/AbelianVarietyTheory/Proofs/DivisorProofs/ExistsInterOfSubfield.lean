import Mathlib
import Formalism.LocalToGlobal.UnitaryNorms.CharExVal
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeCharacterFiniteIdeleValueMemField
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUnitaryRationalInfTypeSubgroupAndInfTypeUnique

noncomputable section

open NumberField IsDedekindDomain Formalism.L2.Host

namespace GlobalTheory.HeckeLocVals

def embField (E : Type) [Field E] [NumberField E] : IntermediateField ℚ ℂ :=
  ⨆ ψ : E →+* ℂ, ψ.toRatAlgHom.fieldRange

variable {E : Type} [Field E] [NumberField E]

instance embField_fd : FiniteDimensional ℚ (embField E) := by
  haveI : ∀ ψ : E →+* ℂ, FiniteDimensional ℚ ψ.toRatAlgHom.fieldRange := fun ψ =>
    ψ.toRatAlgHom.equivFieldRange.toLinearEquiv.finiteDimensional
  exact IntermediateField.finiteDimensional_iSup_of_finite

theorem emb_mem (ψ : E →+* ℂ) (k : E) : ψ k ∈ embField E :=
  le_iSup (fun ψ : E →+* ℂ => ψ.toRatAlgHom.fieldRange) ψ ⟨k, rfl⟩

theorem inf_mem_of_even {I : Type} [Fintype I] {φ : I → E →+* ℂ} {c : I → ℤ} {χ : HChar E}
    (h : χ.HasInf φ (fun i => 2 * c i)) (k : Eˣ) : ((χ.inf k : ℂˣ) : ℂ) ∈ embField E := by
  rw [h k]
  refine prod_mem fun i _ => ?_
  have h0 : φ i (k : E) ≠ 0 := by simp
  rw [zpow_mul, show (2 : ℤ) = ((2 : ℕ) : ℤ) from rfl, zpow_natCast, GlobalTheory.HalfIntChars.unit_sq _ h0]
  exact zpow_mem (div_mem (emb_mem _ _) (emb_mem ((starRingEnd ℂ).comp (φ i)) (k : E))) _

theorem exists_inter_of_subfield (C : Subfield ℂ) [FiniteDimensional ℚ C] :
    ∃ M : IntermediateField ℚ ℂ, FiniteDimensional ℚ M ∧ (C : Set ℂ) ⊆ M := by
  let M : IntermediateField ℚ ℂ := C.toIntermediateField fun x => by simpa using SubfieldClass.ratCast_mem C x
  let e : C ≃ₗ[ℚ] M :=
    { toFun := fun x => ⟨x.1, x.2⟩
      invFun := fun x => ⟨x.1, x.2⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun q x => Subtype.ext (by simp [Rat.smul_def])
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  exact ⟨M, e.finiteDimensional, fun _ h => h⟩

end GlobalTheory.HeckeLocVals

namespace GlobalTheory.HeckeLocVals

variable {E : Type} [Field E] [NumberField E]

theorem zpow_fsum {G : Type} [CommGroup G] (a : G) {ι : Type} (s : Finset ι) (f : ι → ℤ) :
    a ^ (∑ i ∈ s, f i) = ∏ i ∈ s, a ^ f i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih => rw [Finset.sum_insert hj, Finset.prod_insert hj, zpow_add, ih]

theorem algType_of_even {I : Type} [Fintype I] {φ : I → E →+* ℂ} {c : I → ℤ} {χ : HChar E}
    (h : χ.HasInf φ (fun i => 2 * c i)) : ∃ m : (E →+* ℂ) → ℤ, ∀ k : Eˣ,
      ((χ.inf k : ℂˣ) : ℂ) * ∏ ψ : E →+* ℂ, ((‖ψ (k : E)‖ : ℝ) : ℂ) ^ (((0 : ℝ)) : ℂ) = ∏ ψ : E →+* ℂ, ψ (k : E) ^ m ψ := by
  classical
  refine ⟨fun ψ => ∑ i, ((if φ i = ψ then c i else 0) - (if (starRingEnd ℂ).comp (φ i) = ψ then c i else 0)), fun k => ?_⟩
  simp only [Complex.ofReal_zero, Complex.cpow_zero, Finset.prod_const_one, mul_one]
  rw [h k]
  let u : (E →+* ℂ) → ℂˣ := fun ψ => Units.mk0 (ψ (k : E)) (by simp)
  have hu : ∀ ψ (n : ℤ), ψ (k : E) ^ n = ((u ψ ^ n : ℂˣ) : ℂ) := fun ψ n => by
    rw [Units.val_zpow_eq_zpow_val]; rfl
  have hL : ∀ i, (φ i (k : E) / ((‖φ i (k : E)‖ : ℝ) : ℂ)) ^ (2 * c i) =
      ((u (φ i) ^ c i * (u ((starRingEnd ℂ).comp (φ i)) ^ c i)⁻¹ : ℂˣ) : ℂ) := fun i => by
    rw [zpow_mul, show (2 : ℤ) = ((2 : ℕ) : ℤ) from rfl, zpow_natCast, GlobalTheory.HalfIntChars.unit_sq _ (by simp), div_zpow]
    rw [Units.val_mul, Units.val_inv_eq_inv_val, ← hu, ← hu, div_eq_mul_inv]
    rfl
  simp_rw [hL, hu]
  rw [← Units.coe_prod, ← Units.coe_prod]
  congr 1
  symm
  rw [Finset.prod_congr rfl fun ψ _ => (zpow_fsum (u ψ) Finset.univ _).trans (Finset.prod_congr rfl fun i _ => zpow_sub (u ψ) _ _),
    Finset.prod_comm]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [Finset.prod_mul_distrib, Finset.prod_inv_distrib]
  have e1 : ∏ ψ : E →+* ℂ, u ψ ^ (if φ i = ψ then c i else 0) = u (φ i) ^ c i := by
    rw [Finset.prod_eq_single (φ i) (fun ψ _ hψ => by rw [if_neg (Ne.symm hψ), zpow_zero]) (by simp)]
    simp
  have e2 : ∏ ψ : E →+* ℂ, u ψ ^ (if (starRingEnd ℂ).comp (φ i) = ψ then c i else 0) =
      u ((starRingEnd ℂ).comp (φ i)) ^ c i := by
    rw [Finset.prod_eq_single ((starRingEnd ℂ).comp (φ i)) (fun ψ _ hψ => by rw [if_neg (Ne.symm hψ), zpow_zero]) (by simp)]
    simp
  rw [e1, e2]

theorem locVals_of_even {I : Type} [Fintype I] {φ : I → E →+* ℂ} {c : I → ℤ} {χ : HChar E}
    (h : χ.HasInf φ (fun i => 2 * c i)) :
    ∃ M : IntermediateField ℚ ℂ, FiniteDimensional ℚ M ∧ ∀ v x, ((χ.loc v x : ℂˣ) : ℂ) ∈ M := by
  obtain ⟨m, hm⟩ := algType_of_even h
  obtain ⟨C, hC, hv⟩ := CharEx.algValsFin E χ 0 m hm
  obtain ⟨C', hC', hCC⟩ := exists_inter_of_subfield C
  refine ⟨C' ⊔ embField E, inferInstance, fun v x => ?_⟩
  have hle : GlobalTheory.Mem.Fld.valueField χ 0 ≤ C' ⊔ embField E := by
    rw [GlobalTheory.Mem.Fld.valueField_le_iff]
    intro w hw
    obtain ⟨y, hy⟩ := hv w hw
    exact ⟨⟨y, le_sup_left (a := C') (hCC y.2)⟩, hy⟩
  exact GlobalTheory.HeckeValField.mem_unitsIn.1
    (GlobalTheory.HeckeValField.loc_mem χ hle (fun k => le_sup_right (a := C') (inf_mem_of_even h k)) v x)

def rootsField (n : ℕ) : IntermediateField ℚ ℂ := IntermediateField.adjoin ℚ {z : ℂ | z ^ n = 1}

end GlobalTheory.HeckeLocVals
