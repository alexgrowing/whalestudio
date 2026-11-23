import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.PointNormSqNonnegQuotient

namespace ReciprocityTheory.ChartRestriction.G.I2

open NumberField MeasureTheory Col

noncomputable section

theorem cube_split {α β : Type} [Fintype α] [Fintype β] (f : (α ⊕ β → ℝ) → ENNReal)
    (hf : Measurable f) :
    ∫⁻ x in cubeIco (α ⊕ β), f x =
      ∫⁻ y in cubeIco β, ∫⁻ t in cubeIco α, f (fun k => Sum.elim t y k) := by
  have hmp := volume_measurePreserving_sumPiEquivProdPi_symm (fun _ : α ⊕ β => ℝ)
  rw [← hmp.setLIntegral_comp_preimage_emb
    (MeasurableEquiv.sumPiEquivProdPi (fun _ : α ⊕ β => ℝ)).symm.measurableEmbedding]
  have hpre : (MeasurableEquiv.sumPiEquivProdPi (fun _ : α ⊕ β => ℝ)).symm ⁻¹' cubeIco (α ⊕ β) =
      cubeIco α ×ˢ cubeIco β := by
    ext ⟨t, y⟩
    simp [cubeIco, MeasurableEquiv.coe_sumPiEquivProdPi_symm, Sum.forall]
  rw [hpre, Measure.volume_eq_prod, ← Measure.prod_restrict, lintegral_prod_symm]
  · rfl
  · exact (hf.comp (MeasurableEquiv.sumPiEquivProdPi _).symm.measurable).aemeasurable

variable {E : Type} [Field E] [NumberField E]

namespace ZM

variable [IsCMField E] {X : PT E} {DF : ℕ} {P : Par X DF} {I : Submodule ℤ (Vsp X.dim)}

def What (hI : IsSplit P I) (hP : Ext.PackingCount) (a : Fin (Module.finrank ℝ (IR I)) → ℝ)
    (r : Fin (2 * Fintype.card (Fin (gB (IR I)))) → ℝ) : Vsp X.dim :=
  ∑ j, a j • cp hI j + ∑ l, r l • cpp hI hP l

theorem uc_rsmul (c : ℝ) (v : Vsp X.dim) : uc (IR I) (c • v) = c • uc (IR I) v := by
  simp only [uc, z, Hf_rsmul_l, Complex.im_ofReal_mul, Finset.smul_sum, mul_smul]

theorem uc_sum {ι : Type} (F : Finset ι) (f : ι → Vsp X.dim) :
    uc (IR I) (∑ i ∈ F, f i) = ∑ i ∈ F, uc (IR I) (f i) := by
  classical
  induction F using Finset.induction_on with
  | empty => simpa using uc_rsmul (I := I) (0 : ℝ) (0 : Vsp X.dim)
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, uc_add, ih]

theorem uc_What (hI : IsSplit P I) (hP : Ext.PackingCount) (a r) :
    uc (IR I) (What hI hP a r) = ∑ j, a j • uc (IR I) (cp hI j) := by
  have h0 : ∀ l, uc (IR I) (cpp hI hP l) = 0 := fun l => uc_Ip (cpp_mem hI hP l)
  simp only [What, uc_add, uc_sum, uc_rsmul, h0, smul_zero, Finset.sum_const_zero, add_zero]

theorem wmap_What (hI : IsSplit P I) (hP : Ext.PackingCount) (a r) :
    wmap (IR I) (What hI hP a r) = wmap (IR I) (∑ j, a j • cp hI j) + (bB hI hP).equivFun.symm r := by
  rw [What, map_add]
  congr 1
  rw [Module.Basis.equivFun_symm_apply, map_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [ContinuousLinearMap.map_smul_of_tower, cpp_wmap]

end ZM

end

end ReciprocityTheory.ChartRestriction.G.I2
