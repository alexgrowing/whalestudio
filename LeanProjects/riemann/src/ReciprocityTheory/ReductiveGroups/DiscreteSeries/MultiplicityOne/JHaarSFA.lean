import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.StSchurW
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.UnitaryGroupStructuralFacts

open MeasureTheory
open scoped NNReal ENNReal

noncomputable section

namespace ReciprocityTheory.ChartRestriction.DS.Mult1.HaarSigmaFiniteUniqueness

section Grp

variable {G : Type*} [MeasurableSpace G] [Group G] [MeasurableMul₂ G] [MeasurableInv G]

theorem eq_smul_of_sigmaFinite (μ ν : Measure G) [SigmaFinite μ] [SigmaFinite ν]
    [μ.IsMulLeftInvariant] [ν.IsMulLeftInvariant] (hμ : μ ≠ 0) (hν : ν ≠ 0) :
    ∃ c : ℝ≥0, c ≠ 0 ∧ μ = c • ν := by
  obtain ⟨n, hn⟩ : ∃ n, ν (spanningSets (μ + ν) n) ≠ 0 := by
    by_contra h
    push_neg at h
    apply hν
    have : ν Set.univ = 0 := by
      rw [← iUnion_spanningSets (μ + ν)]
      exact measure_iUnion_null h
    exact Measure.measure_univ_eq_zero.mp this
  have hS := measurableSet_spanningSets (μ + ν) n
  have hfin := measure_spanningSets_lt_top (μ + ν) n
  rw [Measure.add_apply] at hfin
  have hνf : ν (spanningSets (μ + ν) n) ≠ ∞ := (lt_of_le_of_lt le_add_self hfin).ne
  have hμf : μ (spanningSets (μ + ν) n) ≠ ∞ := (lt_of_le_of_lt le_self_add hfin).ne
  have heq : μ = (μ (spanningSets (μ + ν) n) / ν (spanningSets (μ + ν) n)) • ν := by
    first
    | exact measure_eq_div_smul μ ν (spanningSets (μ + ν) n) hn hνf
    | exact measure_eq_div_smul μ ν hS hn hνf
    | exact measure_eq_div_smul μ ν (spanningSets (μ + ν) n) hS hn hνf
    | (ext t ht
       have key := measure_mul_measure_eq μ ν (spanningSets (μ + ν) n) t hn hνf ht
       rw [Measure.smul_apply, smul_eq_mul, ENNReal.div_eq_inv_mul, mul_assoc, key, ← mul_assoc,
         ENNReal.inv_mul_cancel hn hνf, one_mul])
    | (ext t ht
       have key := measure_mul_measure_eq μ ν (spanningSets (μ + ν) n) t hn hνf
       rw [Measure.smul_apply, smul_eq_mul, ENNReal.div_eq_inv_mul, mul_assoc, key, ← mul_assoc,
         ENNReal.inv_mul_cancel hn hνf, one_mul])
    | (ext t ht
       have key := measure_mul_measure_eq μ ν (spanningSets (μ + ν) n) t hS ht hn hνf
       rw [Measure.smul_apply, smul_eq_mul, ENNReal.div_eq_inv_mul, mul_assoc, key, ← mul_assoc,
         ENNReal.inv_mul_cancel hn hνf, one_mul])
  have hμ0 : μ (spanningSets (μ + ν) n) ≠ 0 := by
    intro h0
    apply hμ
    rw [heq, h0, ENNReal.zero_div, zero_smul]
  refine ⟨(μ (spanningSets (μ + ν) n) / ν (spanningSets (μ + ν) n)).toNNReal, ?_, ?_⟩
  · intro h
    rw [ENNReal.toNNReal_eq_zero_iff, ENNReal.div_eq_zero_iff] at h
    rcases h with (h | h) | h
    · exact hμ0 h
    · exact hνf h
    · exact ENNReal.div_ne_top hμf hn h
  · rw [ENNReal.smul_def, ENNReal.coe_toNNReal (ENNReal.div_ne_top hμf hn)]
    exact heq

end Grp

section Mat

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2

variable {k r : ℕ}

def Aset (U : Set (Mat k r)) : Set (Mt k r) := {x | Matrix.of x ∈ U}

variable {U : Set (Mat k r)}

private theorem continuous_matrix_of_Mt : Continuous (fun x : Mt k r => (Matrix.of x : Mat k r)) :=
  continuous_matrix (fun i j => (continuous_apply j).comp (continuous_apply i))

theorem isClosed_Aset (hU : IsClosedSubgroup U) : IsClosed (Aset U) := by
  exact hU.closed.preimage continuous_matrix_of_Mt

theorem measurableSet_Aset (hU : IsClosedSubgroup U) : MeasurableSet (Aset U) := by
  exact (isClosed_Aset hU).measurableSet

def toM (a : Aset U) : Mat k r := Matrix.of a.1

theorem toM_inj {a b : Aset U} (h : toM a = toM b) : a = b := by
  exact Subtype.ext (Matrix.of.injective h)

variable [hU : Fact (IsClosedSubgroup U)]

instance : Mul (Aset U) := ⟨fun a b => ⟨(toM a * toM b : Mat k r), hU.out.mul_mem _ a.2 _ b.2⟩⟩
instance : One (Aset U) := ⟨⟨(1 : Mat k r), hU.out.one_mem⟩⟩
instance : Inv (Aset U) := ⟨fun a => ⟨((toM a)⁻¹ : Mat k r), hU.out.inv_mem _ a.2⟩⟩

theorem toM_mul (a b : Aset U) : toM (a * b) = toM a * toM b := rfl
theorem toM_one : toM (1 : Aset U) = 1 := rfl
theorem toM_inv (a : Aset U) : toM a⁻¹ = (toM a)⁻¹ := rfl

instance : Group (Aset U) where
  mul_assoc a b c := toM_inj (by simp only [toM_mul]; exact Matrix.mul_assoc _ _ _)
  one_mul a := toM_inj (by simp only [toM_mul, toM_one]; exact Matrix.one_mul _)
  mul_one a := toM_inj (by simp only [toM_mul, toM_one]; exact Matrix.mul_one _)
  inv_mul_cancel a := toM_inj (by
    simp only [toM_mul, toM_one, toM_inv]
    exact Matrix.nonsing_inv_mul _ (hU.out.unit _ a.2))

theorem continuous_toM : Continuous (toM : Aset U → Mat k r) := by
  exact continuous_matrix_of_Mt.comp continuous_subtype_val

theorem continuous_mulA : Continuous fun p : Aset U × Aset U => p.1 * p.2 := by
  refine Continuous.subtype_mk ?_ _
  show Continuous fun p : Aset U × Aset U => (toM p.1 * toM p.2 : Mat k r)
  exact (continuous_toM.comp continuous_fst).mul (continuous_toM.comp continuous_snd)

theorem continuous_invA : Continuous fun a : Aset U => a⁻¹ := by
  refine Continuous.subtype_mk ?_ _
  have h : (fun a : Aset U => (toM a)⁻¹) = fun a => (toM a).det⁻¹ • (toM a).adjugate := by
    funext a; rw [Matrix.inv_def, Ring.inverse_eq_inv]
  show Continuous fun a : Aset U => ((toM a)⁻¹ : Mat k r)
  rw [h]
  exact ((continuous_toM.matrix_det).inv₀ fun a => (hU.out.unit _ a.2).ne_zero).smul continuous_toM.matrix_adjugate

instance : MeasurableMul₂ (Aset U) := ⟨continuous_mulA.measurable⟩
instance : MeasurableInv (Aset U) := ⟨continuous_invA.measurable⟩

end Mat

section Transfer

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2

variable {k r : ℕ} {U : Set (Mat k r)} [hU : Fact (IsClosedSubgroup U)]

theorem mEmb : MeasurableEmbedding (Subtype.val : Aset U → Mt k r) := by
  exact MeasurableEmbedding.subtype_coe (measurableSet_Aset hU.out)

theorem map_comap_val (μ : Measure (Mt k r)) (hc : μ (Aset U)ᶜ = 0) :
    (μ.comap (Subtype.val : Aset U → Mt k r)).map Subtype.val = μ := by
  rw [(mEmb (U := U)).map_comap μ]
  first | rw [Subtype.range_coe] | rw [Subtype.range_val] | skip
  exact Measure.restrict_eq_self_of_ae_mem (ae_iff.mpr hc)

theorem sigmaFinite_comap (μ : Measure (Mt k r)) [SigmaFinite μ] :
    SigmaFinite (μ.comap (Subtype.val : Aset U → Mt k r)) := by
  refine SigmaFinite.of_map _ (mEmb (U := U)).measurable.aemeasurable ?_
  rw [(mEmb (U := U)).map_comap μ]
  infer_instance

theorem continuous_lmulM (a : Mat k r) : Continuous (lmulM (k := k) (r := r) a) := by
  exact (continuous_const.mul continuous_matrix_of_Mt : Continuous fun x : Mt k r => (a * Matrix.of x : Mat k r))

theorem isMulLeftInvariant_comap (μ : Measure (Mt k r)) (hc : μ (Aset U)ᶜ = 0)
    (hl : ∀ a ∈ U, μ.map (lmulM a) = μ) :
    (μ.comap (Subtype.val : Aset U → Mt k r)).IsMulLeftInvariant := by
  constructor
  intro g
  have hm : Measurable (fun x : Aset U => g * x) := by
    refine Measurable.subtype_mk ?_
    exact (continuous_lmulM (toM g)).measurable.comp measurable_subtype_coe
  have hval : Subtype.val ∘ (fun x : Aset U => g * x) = lmulM (toM g) ∘ Subtype.val := rfl
  have hmap : ((μ.comap (Subtype.val : Aset U → Mt k r)).map (fun x : Aset U => g * x)).map Subtype.val
      = (μ.comap (Subtype.val : Aset U → Mt k r)).map Subtype.val := by
    rw [Measure.map_map (mEmb (U := U)).measurable hm, hval,
      ← Measure.map_map (continuous_lmulM (toM g)).measurable (mEmb (U := U)).measurable,
      map_comap_val μ hc, hl (toM g) g.2]
  ext s hs
  have h1 := congrArg (fun m : Measure (Mt k r) => m (Subtype.val '' s)) hmap
  rwa [(mEmb (U := U)).map_apply, (mEmb (U := U)).map_apply,
    Set.preimage_image_eq _ Subtype.val_injective] at h1

end Transfer

end ReciprocityTheory.ChartRestriction.DS.Mult1.HaarSigmaFiniteUniqueness

end
