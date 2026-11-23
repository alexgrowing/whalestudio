import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.OrbitQuotientTopology.IsClosedRStab

open Matrix MeasureTheory Measure Topology
open scoped ENNReal

noncomputable section

namespace PI.AmpOrbQuot

open Formalism.QuantumDeterminants Formalism.MainNotions.S PI.AmpRootCommon

variable {k r : ℕ}

theorem det_ne_of_uh {a : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (ha : a ∈ UH (Hpk k r)) :
    a.det ≠ 0 := by
  exact (Matrix.isUnit_det_of_left_inverse (uh_left ha)).ne_zero

theorem continuousAt_inv_of_uh {a : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (ha : a ∈ UH (Hpk k r)) : ContinuousAt (Inv.inv : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → _) a := by
  refine continuousAt_matrix_inv a ?_
  rw [Ring.inverse_eq_inv']
  exact continuousAt_inv₀ (det_ne_of_uh ha)

def RS (k r : ℕ) (g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) : Set (Mt k r) :=
  {x | Matrix.of x ∈ RStab k r g}

theorem isClosed_RS (g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) : IsClosed (RS k r g) := IsClosed.preimage (f := fun x : Mt k r => Matrix.of x) continuous_id (isClosed_RStab g)

abbrev RT (k r : ℕ) (g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) : Type := RS k r g

section Grp

variable {g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} [hg : Fact (g ∈ UH (Hpk k r))]

def toM (x : RT k r g) : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ := Matrix.of x.1

theorem toM_mem (x : RT k r g) : toM x ∈ RStab k r g := x.2

theorem toM_inj {x y : RT k r g} (h : toM x = toM y) : x = y := Subtype.ext (Matrix.of.injective h)

instance : Mul (RT k r g) := ⟨fun x y => ⟨fun i j => (toM x * toM y) i j, rstab_mul hg.out x.2 y.2⟩⟩
instance : One (RT k r g) := ⟨⟨fun i j => (1 : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) i j, rstab_one hg.out⟩⟩
instance : Inv (RT k r g) := ⟨fun x => ⟨fun i j => (toM x)⁻¹ i j, rstab_inv hg.out x.2⟩⟩

theorem toM_mul (x y : RT k r g) : toM (x * y) = toM x * toM y := rfl
theorem toM_one : toM (1 : RT k r g) = 1 := rfl
theorem toM_inv (x : RT k r g) : toM x⁻¹ = (toM x)⁻¹ := rfl

instance instGroupRT : Group (RT k r g) where
  mul_assoc x y z := toM_inj (by rw [toM_mul, toM_mul, toM_mul, toM_mul, Matrix.mul_assoc])
  one_mul x := toM_inj (by rw [toM_mul, toM_one, Matrix.one_mul])
  mul_one x := toM_inj (by rw [toM_mul, toM_one, Matrix.mul_one])
  inv_mul_cancel x := toM_inj (by rw [toM_mul, toM_inv, toM_one, uh_inv_mul (toM_mem x).1.1])

theorem continuous_toM : Continuous (toM : RT k r g → Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) := continuous_subtype_val

instance : IsTopologicalGroup (RT k r g) where
  continuous_mul := by
    refine Continuous.subtype_mk ?_ _
    exact (continuous_toM.comp continuous_fst).matrix_mul (continuous_toM.comp continuous_snd)
  continuous_inv := by
    refine Continuous.subtype_mk ?_ _
    refine continuous_iff_continuousAt.2 fun x => ?_
    exact (continuousAt_inv_of_uh (toM_mem x).1.1).comp continuous_toM.continuousAt

instance : LocallyCompactSpace (RT k r g) := (isClosed_RS g).locallyCompactSpace

end Grp

section Meas

variable {g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} {μR : Measure (Mt k r)}

theorem rs_emb (g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) :
    MeasurableEmbedding (Subtype.val : RT k r g → Mt k r) := MeasurableEmbedding.subtype_coe (isClosed_RS g).measurableSet

theorem rs_back (hc : μR {x | Matrix.of x ∉ RStab k r g} = 0) :
    (μR.comap (Subtype.val : RT k r g → Mt k r)).map Subtype.val = μR := by
  rw [(rs_emb g).map_comap, Subtype.range_coe]
  exact Measure.restrict_eq_self_of_ae_mem (ae_iff.mpr hc)

theorem measurable_lmulM (a : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) :
    Measurable (lmulM (k := k) (r := r) a) := by
  apply measurable_pi_lambda
  intro i
  apply measurable_pi_lambda
  intro j
  have : Continuous (fun x : Mt k r => (a * Matrix.of x) i j) := by
    simp only [Matrix.mul_apply, Matrix.of_apply]
    exact continuous_finset_sum _ fun l _ =>
      continuous_const.mul ((continuous_apply j).comp (continuous_apply l))
  exact this.measurable

theorem rs_val_mul [Fact (g ∈ UH (Hpk k r))] (a : RT k r g) :
    (Subtype.val : RT k r g → Mt k r) ∘ (fun x => a * x) = lmulM (toM a) ∘ Subtype.val := by
  funext x
  rfl

theorem rs_inv [Fact (g ∈ UH (Hpk k r))] (hc : μR {x | Matrix.of x ∉ RStab k r g} = 0)
    (hinv : ∀ s ∈ RStab k r g, μR.map (lmulM s) = μR) :
    IsMulLeftInvariant (μR.comap (Subtype.val : RT k r g → Mt k r)) := by
  constructor
  intro a
  have hf : Measurable (fun x : RT k r g => a * x) := by
    rw [← (rs_emb g).measurable_comp_iff, rs_val_mul a]
    exact (measurable_lmulM _).comp measurable_subtype_coe
  rw [← (rs_emb g).comap_map (Measure.map (fun x => a * x) (μR.comap Subtype.val)),
    Measure.map_map (rs_emb g).measurable hf, rs_val_mul a,
    ← Measure.map_map (measurable_lmulM _) (rs_emb g).measurable, rs_back hc, hinv _ (toM_mem a)]

theorem rs_smul [Fact (g ∈ UH (Hpk k r))] (hμ : IsHaarOn (RStab k r g) μR) :
    ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ⊤ ∧
      μR.comap (Subtype.val : RT k r g → Mt k r) = c • (haar : Measure (RT k r g)) := by
  obtain ⟨hσ, h0, hc, hinv⟩ := hμ
  have hback := rs_back hc
  haveI : SigmaFinite (μR.comap (Subtype.val : RT k r g → Mt k r)) :=
    SigmaFinite.of_map _ (rs_emb g).measurable.aemeasurable (by rw [hback]; exact hσ)
  haveI : IsMulLeftInvariant (μR.comap (Subtype.val : RT k r g → Mt k r)) := rs_inv hc hinv
  obtain ⟨K, hK, hK1⟩ := exists_compact_mem_nhds (1 : RT k r g)
  have hK0 : (haar : Measure (RT k r g)) K ≠ 0 := (measure_pos_of_mem_nhds haar hK1).ne'
  have hKt : (haar : Measure (RT k r g)) K ≠ ⊤ := hK.measure_lt_top.ne
  have heq := measure_eq_div_smul (μ' := μR.comap (Subtype.val : RT k r g → Mt k r))
    (ν' := (haar : Measure (RT k r g))) hK0 hKt
  refine ⟨_, ?_, ?_, heq⟩
  · intro hz
    rw [hz, zero_smul] at heq
    apply h0
    rw [← hback, heq, Measure.map_zero]
  · intro ht
    rw [ht] at heq
    set ν := μR.comap (Subtype.val : RT k r g → Mt k r) with hνdef
    obtain ⟨n, hn⟩ : ∃ n, (haar : Measure (RT k r g)) (spanningSets ν n) ≠ 0 := by
      by_contra hcon
      push_neg at hcon
      have hU : (haar : Measure (RT k r g)) (⋃ n, spanningSets ν n) = 0 := measure_iUnion_null hcon
      rw [iUnion_spanningSets] at hU
      exact isOpen_univ.measure_ne_zero haar Set.univ_nonempty hU
    have h2 : ν (spanningSets ν n) = ((⊤ : ℝ≥0∞) • (haar : Measure (RT k r g))) (spanningSets ν n) := by
      rw [← heq]
    rw [Measure.smul_apply, smul_eq_mul, ENNReal.top_mul hn] at h2
    exact (measure_spanningSets_lt_top ν n).ne h2

theorem rhaar_props (hg : g ∈ UH (Hpk k r)) (hμ : IsHaarOn (RStab k r g) μR) :
    (∀ C : Set (Mt k r), IsCompact C → μR C < ⊤) ∧
      (∀ U : Set (Mt k r), IsOpen U → (U ∩ RS k r g).Nonempty → μR U ≠ 0) := by
  haveI : Fact (g ∈ UH (Hpk k r)) := ⟨hg⟩
  obtain ⟨c, hc1, hc2, hν⟩ := rs_smul hμ
  have hback := rs_back hμ.2.2.1
  refine ⟨?_, ?_⟩
  · intro C hC
    have hpc : IsCompact ((Subtype.val : RT k r g → Mt k r) ⁻¹' C) := by
      rw [Subtype.isCompact_iff, Set.image_preimage_eq_inter_range, Subtype.range_coe]
      exact hC.inter_right (isClosed_RS g)
    rw [← hback, Measure.map_apply (rs_emb g).measurable hC.measurableSet, hν, Measure.smul_apply,
      smul_eq_mul]
    exact ENNReal.mul_lt_top hc2.lt_top hpc.measure_lt_top
  · rintro U hU ⟨x, hxU, hxR⟩
    rw [← hback, Measure.map_apply (rs_emb g).measurable hU.measurableSet, hν, Measure.smul_apply,
      smul_eq_mul]
    exact mul_ne_zero hc1 ((hU.preimage continuous_subtype_val).measure_ne_zero haar ⟨⟨x, hxR⟩, hxU⟩)

end Meas

end PI.AmpOrbQuot
