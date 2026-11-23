import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ValuationLocalVolumes.VolUHaar
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ValuationLocalVolumes.VolTProd

noncomputable section

namespace Formalism.L2.SG.Pf.NcVal.VolUL

open Formalism.L2.SG.Pf.NcVal Formalism.L2.SG.LocVol Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory NumberField IsDedekindDomain
open scoped ENNReal NNReal TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (ψ : AddChar (AF F) ℂ) (v : HeightOneSpectrum (𝓞 F))

def AnnAt : Prop :=
  ∀ y : Fv F v ⊗[F] E,
    (∀ x ∈ OEv (E := E) v, psiV F ψ v (Algebra.trace (Fv F v) (Fv F v ⊗[F] E) (x * y)) = 1) ↔
      sc (E := E) v (dV v) * y ∈ OEv (E := E) v

theorem volTO_eq (ι : Type) : VolTO (E := E) v ι = Set.univ.pi fun _ => OEv (E := E) v := by
  ext x
  simp [VolTO]

theorem sd_facts (hψ : IsCharAF F ψ) (hfin : Module.finrank F E = 2) (hann : AnnAt (E := E) ψ v)
    (hd : absV v (dV v) = 1) (ι : Type) [Fintype ι] :
    (sdE (E := E) ψ v ι).IsAddHaarMeasure ∧ SFinite (sdE (E := E) ψ v ι) ∧ VolTOne (E := E) ψ v ι := by
  classical
  obtain ⟨h1, h2, h3, h4, h5⟩ := Formalism.L2.SG.Pf.NcVal.VolUH.top_facts (E := E) v ι
  have hunit : Valued.v (dV v) = 1 := Formalism.L2.SG.Pf.NcVal.VolTU.val_eq_one_of_absV v hd
  have hD1 : PI.UnitaryGroupMassFormula.LocJacTyp.Sd.D1 (E := E) v ψ = OEv (E := E) v := by
    ext y
    show (∀ x ∈ OEv (E := E) v, _) ↔ _
    rw [hann y, Formalism.L2.SG.Pf.NcVal.VolTU.unit_mul_mem_iff v hunit]
  have hone : (1 : Fv F v ⊗[F] E) ∈ OEv (E := E) v := by
    have := PI.UnitaryGroupMassFormula.LocJacTyp.Sd.inclR_mem (E := E) v 1
    simp only [OneMemClass.coe_one, map_one] at this
    exact this
  have htr1 : Algebra.trace (Fv F v) (Fv F v ⊗[F] E) 1 = 2 := by
    have := PI.UnitaryGroupMassFormula.LocJacTyp.Sd.trace_inclR (E := E) v 1
    simp only [map_one] at this
    rw [this, show (1 : E) = algebraMap F E 1 from (map_one _).symm, Algebra.trace_algebraMap, hfin]
    simp
    exact map_ofNat _ 2
  have hOK : PI.UnitaryGroupMassFormula.LocJacTyp.Sd.OpenKer v ψ := by
    refine PI.UnitaryGroupMassFormula.LocJacTyp.Sd.openKer_of v ψ 2 two_ne_zero ?_
    intro c hc
    have hy : sc (E := E) v c * 1 ∈ OEv (E := E) v :=
      Formalism.L2.SG.Pf.NcVal.VolTU.sc_mul_mem v hc hone
    have hmem : sc (E := E) v c * 1 ∈ PI.UnitaryGroupMassFormula.LocJacTyp.Sd.D1 (E := E) v ψ := by rw [hD1]; exact hy
    have := hmem 1 hone
    rw [one_mul, Formalism.L2.SG.Pf.NcVal.VolTU.sc_mul_eq_smul, map_smul, htr1, smul_eq_mul] at this
    exact this
  have hnt : ∃ r : Fv F v, psiV F ψ v r ≠ 1 := by
    obtain ⟨t0, ht0⟩ := PI.UnitaryGroupMassFormula.LocJacTyp.Sd.exists_not_mem_oev (E := E) v
    have : t0 ∉ PI.UnitaryGroupMassFormula.LocJacTyp.Sd.D1 (E := E) v ψ := by rw [hD1]; exact ht0
    simp only [PI.UnitaryGroupMassFormula.LocJacTyp.Sd.D1, Set.mem_setOf_eq, not_forall] at this
    obtain ⟨x, _, hx⟩ := this
    exact ⟨_, hx⟩
  have hex := PI.UnitaryGroupMassFormula.LocJacTyp.Sd.exists_sd (E := E) v ψ hOK hnt ι
  have hsd : SelfDual (sdE (E := E) ψ v ι) (PI.UnitaryGroupMassFormula.LocJacTyp.Sd.chi v ψ ι) := by
    have hex' : ∃ μ : Measure (ι → Fv F v ⊗[F] E), SelfDual μ fun x y : ι → Fv F v ⊗[F] E =>
        psiV F ψ v (∑ i : ι, Algebra.trace (Fv F v) (Fv F v ⊗[F] E) (x i * y i)) := hex
    unfold sdE
    rw [dif_pos hex']
    exact hex'.choose_spec
  haveI : (sdE (E := E) ψ v ι).IsAddHaarMeasure := hsd.1
  refine ⟨inferInstance, inferInstance, ?_⟩
  have hDO : PI.UnitaryGroupMassFormula.LocJacTyp.Sd.Dbox (E := E) v ψ ι = PI.UnitaryGroupMassFormula.LocJacTyp.Obox v ι := by
    simp only [PI.UnitaryGroupMassFormula.LocJacTyp.Sd.Dbox, PI.UnitaryGroupMassFormula.LocJacTyp.Obox, hD1]
    rfl
  have hOc := PI.UnitaryGroupMassFormula.LocJacTyp.Sd.isCompact_obox (E := E) v ι
  have hOo := PI.UnitaryGroupMassFormula.LocJacTyp.Sd.isOpen_obox (E := E) v ι
  have hfin' : sdE (E := E) ψ v ι (PI.UnitaryGroupMassFormula.LocJacTyp.Obox v ι) < ⊤ := hOc.measure_lt_top
  have ht := PI.UnitaryGroupMassFormula.LocJacTyp.Sd.sd_test (E := E) v ψ ι _ hsd (by rw [hDO]; exact hOo.measurableSet)
    (by rw [hDO]; exact hfin')
  rw [hDO] at ht
  have hpos : 0 ≤ (sdE (E := E) ψ v ι).real (PI.UnitaryGroupMassFormula.LocJacTyp.Obox v ι) := measureReal_nonneg
  have hr : (sdE (E := E) ψ v ι).real (PI.UnitaryGroupMassFormula.LocJacTyp.Obox v ι) = 1 := by
    nlinarith [sq_nonneg ((sdE (E := E) ψ v ι).real (PI.UnitaryGroupMassFormula.LocJacTyp.Obox v ι) - 1)]
  show sdE (E := E) ψ v ι (VolTO (E := E) v ι) = 1
  rw [volTO_eq]
  change sdE (E := E) ψ v ι (PI.UnitaryGroupMassFormula.LocJacTyp.Obox v ι) = 1
  rw [← ENNReal.ofReal_toReal hfin'.ne]
  simpa [measureReal_def] using congrArg ENNReal.ofReal hr

theorem volTAff_of (hψ : IsCharAF F ψ) (hfin : Module.finrank F E = 2) (hann : AnnAt (E := E) ψ v)
    (hd : absV v (dV v) = 1) {g : ℕ} (hg0 : g ≠ 0) (hg : absV v (g : Fv F v) = (g : ℝ)⁻¹)
    (ι : Type) [Fintype ι] : VolTAff (E := E) ψ v g ι := by
  classical
  intro b S
  obtain ⟨hH, hS, hV⟩ := sd_facts (E := E) ψ v hψ hfin hann hd ι
  set μ := sdE (E := E) ψ v ι with hμ
  have hgne : ((g : Fv F v))⁻¹ ≠ 0 := inv_ne_zero (Formalism.L2.SG.Pf.NcVal.VolTU.natCast_ne_zero v hg0)
  set T : Set (ι → Fv F v ⊗[F] E) := {u | (fun i => sc (E := E) v ((g : Fv F v))⁻¹ * u i) ∈ S} with hT
  have h1 : μ {w : ι → Fv F v ⊗[F] E | (fun i => (w i - b i) * sc (E := E) v ((g : Fv F v))⁻¹) ∈ S} = μ T := by
    have := Formalism.L2.SG.Pf.NcVal.VolUH.sub_pre (E := E) v ι μ b T
    rw [← this]
    congr 1
    ext w
    simp only [hT, Set.mem_setOf_eq, mul_comm]
  have h2 := Formalism.L2.SG.Pf.NcVal.VolUH.sc_pre (E := E) v ι μ hV (fun _ => ((g : Fv F v))⁻¹) (fun _ => hgne) S
  rw [h1, hT, h2]
  congr 1
  have hset : {w : ι → Fv F v ⊗[F] E | ∀ i, sc (E := E) v ((g : Fv F v))⁻¹ * w i ∈ OEv (E := E) v} =
      Set.univ.pi fun _ : ι => {c : Fv F v ⊗[F] E | sc (E := E) v ((g : Fv F v))⁻¹ * c ∈ OEv (E := E) v} := by
    ext w
    simp
  rw [hset]
  have hbs := PI.UnitaryGroupMassFormula.LocJacTyp.boxScale (E := E) v hfin μ (fun _ => ((g : Fv F v))⁻¹) (fun _ => hgne)
  have hO : μ (PI.UnitaryGroupMassFormula.LocJacTyp.Obox v ι) = 1 := by
    have := hV
    simp only [VolTOne, volTO_eq] at this
    exact this
  have hsub : (Set.univ.pi fun _ : ι => {c : Fv F v ⊗[F] E | sc (E := E) v ((g : Fv F v))⁻¹ * c ∈ OEv (E := E) v})
      ⊆ PI.UnitaryGroupMassFormula.LocJacTyp.Obox v ι := by
    intro w hw
    simp only [Set.mem_pi, Set.mem_univ, Set.mem_setOf_eq, forall_true_left] at hw
    simp only [PI.UnitaryGroupMassFormula.LocJacTyp.Obox, Set.mem_pi, Set.mem_univ, forall_true_left]
    intro i
    have := Formalism.L2.SG.Pf.NcVal.VolTU.sc_mul_mem (E := E) v (Formalism.L2.SG.Pf.NcVal.VolTU.natCast_memO v g) (hw i)
    rw [← mul_assoc, ← Formalism.L2.SG.Pf.NcVal.VolTU.sc_mul, mul_inv_cancel₀ (Formalism.L2.SG.Pf.NcVal.VolTU.natCast_ne_zero v hg0),
      Formalism.L2.SG.Pf.NcVal.VolTU.sc_one, one_mul] at this
    exact this
  have hfin' : μ (Set.univ.pi fun _ : ι => {c : Fv F v ⊗[F] E | sc (E := E) v ((g : Fv F v))⁻¹ * c ∈ OEv (E := E) v}) ≠ ⊤ :=
    ne_top_of_le_ne_top (by rw [hO]; exact ENNReal.one_ne_top) (measure_mono hsub)
  rw [← ENNReal.ofReal_toReal hfin']
  change ENNReal.ofReal (μ (Set.univ.pi fun i : ι => {c : Fv F v ⊗[F] E | PI.LocJacTyp.sc v ((fun _ => ((g : Fv F v))⁻¹) i) * c ∈ PI.LocJacTyp.OEv v})).toReal = _
  rw [hbs, hO]
  have habs : PI.LocJacTyp.absV v ((g : Fv F v))⁻¹ = (g : ℝ) := by
    rw [PI.UnitaryGroupMassFormula.LocJacTyp.absV_inv]
    change (absV v (g : Fv F v))⁻¹ = _
    rw [hg, inv_inv]
  simp only [habs, ENNReal.toReal_one, one_mul, Finset.prod_const, Finset.card_univ]
  rw [← inv_pow, ← pow_mul, ENNReal.ofReal_pow (by positivity), ENNReal.ofReal_inv_of_pos (by positivity)]
  rw [ENNReal.ofReal_natCast, ← ENNReal.inv_pow, mul_comm]

theorem volTLocPres_of (hψ : IsCharAF F ψ) (hfin : Module.finrank F E = 2) (hann : AnnAt (E := E) ψ v)
    (hd : absV v (dV v) = 1) (r : ℕ) : VolTLocPres (E := E) ψ v r := by
  classical
  intro S
  obtain ⟨hH, hS, hV⟩ := sd_facts (E := E) ψ v hψ hfin hann hd (Fin (r + 1) × Fin (r + 1))
  have hunit : Valued.v (dV v) = 1 := Formalism.L2.SG.Pf.NcVal.VolTU.val_eq_one_of_absV v hd
  have hz : ∀ p : Fin (r + 1) × Fin (r + 1), alp v r p.1 * alp v r p.2 ≠ 0 := by
    intro p h
    have h1 := Formalism.L2.SG.Pf.NcVal.VolTU.val_alp v hunit r p.1
    have h2 := Formalism.L2.SG.Pf.NcVal.VolTU.val_alp v hunit r p.2
    have : Valued.v (alp v r p.1 * alp v r p.2) = 1 := by rw [map_mul, h1, h2, one_mul]
    rw [h, map_zero] at this
    exact zero_ne_one this
  have key := Formalism.L2.SG.Pf.NcVal.VolUH.sc_pre (E := E) v (Fin (r + 1) × Fin (r + 1)) (sdE (E := E) ψ v _) hV
    (fun p => alp v r p.1 * alp v r p.2) hz S
  have hset : {w : Fin (r + 1) × Fin (r + 1) → Fv F v ⊗[F] E |
      ∀ i, sc (E := E) v (alp v r i.1 * alp v r i.2) * w i ∈ OEv (E := E) v} = VolTO (E := E) v _ := by
    ext w
    simp only [Set.mem_setOf_eq, VolTO]
    refine forall_congr' fun i => ?_
    apply Formalism.L2.SG.Pf.NcVal.VolTU.unit_mul_mem_iff
    rw [map_mul, Formalism.L2.SG.Pf.NcVal.VolTU.val_alp v hunit, Formalism.L2.SG.Pf.NcVal.VolTU.val_alp v hunit, one_mul]
  rw [hset, hV, one_mul] at key
  exact key

theorem volTO_meas (ι : Type) [Fintype ι] : MeasurableSet (VolTO (E := E) v ι) := by
  rw [volTO_eq]
  exact MeasurableSet.univ_pi fun _ => (PI.UnitaryGroupMassFormula.LocJacTyp.Sd.isOpen_oev (E := E) v).measurableSet

theorem volTUSet_meas {g : ℕ} (hg0 : g ≠ 0) (r : ℕ) : MeasurableSet (VolTUSet (E := E) v g r) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := Formalism.L2.SG.Pf.NcVal.VolUH.top_facts (E := E) v (UIdx r)
  have hO := PI.UnitaryGroupMassFormula.LocJacTyp.Sd.isOpen_oev (E := E) v
  have hc : Continuous fun x : Fv F v ⊗[F] E => x * sc (E := E) v ((g : Fv F v))⁻¹ := by
    simp_rw [mul_comm _ (sc (E := E) v _), Formalism.L2.SG.Pf.NcVal.VolTU.sc_mul_eq_smul]
    exact continuous_const_smul _
  apply IsOpen.measurableSet
  simp only [VolTUSet, Set.setOf_and]
  apply IsOpen.inter
  · simp only [Set.setOf_forall]
    exact isOpen_iInter_of_finite fun q => hO.preimage ((continuous_apply q).comp continuous_fst)
  · simp only [Set.setOf_forall]
    exact isOpen_iInter_of_finite fun q => hO.preimage
      (hc.comp (((continuous_apply q).comp continuous_snd).sub ((continuous_apply q).comp continuous_fst)))

theorem volTProdU_of' (hψ : IsCharAF F ψ) (hfin : Module.finrank F E = 2) (hann : AnnAt (E := E) ψ v)
    (hd : absV v (dV v) = 1) {g : ℕ} (hg0 : g ≠ 0) (hg : absV v (g : Fv F v) = (g : ℝ)⁻¹) (r : ℕ) :
    VolTProdU (E := E) ψ v g r := by
  obtain ⟨-, hS, hO⟩ := sd_facts ψ v hψ hfin hann hd (UIdx r)
  exact volTProdU_of ψ v g r (volTUSet_meas v hg0 r) (volTO_meas v (UIdx r))
    (volTAff_of ψ v hψ hfin hann hd hg0 hg (UIdx r)) hO

end Formalism.L2.SG.Pf.NcVal.VolUL
