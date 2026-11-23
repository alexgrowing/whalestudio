import Development.DiscreteGroups.PiInvariants.CompactSupportTwists.LogAbsEqLogIdeleNorm
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField

set_option linter.all false

noncomputable section

open NumberField Matrix MeasureTheory Filter Set
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.IdeleCovolume GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele PositivityTheory.Rg.BcB
open scoped ENNReal

namespace DiscreteGroups.T1.G

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

abbrev lg (g : GA E n) : ℝ := logAbs g.val.det

theorem lg_eq (g : GA E n) : lg g = Real.log (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.ideleNorm (Matrix.GeneralLinearGroup.det g)) := by
  have h := logAbs_eq_log_ideleNorm (Matrix.GeneralLinearGroup.det g)
  rw [Matrix.GeneralLinearGroup.val_det_apply] at h
  exact h

theorem lg_mul (g h : GA E n) : lg (g * h) = lg g + lg h := by
  rw [lg_eq, lg_eq, lg_eq, map_mul, map_mul,
    Real.log_mul (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.ideleNorm_ne_zero _) (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.ideleNorm_ne_zero _)]

def lgHom : GA E n →* Multiplicative ℝ where
  toFun g := Multiplicative.ofAdd (lg g)
  map_one' := by
    have h := lg_mul (1 : GA E n) 1
    rw [mul_one] at h
    simp only [show lg (1 : GA E n) = 0 by linarith, ofAdd_zero]
  map_mul' g h := by rw [lg_mul, ofAdd_add]

theorem lg_zpow (g : GA E n) (m : ℤ) : lg (g ^ m) = m * lg g := by
  have h := map_zpow (lgHom (E := E) (n := n)) g m
  have h2 := congrArg Multiplicative.toAdd h
  rw [toAdd_zpow] at h2
  simpa [lgHom, zsmul_eq_mul] using h2

theorem lg_rat (γ : GL (Fin n) E) : lg (ratGL E n γ) = 0 := by
  have hd : GeneralLinearGroup.det (ratGL E n γ) = diag E (GeneralLinearGroup.det γ) :=
    Units.ext (by rw [ratGL, GlobalTheory.CuspRep.det_map]; rfl)
  rw [lg_eq, hd, show GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.ideleNorm (E := E) (diag E _) = 1 from ideleNorm_principalIdele _,
    Real.log_one]

theorem lg_e_pos (hn : 1 ≤ n) : 0 < lg (splitCentre E n 1) := by
  rw [lg_eq, det_splitCentre_one, map_pow, Real.log_pow]
  exact mul_pos (by exact_mod_cast hn) (Real.log_pos (one_lt_ideleNorm_eIdele E))

theorem ratRange_le : (ratGL E n).range ≤ latticeGL E n := le_sup_left

instance discreteTopology_ratRange : DiscreteTopology (ratGL E n).range :=
  DiscreteTopology.of_continuous_injective (f := Subgroup.inclusion (ratRange_le (E := E) (n := n)))
    (Continuous.subtype_mk continuous_subtype_val _) (Subgroup.inclusion_injective _)

theorem tsum_indicator (hn : 1 ≤ n) (h : GA E n → ℝ≥0∞) (hh : LeftInv (latticeGL E n) h) (v : ℝ → ℝ≥0∞)
    (y : GA E n) :
    ∑' γ : latticeGL E n, (stdDom (ratGL E n).range).indicator (fun g => h g * v (lg g)) ((γ : GA E n) * y) =
      h y * ∑' m : ℤ, v (lg y + m * lg (splitCentre E n 1)) := by
  set Γ₀ := (ratGL E n).range with hΓ₀
  set e := splitCentre E n 1 with he
  have hc : lg e ≠ 0 := (lg_e_pos hn).ne'
  let r : ℤ → Γ₀ := fun m => (existsUnique_stdDom Γ₀ (e ^ m * y)).choose
  have hr : ∀ m, ((r m : Γ₀) : GA E n) * (e ^ m * y) ∈ stdDom Γ₀ := fun m =>
    (existsUnique_stdDom Γ₀ (e ^ m * y)).choose_spec.1
  have hrlg : ∀ m, lg ((r m : Γ₀) : GA E n) = 0 := fun m => by
    obtain ⟨γ, hγ⟩ := (r m).2
    rw [← hγ]
    exact lg_rat γ
  let g : ℤ → latticeGL E n := fun m =>
    ⟨((r m : Γ₀) : GA E n) * e ^ m, mul_mem (ratRange_le (r m).2) (zpow_mem_latticeGL m)⟩
  have hlgg : ∀ m : ℤ, lg (((g m : latticeGL E n) : GA E n) * y) = lg y + m * lg e := fun m => by
    change lg (((r m : Γ₀) : GA E n) * e ^ m * y) = _
    rw [lg_mul, lg_mul, hrlg, lg_zpow]
    ring
  have hinj : Function.Injective g := fun m m' hmm => by
    have h1 := congrArg (fun γ : latticeGL E n => lg ((γ : GA E n) * y)) hmm
    simp only [hlgg] at h1
    have h2 : (m : ℝ) * lg e = m' * lg e := by linarith
    exact_mod_cast mul_right_cancel₀ hc h2
  rw [← hinj.tsum_eq, ← ENNReal.tsum_mul_left]
  · refine tsum_congr fun m => ?_
    have hmem : ((g m : latticeGL E n) : GA E n) * y ∈ stdDom Γ₀ := by
      change ((r m : Γ₀) : GA E n) * e ^ m * y ∈ stdDom Γ₀
      rw [mul_assoc]
      exact hr m
    rw [indicator_of_mem hmem]
    change h (((g m : latticeGL E n) : GA E n) * y) * v (lg (((g m : latticeGL E n) : GA E n) * y)) = _
    rw [hlgg, hh _ (g m).2 y]
  · intro γ hγ
    have hin : (γ : GA E n) * y ∈ stdDom Γ₀ := by
      by_contra hc'
      exact hγ (indicator_of_notMem hc' _)
    obtain ⟨γ₁, m, hγe⟩ := mem_latticeGL_iff.1 γ.2
    refine ⟨m, Subtype.ext ?_⟩
    have h3 : ((⟨ratGL E n γ₁, γ₁, rfl⟩ : Γ₀) : GA E n) * (e ^ m * y) ∈ stdDom Γ₀ := by
      change ratGL E n γ₁ * (e ^ m * y) ∈ stdDom Γ₀
      rw [← mul_assoc, hγe]
      exact hin
    have hu := (existsUnique_stdDom Γ₀ (e ^ m * y)).unique (hr m) h3
    change ((r m : Γ₀) : GA E n) * e ^ m = γ
    rw [hu]
    exact hγe

theorem lintegral_unfold (μ : Measure (GA E n)) [μ.IsMulLeftInvariant] (hn : 1 ≤ n) (h : GA E n → ℝ≥0∞)
    (hh : LeftInv (latticeGL E n) h) (hm : AEMeasurable h μ) (v : ℝ → ℝ≥0∞) (hv : Measurable v) :
    ∫⁻ g in stdDom (ratGL E n).range, h g * v (lg g) ∂μ =
      ∫⁻ q, h q.out * ∑' m : ℤ, v (lg q.out + m * lg (splitCentre E n 1)) ∂quotMeasure (latticeGL E n) μ := by
  have hS := measurableSet_stdDom (ratGL E n).range
  have hf : AEMeasurable ((stdDom (ratGL E n).range).indicator fun g => h g * v (lg g)) μ :=
    (hm.mul (hv.comp_aemeasurable continuous_logAbs_det.measurable.aemeasurable)).indicator hS
  rw [← lintegral_indicator hS, lintegral_eq_lintegral_tsum (Γ := latticeGL E n) hf]
  exact lintegral_congr fun q => tsum_indicator hn h hh v q.out

end DiscreteGroups.T1.G
