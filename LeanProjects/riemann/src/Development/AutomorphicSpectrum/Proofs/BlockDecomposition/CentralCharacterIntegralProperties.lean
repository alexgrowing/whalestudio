import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.VerticalStrips.UnramifiedEulerProductIntegral

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Filter Topology
open GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.GodementSection (localChar adeleAt glAt restrictedTensor2 godementSection archSection partialLFunction modPow)
open GroundTheory.Automorphic.GL2Classical (realEmb realPart Gamma0Level archLift)
open GroundTheory.Automorphic.Reduction (finAt infAt maxCompact)
open GroundTheory.Automorphic.GLnLocal (integralGL)
open scoped NumberField.AdeleRing ValuativeRel ENNReal ComplexConjugate SchwartzMap Classical

namespace GlobalTheory.CompanionTheory.FundamentalDomainCentralCharacter
open Ad3.R Ad3

theorem countable_range : Countable (AdelicGLn.diagonal ℚ 2).range := by
  haveI : Countable (Matrix (Fin 2) (Fin 2) ℚ) := inferInstanceAs (Countable (Fin 2 → Fin 2 → ℚ))
  haveI : Countable (GL (Fin 2) ℚ) := Function.Injective.countable (f := fun u : GL (Fin 2) ℚ => (u.val, u.inv)) (fun a b h => Units.ext (congrArg Prod.fst h))
  exact (Set.countable_range (AdelicGLn.diagonal ℚ 2)).to_subtype

theorem md_pos (a : Jd) : 0 < md a := (IdeleGroup.ideleModule ℚ a).2
theorem md_mul (a b : Jd) : md (a * b) = md a * md b := by
  simp [md, map_mul]
theorem md_one : md 1 = 1 := by simp [md]
theorem continuous_md : Continuous md := continuous_subtype_val.comp IdeleGroup.continuous_ideleModule
theorem continuous_Dt : Continuous Dt := continuous_md.comp (AdelicGLn.continuous_det ℚ 2)
theorem Dt_pos (g : G2) : 0 < Dt g := md_pos _
theorem Dt_mul (g h : G2) : Dt (g * h) = Dt g * Dt h := by
  simp [Dt, map_mul, md_mul]
theorem Dt_inv (g : G2) : Dt g⁻¹ = (Dt g)⁻¹ := by
  have := Dt_mul g g⁻¹
  have h1 : Dt (1 : G2) = 1 := by simp [Dt, md_one]
  rw [mul_inv_cancel, h1] at this
  exact eq_inv_of_mul_eq_one_right this.symm
theorem Dt_dia (γ : GL (Fin 2) ℚ) : Dt (dia2 γ) = 1 := by
  have := Reduction.rationalGL_le_normOneGL (K := ℚ) (n := 2) ⟨γ, rfl⟩
  rw [Reduction.mem_normOneGL] at this
  exact this
theorem Dt_central (z : Jd) : Dt (dg2 z z) = md z ^ 2 := by
  have : GeneralLinearGroup.det (dg2 z z) = z * z := by
    ext
    simp [dg2, Matrix.det_fin_two]
  rw [Dt, this, md_mul, sq]

theorem exists_ne_one {η : HeckeCharacter ℚ} (h : η ≠ 1) : ∃ z : Jd, η.toIdele z ≠ 1 := by
  by_contra hc
  push_neg at hc
  apply h
  ext x
  obtain ⟨z, rfl⟩ := QuotientGroup.mk_surjective x
  have := hc z
  rw [HeckeCharacter.toIdele_apply] at this
  show ((η (IdeleClassGroup.mk ℚ z) : Circle) : ℂ) = ((1 : Circle) : ℂ)
  rw [this]

open scoped Pointwise

theorem measurableSet_band : MeasurableSet band := by
  have : band = Dt ⁻¹' Set.Ico 1 2 := by
    ext g; simp [band]
  rw [this]
  exact continuous_Dt.measurable measurableSet_Ico

theorem mem_band_dia {γ : GL (Fin 2) ℚ} {g : G2} : dia2 γ * g ∈ band ↔ g ∈ band := by
  simp [band, Dt_mul, Dt_dia]

theorem fundamental_domain_integral_central_vanishing : Ad3.R.G1a → Ad3.R.G1 := by
  intro hA μ 𝓕 mK 𝓓 hS F hF hB hL
  haveI := hS.haar
  haveI := hS.right
  obtain ⟨-, hz, hT⟩ := hA μ 𝓕 mK 𝓓 hS
  have hbM := measurableSet_band
  have Fm : Measurable F := hF.measurable
  have hIndL : LInv (band.indicator F) := by
    intro γ g
    by_cases hg : g ∈ band
    · rw [Set.indicator_of_mem hg, Set.indicator_of_mem (mem_band_dia.2 hg), hL]
    · rw [Set.indicator_of_notMem hg, Set.indicator_of_notMem (fun h => hg (mem_band_dia.1 h))]
  have hIndM : Measurable (band.indicator F) := Fm.indicator hbM
  have hI : ∀ f : G2 → ℂ, ∫ g in 𝓕 ∩ band, f g ∂μ = ∫ g in 𝓕, band.indicator f g ∂μ :=
    fun f => (setIntegral_indicator hbM).symm
  refine ⟨?_, ?_, ?_⟩
  · intro hC h
    obtain ⟨z, hz1, -⟩ := hz (Dt h)⁻¹ (inv_pos.2 (Dt_pos h))
    set Bh : Set G2 := {g | g * h⁻¹ ∈ band} with hBh
    have hBhM : MeasurableSet Bh :=
      hbM.preimage (continuous_id.mul continuous_const).measurable
    have hBhL : LInv (Bh.indicator F) := by
      intro γ g
      have hm : dia2 γ * g ∈ Bh ↔ g ∈ Bh := by
        simp only [hBh, Set.mem_setOf_eq, mul_assoc, mem_band_dia]
      by_cases hg : g ∈ Bh
      · rw [Set.indicator_of_mem hg, Set.indicator_of_mem (hm.2 hg), hL]
      · rw [Set.indicator_of_notMem hg, Set.indicator_of_notMem (fun h => hg (hm.1 h))]
    have e1 : ∀ g, Bh.indicator F (g * h) = band.indicator (fun g => F (g * h)) g := by
      intro g
      have hm : g * h ∈ Bh ↔ g ∈ band := by simp [hBh]
      by_cases hg : g ∈ band
      · rw [Set.indicator_of_mem hg, Set.indicator_of_mem (hm.2 hg)]
      · rw [Set.indicator_of_notMem hg, Set.indicator_of_notMem (fun h => hg (hm.1 h))]
    have e2 : ∀ g, band.indicator F (dg2 z z * g) = Bh.indicator F g := by
      intro g
      have hm : dg2 z z * g ∈ band ↔ g ∈ Bh := by
        have : Dt (dg2 z z * g) = Dt (g * h⁻¹) := by
          rw [Dt_mul, Dt_mul, Dt_central, hz1, Dt_inv, mul_comm]
        simp only [hBh, Set.mem_setOf_eq, band, this]
      by_cases hg : g ∈ Bh
      · rw [Set.indicator_of_mem hg, Set.indicator_of_mem (hm.2 hg), hC]
      · rw [Set.indicator_of_notMem hg, Set.indicator_of_notMem (fun h => hg (hm.1 h))]
    rw [hI, hI]
    simp_rw [← e1]
    rw [(hT (fun g => g * h) (Or.inr (Or.inl ⟨h, rfl⟩))).2 _ (Fm.indicator hBhM) hBhL]
    simp_rw [← e2]
    exact (hT (fun g => dg2 z z * g) (Or.inr (Or.inr ⟨z, rfl⟩))).2 _ hIndM hIndL
  · intro η hη hc hne
    obtain ⟨z0, h0⟩ := exists_ne_one hne
    obtain ⟨z1, hz1, hz1'⟩ := hz ((md z0) ^ 2)⁻¹ (inv_pos.2 (pow_pos (md_pos _) 2))
    set z : Jd := z0 * z1 with hzdef
    have hmd : md z ^ 2 = 1 := by
      rw [hzdef, md_mul, mul_pow, hz1]
      exact mul_inv_cancel₀ (pow_pos (md_pos _) 2).ne'
    have hηz : η.toIdele z ≠ 1 := by
      rw [hzdef, map_mul, hz1' η hη, mul_one]
      exact h0
    have hηz' : (η.toIdele z : ℂ) ≠ 1 := fun h => hηz (Circle.ext (by simpa using h))
    have e : ∀ g, band.indicator F (dg2 z z * g) = (η.toIdele z : ℂ) * band.indicator F g := by
      intro g
      have hm : dg2 z z * g ∈ band ↔ g ∈ band := by
        have : Dt (dg2 z z * g) = Dt g := by rw [Dt_mul, Dt_central, hmd, one_mul]
        simp only [band, Set.mem_setOf_eq, this]
      by_cases hg : g ∈ band
      · rw [Set.indicator_of_mem hg, Set.indicator_of_mem (hm.2 hg), hc]
      · rw [Set.indicator_of_notMem hg, Set.indicator_of_notMem (fun h => hg (hm.1 h)), mul_zero]
    have key := (hT (fun g => dg2 z z * g) (Or.inr (Or.inr ⟨z, rfl⟩))).2 _ hIndM hIndL
    simp_rw [e] at key
    rw [integral_const_mul] at key
    rw [hI]
    have : ((η.toIdele z : ℂ) - 1) * ∫ g in 𝓕, band.indicator F g ∂μ = 0 := by
      rw [sub_mul, one_mul, key, sub_self]
    exact (mul_eq_zero.1 this).resolve_left (sub_ne_zero.2 hηz')
  · intro hC hne hI0
    apply hne
    have hn : ∀ g, F g * conj (F g) = ((Complex.normSq (F g) : ℝ) : ℂ) := fun g => Complex.mul_conj _
    simp_rw [hn] at hI0
    rw [integral_complex_ofReal] at hI0
    have hI1 : ∫ g in 𝓕 ∩ band, Complex.normSq (F g) ∂μ = 0 := by exact_mod_cast hI0
    obtain ⟨C, hCb⟩ := hB
    have hmeas : MeasurableSet (𝓕 ∩ band) := hS.meas.inter hbM
    have hint : IntegrableOn (fun g => Complex.normSq (F g)) (𝓕 ∩ band) μ := by
      refine Measure.integrableOn_of_bounded (M := C ^ 2) hS.vol.ne
        (Complex.continuous_normSq.comp hF).aestronglyMeasurable ?_
      refine Eventually.of_forall fun g => ?_
      rw [Real.norm_of_nonneg (Complex.normSq_nonneg _), Complex.normSq_eq_norm_sq]
      exact pow_le_pow_left₀ (norm_nonneg _) (hCb g) 2
    have hae := (setIntegral_eq_zero_iff_of_nonneg_ae
      (Eventually.of_forall fun g => Complex.normSq_nonneg (F g)) hint).1 hI1
    set t : Set G2 := band ∩ {g | F g ≠ 0} with ht
    have h0 : μ (t ∩ 𝓕) = 0 := by
      have h1 := (ae_iff.1 ((ae_restrict_iff' hmeas).1 hae))
      refine measure_mono_null ?_ h1
      rintro g ⟨⟨hb, hf⟩, hg⟩
      simp only [Set.mem_setOf_eq, not_forall]
      exact ⟨⟨hg, hb⟩, by simpa using hf⟩
    have hinv : ∀ γ ∈ (AdelicGLn.diagonal ℚ 2).range, ∀ x : G2, γ * x ∈ t ↔ x ∈ t := by
      rintro _ ⟨δ, rfl⟩ x
      have e1 := hL δ x
      simp only [ht, Set.mem_inter_iff, Set.mem_setOf_eq]
      rw [show AdelicGLn.diagonal ℚ 2 δ * x = dia2 δ * x from rfl, mem_band_dia, e1]
    have hts : ∀ γ : (AdelicGLn.diagonal ℚ 2).range, γ • t = t := by
      intro γ
      ext x
      rw [Set.mem_smul_set_iff_inv_smul_mem, Subgroup.smul_def, smul_eq_mul]
      exact hinv _ (γ⁻¹).2 x
    haveI := countable_range
    have hμt : μ t = 0 := hS.fd.measure_zero_of_invariant t hts h0
    set U : Set G2 := {g | 1 < Dt g ∧ Dt g < 2 ∧ F g ≠ 0} with hU
    have hUo : IsOpen U := by
      refine (isOpen_lt continuous_const continuous_Dt).inter
        ((isOpen_lt continuous_Dt continuous_const).inter (isOpen_ne_fun hF continuous_const))
    have hU0 : U = ∅ := hUo.eq_empty_of_measure_zero
      (measure_mono_null (show U ⊆ t from fun g hg => ⟨⟨hg.1.le, hg.2.1⟩, hg.2.2⟩) hμt)
    funext g
    by_contra hg
    obtain ⟨z, hz1, -⟩ := hz (3 / 2 / Dt g) (div_pos (by norm_num) (Dt_pos g))
    have hD : Dt (dg2 z z * g) = 3 / 2 := by
      rw [Dt_mul, Dt_central, hz1, div_mul_cancel₀ _ (Dt_pos g).ne']
    have hmem : dg2 z z * g ∈ U := by
      refine ⟨by rw [hD]; norm_num, by rw [hD]; norm_num, ?_⟩
      rw [hC]
      exact hg
    rw [hU0] at hmem
    exact hmem

end GlobalTheory.CompanionTheory.FundamentalDomainCentralCharacter
