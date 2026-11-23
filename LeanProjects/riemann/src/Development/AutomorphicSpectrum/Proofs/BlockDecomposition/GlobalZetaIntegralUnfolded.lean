import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.VerticalStrips.UnramifiedEulerProductIntegral
import GroundTheory.AutomorphicForms.GL2.IdeleModuleDetOfMemMaxCompact

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Filter Topology
open GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.GodementSection (localChar adeleAt glAt restrictedTensor2 godementSection archSection partialLFunction modPow)
open GroundTheory.Automorphic.Reduction (finAt infAt maxCompact)
open scoped NumberField.AdeleRing ValuativeRel ENNReal ComplexConjugate

namespace GlobalTheory.CompanionTheory.RankinUnfold

open Ad3 Ad3.R

theorem pri_eq (α : ℚˣ) : pri α = IdeleGroup.diagonal ℚ α := by
  rfl

theorem md_pri_mul (α : ℚˣ) (a : Jd) : md (pri α * a) = md a := by
  unfold md
  rw [pri_eq, map_mul, IdeleGroup.ideleModule_diagonal, one_mul]

theorem modPow_pri_mul (α : ℚˣ) (a : Jd) (s : ℂ) : modPow (pri α * a) s = modPow a s := by
  unfold modPow
  rw [pri_eq, map_mul, IdeleGroup.ideleModule_diagonal, one_mul]

theorem char_pri_mul (c : HeckeCharacter ℚ) (α : ℚˣ) (a : Jd) :
    c.toIdele (pri α * a) = c.toIdele a := by
  rw [pri_eq, map_mul, HeckeCharacter.toIdele_diagonal, one_mul]

theorem continuous_left_torus_embedding : Continuous (fun a : Jd => (dg2 a 1 : G2)) := by
  refine Units.continuous_iff.mpr ⟨?_, ?_⟩
  · unfold dg2
    refine continuous_pi fun i => continuous_pi fun j => ?_
    fin_cases i <;> fin_cases j <;> simp <;> fun_prop
  · unfold dg2
    refine continuous_pi fun i => continuous_pi fun j => ?_
    fin_cases i <;> fin_cases j <;> simp <;> fun_prop

private theorem continuous_det_lemma : Continuous (fun g : G2 => (GeneralLinearGroup.det g : Jd)) := by
  refine Units.continuous_iff.mpr ⟨?_, ?_⟩
  · show Continuous (fun g : G2 => ((g : Matrix (Fin 2) (Fin 2) 𝔸[ℚ])).det)
    exact Units.continuous_val.matrix_det
  · show Continuous (fun g : G2 => (((g⁻¹ : G2) : Matrix (Fin 2) (Fin 2) 𝔸[ℚ])).det)
    exact (Units.continuous_val.comp continuous_inv).matrix_det

theorem continuous_cdet (c : HeckeCharacter ℚ) : Continuous (cdet c) := by
  unfold cdet
  first
    | exact continuous_subtype_val.comp ((HeckeCharacter.continuous_toIdele c).comp continuous_det_lemma)
    | exact Circle.continuous_coe.comp ((HeckeCharacter.continuous_toIdele c).comp continuous_det_lemma)
    | fun_prop

theorem continuous_Dt : Continuous Dt := by
  unfold Dt md
  exact continuous_subtype_val.comp (IdeleGroup.continuous_ideleModule.comp continuous_det_lemma)

theorem continuous_modPow (s : ℂ) : Continuous (fun a : Jd => modPow a s) := by
  unfold modPow
  refine Continuous.cpow ?_ continuous_const ?_
  · exact Complex.continuous_ofReal.comp (continuous_subtype_val.comp IdeleGroup.continuous_ideleModule)
  · intro a
    exact Complex.ofReal_mem_slitPlane.mpr (IdeleGroup.ideleModule ℚ a).2

theorem fd_unfold {𝓓 : Set Jd} (hm : MeasurableSet 𝓓) (hu : ∀ a : Jd, ∃! α : ℚˣ, pri α * a ∈ 𝓓)
    (f : Jd → ℂ) (hf : Continuous f)
    (hfin : ∫⁻ a in 𝓓, ∑' α : ℚˣ, ‖f (pri α * a)‖ₑ ∂ideleMeasure ℚ < ∞) :
    ∫ a in 𝓓, ∑' α : ℚˣ, f (pri α * a) ∂ideleMeasure ℚ = ∫ a, f a ∂ideleMeasure ℚ := by
  haveI : Countable ℚˣ := Function.Injective.countable (fun a b h => Units.ext h)
  have hpinv : ∀ α : ℚˣ, pri α⁻¹ = (pri α)⁻¹ := fun α => by rw [pri_eq, pri_eq, map_inv]
  let S : ℚˣ → Set Jd := fun α => (fun b => (pri α)⁻¹ * b) ⁻¹' 𝓓
  have hSm : ∀ α, MeasurableSet (S α) := fun α => (measurable_const_mul _) hm
  have hpre : ∀ α, (fun a => pri α * a) ⁻¹' S α = 𝓓 := by
    intro α
    ext a
    simp only [S, Set.mem_preimage, inv_mul_cancel_left]
  have hcov : (⋃ α, S α) = Set.univ := by
    refine Set.eq_univ_of_forall fun b => Set.mem_iUnion.mpr ?_
    obtain ⟨α, hα, -⟩ := hu b
    refine ⟨α⁻¹, ?_⟩
    show (pri α⁻¹)⁻¹ * b ∈ 𝓓
    rwa [hpinv, inv_inv]
  have hdisj : Pairwise (Function.onFun Disjoint S) := by
    intro α β hne
    refine Set.disjoint_left.mpr fun b hbα hbβ => hne ?_
    obtain ⟨γ, -, huq⟩ := hu b
    have h1 : α⁻¹ = γ := huq α⁻¹ (by show pri α⁻¹ * b ∈ 𝓓; rw [hpinv]; exact hbα)
    have h2 : β⁻¹ = γ := huq β⁻¹ (by show pri β⁻¹ * b ∈ 𝓓; rw [hpinv]; exact hbβ)
    exact inv_injective (h1.trans h2.symm)
  have hmp : ∀ α : ℚˣ, MeasurePreserving (fun a => pri α * a) (ideleMeasure ℚ) (ideleMeasure ℚ) :=
    fun α => measurePreserving_mul_left (ideleMeasure ℚ) (pri α)
  have hemb : ∀ α : ℚˣ, MeasurableEmbedding (fun a : Jd => pri α * a) :=
    fun α => measurableEmbedding_mulLeft (pri α)
  have hint : ∀ α : ℚˣ, ∫ a in 𝓓, f (pri α * a) ∂ideleMeasure ℚ = ∫ b in S α, f b ∂ideleMeasure ℚ := by
    intro α
    rw [← (hmp α).setIntegral_preimage_emb (hemb α) f (S α), hpre]
  have hlint : ∀ α : ℚˣ, ∫⁻ a in 𝓓, ‖f (pri α * a)‖ₑ ∂ideleMeasure ℚ =
      ∫⁻ b in S α, ‖f b‖ₑ ∂ideleMeasure ℚ := by
    intro α
    rw [← (hmp α).setLIntegral_comp_preimage_emb (hemb α) (fun b => ‖f b‖ₑ) (S α), hpre]
  have hfm : ∀ α : ℚˣ, Continuous (fun a => f (pri α * a)) :=
    fun α => hf.comp (continuous_const.mul continuous_id)
  have hsum : ∑' α : ℚˣ, ∫⁻ a in 𝓓, ‖f (pri α * a)‖ₑ ∂ideleMeasure ℚ =
      ∫⁻ a in 𝓓, ∑' α : ℚˣ, ‖f (pri α * a)‖ₑ ∂ideleMeasure ℚ :=
    (lintegral_tsum fun α => ((hfm α).measurable.enorm).aemeasurable).symm
  have hfint : Integrable f (ideleMeasure ℚ) := by
    refine ⟨hf.aestronglyMeasurable, ?_⟩
    unfold HasFiniteIntegral
    rw [← setLIntegral_univ, ← hcov, lintegral_iUnion hSm hdisj]
    simp_rw [← hlint]
    rw [hsum]
    exact hfin
  rw [integral_tsum (fun α => (hfm α).aestronglyMeasurable) (by rw [hsum]; exact hfin.ne)]
  simp_rw [hint]
  rw [← integral_iUnion hSm hdisj hfint.integrableOn, hcov, Measure.restrict_univ]

theorem enorm_circle (u : Circle) : ‖(u : ℂ)‖ₑ = 1 := by
  first
    | rw [← ofReal_norm, Circle.norm_coe, ENNReal.ofReal_one]
    | simp

theorem enorm_modPow (a : Jd) (s : ℂ) : ‖modPow a s‖ₑ = ENNReal.ofReal (md a ^ s.re) := by
  rw [← ofReal_norm]
  unfold modPow md
  rw [Complex.norm_cpow_eq_rpow_re_of_pos (IdeleGroup.ideleModule ℚ a).2]

theorem md_pos (a : Jd) : 0 < md a := by
  unfold md
  exact (IdeleGroup.ideleModule ℚ a).2

theorem det_unipotent_adele (x : 𝔸[ℚ]) : GeneralLinearGroup.det (uni2 x : G2) = 1 := by
  first
    | (ext; simp [uni2, Matrix.det_fin_two])
    | (unfold uni2; ext; simp [Matrix.det_fin_two])

theorem det_diagonal_two (a b : Jd) : GeneralLinearGroup.det (dg2 a b : G2) = a * b := by
  first
    | (ext; simp [dg2, Matrix.det_fin_two])
    | (unfold dg2; ext; simp [Matrix.det_fin_two])

theorem det_pt (x : 𝔸[ℚ]) (a z : Jd) (κ : G2) :
    GeneralLinearGroup.det (pt x a z κ) = a * (z * z) * GeneralLinearGroup.det κ := by
  unfold pt
  simp only [map_mul, det_unipotent_adele, det_diagonal_two, one_mul, mul_one]

theorem det_rationalEmbedding (γ : GL (Fin 2) ℚ) : GeneralLinearGroup.det (dia2 γ) = pri (GeneralLinearGroup.det γ) := by
  ext
  simp [dia2, pri, AdelicGLn.diagonal, Matrix.GeneralLinearGroup.val_det_apply, RingHom.map_det]

theorem central_diagonal_commute (z : Jd) (g : G2) : g * dg2 z z = dg2 z z * g := by
  ext i j
  simp only [Units.val_mul]
  unfold dg2
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, mul_comm]

theorem central_pt {H : G2 → ℂ} (hc : CInv H) (x : 𝔸[ℚ]) (a z : Jd) (κ : G2) :
    H (pt x a z κ) = H (uni2 x * dg2 a 1 * κ) := by
  have h1 : pt x a z κ = (uni2 x * dg2 a 1 * dg2 z z) * κ := rfl
  rw [h1, central_diagonal_commute z (uni2 x * dg2 a 1), mul_assoc]
  exact hc z _

private theorem md_mul_lemma (a b : Jd) : md (a * b) = md a * md b := by
  unfold md
  rw [map_mul]
  rfl

private theorem cpow_pos_lemma {x : ℝ} (hx : 0 < x) (s : ℂ) :
    (x : ℂ) ^ s = Complex.exp ((Real.log x : ℂ) * s) := by
  rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast hx.ne'), Complex.ofReal_log hx.le]

private theorem scal_lemma {p q r : ℝ} (hp : 0 < p) (hq : 0 < q) (hr : 0 < r) (s : ℂ) :
    ((p * (q * q) * r : ℝ) : ℂ) ^ s * ((p⁻¹ : ℝ) : ℂ) =
      (p : ℂ) ^ (s - 1) * (q : ℂ) ^ (2 * s) * (r : ℂ) ^ s := by
  have h1 : 0 < p * (q * q) := mul_pos hp (mul_pos hq hq)
  have h2 : 0 < p * (q * q) * r := mul_pos h1 hr
  have hinv : ((p⁻¹ : ℝ) : ℂ) = Complex.exp (-(Real.log p : ℂ)) := by
    rw [← Complex.ofReal_neg, ← Complex.ofReal_exp, Real.exp_neg, Real.exp_log hp]
  rw [cpow_pos_lemma h2, cpow_pos_lemma hp, cpow_pos_lemma hq, cpow_pos_lemma hr, hinv,
    Real.log_mul h1.ne' hr.ne', Real.log_mul hp.ne' (mul_pos hq hq).ne', Real.log_mul hq.ne' hq.ne']
  simp only [← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem pt_formula {H : G2 → ℂ} (hc : CInv H) (c : HeckeCharacter ℚ) (Φ : (Fin 2 → 𝔸[ℚ]) → ℂ) (s : ℂ)
    (x : 𝔸[ℚ]) (a z : Jd) (κ : G2) :
    (H (pt x a z κ) * cdet c (pt x a z κ) * ((Dt (pt x a z κ) : ℝ) : ℂ) ^ s) * Φ (lrow z κ) *
        (((md a)⁻¹ : ℝ) : ℂ) =
      H (uni2 x * dg2 a 1 * κ) * ((c.toIdele a : ℂ) * modPow a (s - 1)) *
        (Φ (lrow z κ) * ((c * c⁻¹⁻¹).toIdele z : ℂ) * ((IdeleGroup.ideleModule ℚ z : ℝ) : ℂ) ^ (2 * s)) *
        ((c.toIdele (GeneralLinearGroup.det κ) : ℂ) * modPow (GeneralLinearGroup.det κ) s) := by
  rw [central_pt hc]
  have hA := md_pos a
  have hZ := md_pos z
  have hK := md_pos (GeneralLinearGroup.det κ)
  have e1 : cdet c (pt x a z κ) = (c.toIdele a : ℂ) * ((c.toIdele z : ℂ) * (c.toIdele z : ℂ)) *
      (c.toIdele (GeneralLinearGroup.det κ) : ℂ) := by
    unfold cdet
    rw [det_pt, map_mul, map_mul, map_mul]
    push_cast
    ring
  have e2 : Dt (pt x a z κ) = md a * (md z * md z) * md (GeneralLinearGroup.det κ) := by
    unfold Dt
    rw [det_pt, md_mul_lemma, md_mul_lemma, md_mul_lemma]
  have e3 : ((c * c⁻¹⁻¹).toIdele z : ℂ) = (c.toIdele z : ℂ) * (c.toIdele z : ℂ) := by
    rw [inv_inv]
    first
      | rfl
      | simp [HeckeCharacter.toIdele_apply]
  have e4 : ((IdeleGroup.ideleModule ℚ z : ℝ) : ℂ) = ((md z : ℝ) : ℂ) := rfl
  have e5 : modPow a (s - 1) = ((md a : ℝ) : ℂ) ^ (s - 1) := rfl
  have e6 : modPow (GeneralLinearGroup.det κ) s = ((md (GeneralLinearGroup.det κ) : ℝ) : ℂ) ^ s := rfl
  rw [e1, e2, e3, e4, e5, e6]
  have key := scal_lemma hA hZ hK s
  linear_combination (H (uni2 x * dg2 a 1 * κ) * ((c.toIdele a : ℂ) * ((c.toIdele z : ℂ) * (c.toIdele z : ℂ)) *
    (c.toIdele (GeneralLinearGroup.det κ) : ℂ)) * Φ (lrow z κ)) * key

theorem torus {μ : Measure G2} {𝓕 : Set G2} {mK : Measure KA} {𝓓 : Set Jd} (hS : Set0 μ 𝓕 mK 𝓓)
    {H P : G2 → ℂ} (hP : Par H P) (c : HeckeCharacter ℚ) {s : ℂ} (hs : 1 < s.re) (κ : KA) :
    ∫ a in 𝓓, (∫ x in fundamentalSet ℚ, H (uni2 x * dg2 a 1 * κ.1) ∂adeleMeasure ℚ) *
      ((c.toIdele a : ℂ) * modPow a (s - 1)) ∂ideleMeasure ℚ = Ag P c s κ.1 := by
  obtain ⟨M, hM⟩ : ∃ M : ℕ, s.re - 1 < M := exists_nat_gt _
  obtain ⟨C, hC⟩ := hP.bd M
  set f : Jd → ℂ := fun b => P (dg2 b 1 * κ.1) * ((c.toIdele b : ℂ) * modPow b (s - 1)) with hf
  have hpt : ∀ a : Jd, (∫ x in fundamentalSet ℚ, H (uni2 x * dg2 a 1 * κ.1) ∂adeleMeasure ℚ) *
      ((c.toIdele a : ℂ) * modPow a (s - 1)) = ∑' α : ℚˣ, f (pri α * a) := by
    intro a
    rw [← (hP.sum a κ).tsum_eq, ← tsum_mul_right]
    refine tsum_congr fun α => ?_
    simp only [hf, char_pri_mul, modPow_pri_mul]
  have hcc : Continuous (fun b : Jd => (c.toIdele b : ℂ)) := by
    first
      | exact continuous_subtype_val.comp (HeckeCharacter.continuous_toIdele c)
      | exact Circle.continuous_coe.comp (HeckeCharacter.continuous_toIdele c)
      | fun_prop
  have hfc : Continuous f :=
    (hP.cont.comp (continuous_left_torus_embedding.mul continuous_const)).mul (hcc.mul (continuous_modPow _))
  have hτ : 0 < s.re - 1 := by linarith
  have hbound : ∀ a : Jd, ∑' α : ℚˣ, ‖f (pri α * a)‖ₑ ≤
      ENNReal.ofReal (max C 0) * ENNReal.ofReal (min 1 (md a)⁻¹ ^ M * md a ^ (s.re - 1)) := by
    intro a
    have e : ∀ α : ℚˣ, ‖f (pri α * a)‖ₑ =
        ‖P (dg2 (pri α * a) 1 * κ.1)‖ₑ * ENNReal.ofReal (md a ^ (s.re - 1)) := by
      intro α
      simp only [hf, enorm_mul, enorm_circle, one_mul, enorm_modPow, md_pri_mul, Complex.sub_re,
        Complex.one_re]
    simp_rw [e]
    rw [ENNReal.tsum_mul_right]
    have hm : 0 ≤ min 1 (md a)⁻¹ ^ M :=
      pow_nonneg (le_min zero_le_one (inv_nonneg.mpr (md_pos a).le)) M
    calc (∑' α : ℚˣ, ‖P (dg2 (pri α * a) 1 * κ.1)‖ₑ) * ENNReal.ofReal (md a ^ (s.re - 1))
        ≤ ENNReal.ofReal (C * min 1 (md a)⁻¹ ^ M) * ENNReal.ofReal (md a ^ (s.re - 1)) := by
          gcongr
          exact hC a κ
      _ ≤ ENNReal.ofReal (max C 0 * min 1 (md a)⁻¹ ^ M) * ENNReal.ofReal (md a ^ (s.re - 1)) := by
          gcongr
          exact le_max_left _ _
      _ = ENNReal.ofReal (max C 0) * ENNReal.ofReal (min 1 (md a)⁻¹ ^ M * md a ^ (s.re - 1)) := by
          rw [ENNReal.ofReal_mul (le_max_right _ _), ENNReal.ofReal_mul hm, mul_assoc]
  have hfin : ∫⁻ a in 𝓓, ∑' α : ℚˣ, ‖f (pri α * a)‖ₑ ∂ideleMeasure ℚ < ∞ := by
    calc ∫⁻ a in 𝓓, ∑' α : ℚˣ, ‖f (pri α * a)‖ₑ ∂ideleMeasure ℚ
        ≤ ∫⁻ a in 𝓓, ENNReal.ofReal (max C 0) *
            ENNReal.ofReal (min 1 (md a)⁻¹ ^ M * md a ^ (s.re - 1)) ∂ideleMeasure ℚ :=
          lintegral_mono hbound
      _ = ENNReal.ofReal (max C 0) *
            ∫⁻ a in 𝓓, ENNReal.ofReal (min 1 (md a)⁻¹ ^ M * md a ^ (s.re - 1)) ∂ideleMeasure ℚ :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ < ∞ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top (hS.finD (s.re - 1) M hτ hM)
  rw [integral_congr_ae (Filter.Eventually.of_forall hpt), fd_unfold hS.measD hS.uniqD f hfc hfin]
  unfold Ag
  refine integral_congr_ae (Filter.Eventually.of_forall fun b => ?_)
  simp only [hf]
  ring

theorem unfolding : Ad3.R.G2c → Ad3.R.G3 → Ad3.R.G3a → Ad3.R.G5 := by
  intro hG2c hG3 hG3a μ 𝓕 mK 𝓓 C hS hC H P hH hP Φ hΦ c s hs
  obtain ⟨hΦc, -⟩ := hG3a Φ hΦ
  obtain ⟨-, -, hfin⟩ := hG3 μ 𝓕 mK 𝓓 hS H hH Φ hΦ s.re hs
  have hDt : ∀ g : G2, 0 < Dt g := fun g => md_pos _
  have hH1c : Continuous (fun g : G2 => H g * cdet c g * ((Dt g : ℝ) : ℂ) ^ s) :=
    (hH.cont.mul (continuous_cdet c)).mul
      ((Complex.continuous_ofReal.comp continuous_Dt).cpow continuous_const
        (fun g => Complex.ofReal_mem_slitPlane.mpr (hDt g)))
  have hH1L : LInv (fun g : G2 => H g * cdet c g * ((Dt g : ℝ) : ℂ) ^ s) := by
    intro γ g
    have hdet : GeneralLinearGroup.det (dia2 γ * g) =
        pri (GeneralLinearGroup.det γ) * GeneralLinearGroup.det g := by
      rw [map_mul, det_rationalEmbedding]
    have h1 : cdet c (dia2 γ * g) = cdet c g := by
      unfold cdet
      rw [hdet, char_pri_mul]
    have h2 : Dt (dia2 γ * g) = Dt g := by
      unfold Dt
      rw [hdet, md_pri_mul]
    dsimp only
    rw [hH.left γ g, h1, h2]
  have hfin1 : ∫⁻ g in 𝓕, ‖H g * cdet c g * ((Dt g : ℝ) : ℂ) ^ s‖ₑ *
      ∑' ξ : NZ, ‖Φ (row ξ g)‖ₑ ∂μ < ⊤ := by
    refine lt_of_eq_of_lt (lintegral_congr fun g => ?_) hfin
    have hc1 : ‖cdet c g‖ₑ = 1 := enorm_circle _
    have hn : ‖((Dt g : ℝ) : ℂ) ^ s‖ₑ = ENNReal.ofReal (Dt g ^ s.re) := by
      rw [← ofReal_norm, Complex.norm_cpow_eq_rpow_re_of_pos (hDt g)]
    rw [enorm_mul, enorm_mul, hc1, mul_one, hn]
  have hmain := hG2c μ 𝓕 mK 𝓓 C hS hC (fun g : G2 => H g * cdet c g * ((Dt g : ℝ) : ℂ) ^ s) Φ
    hH1c.measurable hH1L hΦc.measurable hfin1
  beta_reduce at hmain
  unfold Zg Jg
  rw [hmain]
  congr 1
  refine integral_congr_ae (Filter.Eventually.of_forall fun κ => ?_)
  simp_rw [pt_formula hH.cen c Φ s]
  simp_rw [integral_mul_const, integral_const_mul]
  rw [torus hS hP c hs κ]
  have hz : ∫ z, Φ (lrow z κ.1) * ((c * c⁻¹⁻¹).toIdele z : ℂ) *
      ((IdeleGroup.ideleModule ℚ z : ℝ) : ℂ) ^ (2 * s) ∂ideleMeasure ℚ =
      globalZeta (GodementSection.slice Φ κ.1) (c * c⁻¹⁻¹) (2 * s) := rfl
  rw [hz]
  unfold godementSection GodementSection.detI
  ring

end GlobalTheory.CompanionTheory.RankinUnfold
end
