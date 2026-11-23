import Mathlib
import GroundTheory.AutomorphicForms.HaarSK
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.VerticalStrips.UnramifiedEulerProductIntegral

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Filter Topology
open GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.Reduction (finAt infAt maxCompact adelicBorel)
open scoped NumberField.AdeleRing ValuativeRel ENNReal ComplexConjugate

namespace GlobalTheory.CompanionTheory.RSCoord

open Ad3 Ad3.R

abbrev Xc : Type := Jd × Jd × 𝔸[ℚ]

abbrev Bo : Type := (adelicBorel : Subgroup G2)

theorem continuous_unipotentGL2 : Continuous (uni2 : 𝔸[ℚ] → GL (Fin 2) 𝔸[ℚ]) := by
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp [uni2] <;> fun_prop
  · refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp [uni2] <;> fun_prop

theorem continuous_diagGL2 : Continuous (fun p : Jd × Jd => (dg2 p.1 p.2 : GL (Fin 2) 𝔸[ℚ])) := by
  have h1 : Continuous (fun a : Jd => (a : 𝔸[ℚ])) := Units.continuous_val
  have h2 : Continuous (fun a : Jd => ((a⁻¹ : Jd) : 𝔸[ℚ])) := Units.continuous_val.comp continuous_inv
  have f1 : Continuous (fun p : Jd × Jd => (p.1 : 𝔸[ℚ])) := h1.comp continuous_fst
  have f2 : Continuous (fun p : Jd × Jd => (p.2 : 𝔸[ℚ])) := h1.comp continuous_snd
  have f3 : Continuous (fun p : Jd × Jd => ((p.1⁻¹ : Jd) : 𝔸[ℚ])) := h2.comp continuous_fst
  have f4 : Continuous (fun p : Jd × Jd => ((p.2⁻¹ : Jd) : 𝔸[ℚ])) := h2.comp continuous_snd
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp [dg2] <;> first | exact f1 | exact f2 | exact continuous_const
  · refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp [dg2] <;> first | exact f3 | exact f4 | exact continuous_const

theorem pt_val (x : 𝔸[ℚ]) (a z : Jd) :
    ((uni2 x * dg2 a 1 * dg2 z z : GL (Fin 2) 𝔸[ℚ]) : Matrix (Fin 2) (Fin 2) 𝔸[ℚ]) =
      !![(a : 𝔸[ℚ]) * z, x * z; 0, z] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [uni2, dg2, Matrix.mul_apply, Fin.sum_univ_two]

theorem cont_entry (i j : Fin 2) : Continuous (fun g : G2 => (g : Matrix (Fin 2) (Fin 2) 𝔸[ℚ]) i j) :=
  Continuous.matrix_elem (Units.continuous_val (M := Matrix (Fin 2) (Fin 2) 𝔸[ℚ])) i j

theorem bo_low (b : Bo) : (b.1 : Matrix (Fin 2) (Fin 2) 𝔸[ℚ]) 1 0 = 0 :=
  (Reduction.mem_adelicBorel.1 b.2) (by decide : (0 : Fin 2) < 1)

theorem bo_low_inv (b : Bo) : ((b.1⁻¹ : G2) : Matrix (Fin 2) (Fin 2) 𝔸[ℚ]) 1 0 = 0 :=
  (Reduction.mem_adelicBorel.1 (inv_mem b.2)) (by decide : (0 : Fin 2) < 1)

theorem bo_diag (b : Bo) (i : Fin 2) :
    (b.1 : Matrix (Fin 2) (Fin 2) 𝔸[ℚ]) i i * ((b.1⁻¹ : G2) : Matrix (Fin 2) (Fin 2) 𝔸[ℚ]) i i = 1 := by
  have h : ((b.1 * b.1⁻¹ : G2) : Matrix (Fin 2) (Fin 2) 𝔸[ℚ]) i i = (1 : Matrix (Fin 2) (Fin 2) 𝔸[ℚ]) i i := by
    rw [mul_inv_cancel]; rfl
  rw [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two] at h
  fin_cases i
  · simpa [bo_low_inv b] using h
  · simpa [bo_low b] using h

def dE (b : Bo) (i : Fin 2) : Jd :=
  ⟨(b.1 : Matrix (Fin 2) (Fin 2) 𝔸[ℚ]) i i, ((b.1⁻¹ : G2) : Matrix (Fin 2) (Fin 2) 𝔸[ℚ]) i i,
    bo_diag b i, by rw [mul_comm]; exact bo_diag b i⟩

theorem continuous_dE (i : Fin 2) : Continuous (fun b : Bo => dE b i) := by
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · exact (cont_entry i i).comp continuous_subtype_val
  · exact (cont_entry i i).comp (continuous_inv.comp continuous_subtype_val)

theorem pt_mem (p : Xc) : (uni2 p.2.2 * dg2 p.2.1 1 * dg2 p.1 p.1 : G2) ∈ (adelicBorel : Subgroup G2) := by
  refine Reduction.mem_adelicBorel.2 ?_
  intro i j hij
  rw [pt_val]
  fin_cases i <;> fin_cases j <;> simp_all

def eB : Xc ≃ₜ Bo where
  toFun p := ⟨uni2 p.2.2 * dg2 p.2.1 1 * dg2 p.1 p.1, pt_mem p⟩
  invFun b := (dE b 1, dE b 0 * (dE b 1)⁻¹, (b.1 : Matrix (Fin 2) (Fin 2) 𝔸[ℚ]) 0 1 * (((dE b 1)⁻¹ : Jd) : 𝔸[ℚ]))
  left_inv := by
    rintro ⟨z, a, x⟩
    have h1 : dE ⟨_, pt_mem (z, a, x)⟩ 1 = z := Units.ext (by
      show ((uni2 x * dg2 a 1 * dg2 z z : GL (Fin 2) 𝔸[ℚ]) : Matrix (Fin 2) (Fin 2) 𝔸[ℚ]) 1 1 = z
      rw [pt_val]; simp)
    have h0 : dE ⟨_, pt_mem (z, a, x)⟩ 0 = a * z := Units.ext (by
      show ((uni2 x * dg2 a 1 * dg2 z z : GL (Fin 2) 𝔸[ℚ]) : Matrix (Fin 2) (Fin 2) 𝔸[ℚ]) 0 0 = _
      rw [pt_val]; simp)
    simp only [h1, h0]
    refine Prod.ext rfl (Prod.ext (by simp) ?_)
    show ((uni2 x * dg2 a 1 * dg2 z z : GL (Fin 2) 𝔸[ℚ]) : Matrix (Fin 2) (Fin 2) 𝔸[ℚ]) 0 1 * ((z⁻¹ : Jd) : 𝔸[ℚ]) = x
    rw [pt_val]; simp [mul_assoc]
  right_inv := by
    intro b
    refine Subtype.ext (Units.ext ?_)
    rw [pt_val]
    have h : ((b.1 : Matrix (Fin 2) (Fin 2) 𝔸[ℚ]))⁻¹ 1 1 * (b.1 : Matrix (Fin 2) (Fin 2) 𝔸[ℚ]) 1 1 = 1 := by
      rw [mul_comm, ← Matrix.coe_units_inv]; exact bo_diag b 1
    ext i j
    fin_cases i <;> fin_cases j <;> simp [dE, bo_low b, mul_assoc, h]
  continuous_toFun := by
    refine Continuous.subtype_mk ?_ _
    have ha : Continuous (fun p : Xc => (dg2 p.2.1 1 : G2)) :=
      continuous_diagGL2.comp ((continuous_fst.comp continuous_snd).prodMk continuous_const)
    have hz : Continuous (fun p : Xc => (dg2 p.1 p.1 : G2)) :=
      continuous_diagGL2.comp (continuous_fst.prodMk continuous_fst)
    have hx : Continuous (fun p : Xc => (uni2 p.2.2 : G2)) :=
      continuous_unipotentGL2.comp (continuous_snd.comp continuous_snd)
    exact (hx.mul ha).mul hz
  continuous_invFun := by
    have h01 : Continuous (fun b : Bo => (b.1 : Matrix (Fin 2) (Fin 2) 𝔸[ℚ]) 0 1) :=
      (cont_entry 0 1).comp continuous_subtype_val
    have hi : Continuous (fun b : Bo => (((dE b 1)⁻¹ : Jd) : 𝔸[ℚ])) :=
      Units.continuous_val.comp (continuous_inv.comp (continuous_dE 1))
    exact (continuous_dE 1).prodMk (((continuous_dE 0).mul ((continuous_dE 1).inv)).prodMk (h01.mul hi))

theorem md_pos (a : Jd) : 0 < md a := (IdeleGroup.ideleModule ℚ a).2

theorem continuous_md : Continuous md :=
  continuous_subtype_val.comp (IdeleGroup.continuous_ideleModule (K := ℚ))

theorem md_mul (a b : Jd) : md (a * b) = md a * md b := by
  simp [md, map_mul]

theorem md_inv (a : Jd) : md a⁻¹ = (md a)⁻¹ := by
  simp [md, map_inv]

def wD (a : Jd) : ℝ≥0∞ := ENNReal.ofReal (md a)⁻¹

theorem measurable_wD : Measurable wD :=
  ENNReal.measurable_ofReal.comp (continuous_md.measurable.inv)

def wM : Measure Jd := (ideleMeasure ℚ).withDensity wD

instance : SFinite wM := by unfold wM; infer_instance

instance : IsLocallyFiniteMeasure wM :=
  IsLocallyFiniteMeasure.withDensity_ofReal (continuous_md.inv₀ fun a => (md_pos a).ne')

instance : wM.IsOpenPosMeasure :=
  Measure.AbsolutelyContinuous.isOpenPosMeasure (μ := ideleMeasure ℚ)
    (withDensity_absolutelyContinuous' measurable_wD.aemeasurable
      (Eventually.of_forall fun a => by simp [wD, md_pos a]))

def nu : Measure Xc := (ideleMeasure ℚ).prod (wM.prod (adeleMeasure ℚ))

instance : SFinite nu := by unfold nu; infer_instance

theorem map_wM (a₀ : Jd) : wM.map (a₀ * ·) = ENNReal.ofReal (md a₀) • wM := by
  refine Measure.ext_of_lintegral _ fun g hg => ?_
  have hm : Measurable (fun a : Jd => a₀ * a) := measurable_const_mul a₀
  rw [lintegral_map hg hm, lintegral_smul_measure, wM,
    lintegral_withDensity_eq_lintegral_mul _ measurable_wD (show Measurable (fun a => g (a₀ * a)) from hg.comp hm),
    lintegral_withDensity_eq_lintegral_mul _ measurable_wD hg, smul_eq_mul,
    ← lintegral_const_mul _ (measurable_wD.mul hg)]
  have h := lintegral_mul_left_eq_self (μ := ideleMeasure ℚ) (fun y => wD (a₀⁻¹ * y) * g y) a₀
  simp only [inv_mul_cancel_left] at h
  simp only [Pi.mul_apply]
  rw [h]
  refine lintegral_congr fun y => ?_
  have : wD (a₀⁻¹ * y) = ENNReal.ofReal (md a₀) * wD y := by
    simp only [wD, md_mul, md_inv, mul_inv, inv_inv]
    rw [ENNReal.ofReal_mul (md_pos a₀).le]
  rw [this, mul_assoc]

theorem map_aff (x₀ : 𝔸[ℚ]) (a₀ : Jd) :
    (adeleMeasure ℚ).map (fun x => x₀ + a₀ • x) = ENNReal.ofReal (md a₀)⁻¹ • adeleMeasure ℚ := by
  have h1 : Measurable (fun x : 𝔸[ℚ] => a₀ • x) := (continuous_const_smul a₀).measurable
  have h2 : Measurable (fun x : 𝔸[ℚ] => x₀ + x) := measurable_const_add x₀
  have h3 : (fun x : 𝔸[ℚ] => x₀ + a₀ • x) = (fun x => x₀ + x) ∘ (fun x => a₀ • x) := rfl
  rw [h3, ← Measure.map_map h2 h1, map_smul_adeleMeasure, Measure.map_smul, map_add_left_eq_self]
  rfl

def tr (z₀ a₀ : Jd) (x₀ : 𝔸[ℚ]) : Xc → Xc :=
  Prod.map (z₀ * ·) (Prod.map (a₀ * ·) (fun x => x₀ + a₀ • x))

theorem map_tr (z₀ a₀ : Jd) (x₀ : 𝔸[ℚ]) : nu.map (tr z₀ a₀ x₀) = nu := by
  have hz : Measurable (fun a : Jd => z₀ * a) := measurable_const_mul z₀
  have ha : Measurable (fun a : Jd => a₀ * a) := measurable_const_mul a₀
  have hx : Measurable (fun x : 𝔸[ℚ] => x₀ + a₀ • x) :=
    (measurable_const_add x₀).comp (continuous_const_smul a₀).measurable
  rw [nu, tr, ← Measure.map_prod_map _ _ hz (ha.prodMap hx), ← Measure.map_prod_map _ _ ha hx,
    map_mul_left_eq_self, map_wM, map_aff, Measure.prod_smul_left, Measure.prod_smul_right,
    Measure.prod_smul_right, Measure.prod_smul_right, smul_smul, ← ENNReal.ofReal_mul (md_pos a₀).le,
    mul_inv_cancel₀ (md_pos a₀).ne', ENNReal.ofReal_one, one_smul]

theorem eB_mul (z₀ a₀ : Jd) (x₀ : 𝔸[ℚ]) (p : Xc) :
    eB (z₀, a₀, x₀) * eB p = eB (tr z₀ a₀ x₀ p) := by
  obtain ⟨z, a, x⟩ := p
  refine Subtype.ext (Units.ext ?_)
  show ((uni2 x₀ * dg2 a₀ 1 * dg2 z₀ z₀ * (uni2 x * dg2 a 1 * dg2 z z) : GL (Fin 2) 𝔸[ℚ]) : Matrix (Fin 2) (Fin 2) 𝔸[ℚ]) =
    ((uni2 (x₀ + a₀ • x) * dg2 (a₀ * a) 1 * dg2 (z₀ * z) (z₀ * z) : GL (Fin 2) 𝔸[ℚ]) : Matrix (Fin 2) (Fin 2) 𝔸[ℚ])
  rw [Units.val_mul (uni2 x₀ * dg2 a₀ 1 * dg2 z₀ z₀), pt_val, pt_val, pt_val]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, Units.smul_def] <;> ring

instance : (nu.map eB).IsMulLeftInvariant := by
  refine ⟨fun b => ?_⟩
  obtain ⟨⟨z₀, a₀, x₀⟩, rfl⟩ := eB.surjective b
  have h : (fun s : Bo => eB (z₀, a₀, x₀) * s) ∘ eB = eB ∘ tr z₀ a₀ x₀ := funext (eB_mul z₀ a₀ x₀)
  have hT : Measurable (tr z₀ a₀ x₀) :=
    (measurable_const_mul z₀).prodMap ((measurable_const_mul a₀).prodMap
      ((measurable_const_add x₀).comp (continuous_const_smul a₀).measurable))
  rw [Measure.map_map (measurable_const_mul _) eB.measurable, h,
    ← Measure.map_map eB.measurable hT, map_tr]

instance : (nu.map eB).IsOpenPosMeasure := by
  have : nu.IsOpenPosMeasure := by unfold nu; infer_instance
  exact eB.continuous.isOpenPosMeasure_map eB.surjective

instance : IsFiniteMeasureOnCompacts (nu.map eB) := by
  have : IsFiniteMeasureOnCompacts nu := by unfold nu; infer_instance
  refine ⟨fun C hC => ?_⟩
  rw [Measure.map_apply eB.measurable hC.measurableSet]
  exact (eB.isCompact_preimage.2 hC).measure_lt_top

instance : (nu.map eB).IsHaarMeasure := { }

theorem lintegral_nu (G : Xc → ℝ≥0∞) (hG : Measurable G) :
    ∫⁻ p, G p ∂nu = ∫⁻ z, ∫⁻ a, ∫⁻ x, G (z, a, x) * ENNReal.ofReal (md a)⁻¹
      ∂adeleMeasure ℚ ∂ideleMeasure ℚ ∂ideleMeasure ℚ := by
  rw [nu, lintegral_prod _ hG.aemeasurable]
  refine lintegral_congr fun z => ?_
  have hGz : Measurable (fun q : Jd × 𝔸[ℚ] => G (z, q)) := hG.comp measurable_prodMk_left
  rw [lintegral_prod _ hGz.aemeasurable, wM,
    lintegral_withDensity_eq_lintegral_mul _ measurable_wD hGz.lintegral_prod_right']
  refine lintegral_congr fun a => ?_
  have hGa : Measurable (fun x : 𝔸[ℚ] => G (z, a, x)) := hGz.comp measurable_prodMk_left
  simp only [Pi.mul_apply]
  rw [← lintegral_const_mul _ hGa]
  exact lintegral_congr fun x => mul_comm _ _

theorem isClosed_bo : IsClosed ((adelicBorel : Subgroup G2) : Set G2) := by
  have h : ((adelicBorel : Subgroup G2) : Set G2) = {g : G2 | (g : Matrix (Fin 2) (Fin 2) 𝔸[ℚ]) 1 0 = 0} := by
    ext g
    constructor
    · intro hg
      exact (Reduction.mem_adelicBorel.1 hg) (by decide : (0 : Fin 2) < 1)
    · intro hg
      refine Reduction.mem_adelicBorel.2 ?_
      intro i j hij
      fin_cases i <;> fin_cases j <;> simp_all
  rw [h]
  exact isClosed_eq (cont_entry 1 0) continuous_const

instance : SecondCountableTopology Bo := TopologicalSpace.Subtype.secondCountableTopology _
instance : SecondCountableTopology KA := TopologicalSpace.Subtype.secondCountableTopology _

theorem meas_J (F : G2 → ℝ≥0∞) (hF : Measurable F) : Measurable (fun q : Xc × KA => F ((eB q.1).1 * q.2.1)) :=
  hF.comp (((continuous_subtype_val.comp (eB.continuous.comp continuous_fst)).mul
    (continuous_subtype_val.comp continuous_snd)).measurable)

theorem meas_S (mK : Measure KA) [SFinite mK] (F : G2 → ℝ≥0∞) (hF : Measurable F) :
    Measurable (fun s : Bo => ∫⁻ k : KA, F ((s : G2) * k) ∂mK) := by
  have : Measurable (fun q : Bo × KA => F ((q.1 : G2) * q.2.1)) :=
    hF.comp (((continuous_subtype_val.comp continuous_fst).mul
      (continuous_subtype_val.comp continuous_snd)).measurable)
  exact this.lintegral_prod_right'

theorem pt_eq (x : 𝔸[ℚ]) (a z : Jd) (κ : G2) : (eB (z, a, x)).1 * κ = pt x a z κ := rfl

theorem inner_map (mK : Measure KA) [SFinite mK] (F : G2 → ℝ≥0∞) (hF : Measurable F) :
    ∫⁻ s : Bo, ∫⁻ k : KA, F ((s : G2) * k) ∂mK ∂(nu.map eB) =
      ∫⁻ p : Xc, ∫⁻ k : KA, F ((eB p).1 * k.1) ∂mK ∂nu :=
  lintegral_map (meas_S mK F hF) eB.measurable

theorem inner_swap (mK : Measure KA) [SFinite mK] (F : G2 → ℝ≥0∞) (hF : Measurable F) :
    ∫⁻ p : Xc, ∫⁻ k : KA, F ((eB p).1 * k.1) ∂mK ∂nu = ∫⁻ k : KA, ∫⁻ p : Xc, F ((eB p).1 * k.1) ∂nu ∂mK :=
  lintegral_lintegral_swap (f := fun (p : Xc) (k : KA) => F ((eB p).1 * k.1)) (meas_J F hF).aemeasurable

theorem inner_nu (F : G2 → ℝ≥0∞) (hF : Measurable F) (κ : KA) :
    ∫⁻ p : Xc, F ((eB p).1 * κ.1) ∂nu = ∫⁻ z, ∫⁻ a, ∫⁻ x, F (pt x a z κ.1) * ENNReal.ofReal (md a)⁻¹
        ∂adeleMeasure ℚ ∂ideleMeasure ℚ ∂ideleMeasure ℚ := by
  have h : Measurable (fun p : Xc => F ((eB p).1 * κ.1)) :=
    hF.comp ((continuous_subtype_val.comp eB.continuous).mul continuous_const).measurable
  rw [lintegral_nu _ h]
  simp only [pt_eq]

theorem inner_eq (mK : Measure KA) [SFinite mK] (F : G2 → ℝ≥0∞) (hF : Measurable F) :
    ∫⁻ s : Bo, ∫⁻ k : KA, F ((s : G2) * k) ∂mK ∂(nu.map eB) =
      ∫⁻ κ, ∫⁻ z, ∫⁻ a, ∫⁻ x, F (pt x a z κ.1) * ENNReal.ofReal (md a)⁻¹
        ∂adeleMeasure ℚ ∂ideleMeasure ℚ ∂ideleMeasure ℚ ∂mK := by
  rw [inner_map mK F hF, inner_swap mK F hF]
  exact lintegral_congr fun κ => inner_nu F hF κ

theorem surj_mulMap : Function.Surjective (HaarSK.mulMap (adelicBorel : Subgroup G2) (maxCompact : Subgroup G2)) := by
  intro g
  obtain ⟨b, hb, k, hk, rfl⟩ := Reduction.exists_adelicBorel_mul_maxCompact g
  exact ⟨(⟨b, hb⟩, ⟨k, hk⟩), rfl⟩

theorem coord_of (μ : Measure G2) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] (mK : Measure KA) [mK.IsHaarMeasure]
    [IsProbabilityMeasure mK] : ∃ C, Coord μ mK C := by
  haveI : LocallyCompactSpace G2 := AdelicGLn.locallyCompactSpace ℚ 2
  obtain ⟨c, hc0, hc⟩ := HaarSK.exists_lintegral_eq μ isClosed_bo Reduction.isCompact_maxCompact surj_mulMap
    (nu.map eB) mK
  exact ⟨c, hc0, fun F hF => (hc F hF).trans (congrArg _ (inner_eq mK F hF))⟩

theorem coord_exists : Ad3.R.G2a := by
  intro μ 𝓕 mK 𝓓 h
  haveI := h.haar
  haveI := h.right
  haveI := h.haarK
  haveI := h.probK
  exact coord_of μ mK

end GlobalTheory.CompanionTheory.RSCoord
end
