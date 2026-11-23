import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.FrameMeasStatementPfB

namespace ReciprocityTheory.ChartRestriction.G.AR.Up.FM

open NumberField Matrix MeasureTheory Topology ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData
  ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Up.MI
open scoped ENNReal NNReal

noncomputable section

attribute [local instance] Classical.propDecidable

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)

def ufL : (Ix X.Ψ r → ℂ) ≃ₗ[ℂ] Frame X.Ψ r where
  toFun := uf X
  invFun x i := x i.1 i.2.1 i.2.2
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

def ufC : (Ix X.Ψ r → ℂ) ≃L[ℂ] Frame X.Ψ r := (ufL X).toContinuousLinearEquiv

theorem haarF : (volume : Measure (Frame X.Ψ r)).IsAddHaarMeasure := by
  haveI h1 : (volume : Measure (Fin r → ℂ)).IsAddHaarMeasure := by
    rw [volume_pi]
    exact Measure.pi.isAddHaarMeasure _
  haveI h2 : (volume : Measure (Fin r → Fin r → ℂ)).IsAddHaarMeasure := by
    rw [volume_pi]
    exact Measure.pi.isAddHaarMeasure _
  rw [volume_pi]
  exact Measure.pi.isAddHaarMeasure _

theorem haarIx : (volume : Measure (Ix X.Ψ r → ℂ)).IsAddHaarMeasure := by
  infer_instance

attribute [local instance] haarF haarIx

theorem lintegral_ufC (F : Frame X.Ψ r → ℝ≥0∞) :
    ∫⁻ v, F (ufC X v) = Measure.addHaarScalarFactor (volume.map (ufC X)) volume * ∫⁻ x, F x := by
  haveI : (volume.map (ufC X)).IsAddHaarMeasure := (ufC X).isAddHaarMeasure_map volume
  have e1 : ∫⁻ v, F (ufC X v) = ∫⁻ x, F x ∂(volume.map (ufC X)) :=
    (lintegral_map_equiv F (ufC X).toHomeomorph.toMeasurableEquiv).symm
  rw [e1]
  conv_lhs => rw [Measure.isAddLeftInvariant_eq_smul (volume.map (ufC X)) volume]
  rw [lintegral_smul_measure]
  rfl

theorem cont_ent (τ : X.Ψ) (a b : Fin r) : Continuous fun x : Frame X.Ψ r => x τ a b := by
  exact (continuous_apply b).comp ((continuous_apply a).comp (continuous_apply τ))

theorem continuous_UF : Continuous (UF X) := by
  apply continuous_pi
  intro τ
  apply continuous_pi
  intro a
  apply continuous_pi
  intro b
  simp only [UF, Umat, Matrix.of_apply]
  by_cases hh : b < a
  · simp only [hh, not_true_eq_false, dite_false]
    exact continuous_const
  · simp only [hh, not_false_eq_true, dite_true]
    fun_prop

theorem continuous_rmul : Continuous fun q : Frame X.Ψ r × Frame X.Ψ r => rmul q.1 q.2 := by
  apply continuous_pi
  intro τ
  apply continuous_pi
  intro a
  apply continuous_pi
  intro b
  simp only [rmul, mat, Matrix.mul_apply, Matrix.of_apply]
  apply continuous_finset_sum
  intro k _
  fun_prop

def fI (C : Set (Frame X.Ψ r)) (q : Frame X.Ψ r × (UpI X.Ψ r → ℂ)) : ℝ≥0∞ :=
  if ∀ τ b, q.2 (dI τ b) ≠ 0 then
    ENNReal.ofReal (Complex.normSq (jacU q.2)) * C.indicator (1 : Frame X.Ψ r → ℝ≥0∞) (rmul q.1 (UF X q.2)) else 0

theorem measurable_fI {C : Set (Frame X.Ψ r)} (hCm : MeasurableSet C) : Measurable (fI X C) := by
  have hJ : Continuous (fun y : UpI X.Ψ r → ℂ => jacU y) := by
    unfold jacU
    apply continuous_finset_prod
    intro i _
    split_ifs
    · exact continuous_apply _
    · exact continuous_const
  have hS : MeasurableSet {q : Frame X.Ψ r × (UpI X.Ψ r → ℂ) | ∀ τ b, q.2 (dI τ b) ≠ 0} := by
    simp only [Set.setOf_forall]
    refine MeasurableSet.iInter fun τ => MeasurableSet.iInter fun b => ?_
    have hc : Continuous fun q : Frame X.Ψ r × (UpI X.Ψ r → ℂ) => q.2 (dI τ b) :=
      (continuous_apply (dI τ b) : Continuous fun y : UpI X.Ψ r → ℂ => y (dI τ b)).comp continuous_snd
    exact (isOpen_ne_fun hc continuous_const).measurableSet
  have hf : Measurable (fun q : Frame X.Ψ r × (UpI X.Ψ r → ℂ) =>
      ENNReal.ofReal (Complex.normSq (jacU q.2))) :=
    ENNReal.measurable_ofReal.comp ((Complex.continuous_normSq.comp (hJ.comp continuous_snd)).measurable)
  have hg : Measurable (fun q : Frame X.Ψ r × (UpI X.Ψ r → ℂ) =>
      C.indicator (1 : Frame X.Ψ r → ℝ≥0∞) (rmul q.1 (UF X q.2))) :=
    (measurable_one.indicator hCm).comp
      ((continuous_rmul X).comp (continuous_fst.prodMk ((continuous_UF X).comp continuous_snd))).measurable
  unfold fI
  exact Measurable.ite hS (hf.mul hg) measurable_const

theorem measurable_Jp {C : Set (Frame X.Ψ r)} (hCm : MeasurableSet C) : Measurable (Jp X C) := by
  exact (measurable_fI X hCm).lintegral_prod_right'

theorem Jp_eq_zero {C : Set (Frame X.Ψ r)} {q : Frame X.Ψ r}
    (h : ∀ y : UpI X.Ψ r → ℂ, (∀ τ b, y (dI τ b) ≠ 0) → rmul q (UF X y) ∉ C) : Jp X C q = 0 := by
  unfold Jp
  have hz : ∀ y : UpI X.Ψ r → ℂ, (if ∀ τ b, y (dI τ b) ≠ 0 then
      ENNReal.ofReal (Complex.normSq (jacU y)) * C.indicator 1 (rmul q (UF X y)) else 0) = 0 := by
    intro y
    split_ifs with hy
    · simp [Set.indicator, h y hy]
    · rfl
  simp_rw [hz]
  exact lintegral_zero

theorem mem_sat {C : Set (Frame X.Ψ r)} (hCd : C ⊆ X.dom) {x0 : Frame X.Ψ r} {z : V (nd X)}
    {y : UpI X.Ψ r → ℂ} (hd : ∀ τ b, y (dI τ b) ≠ 0) (hxC : rmul (cpt X x0 z) (UF X y) ∈ C) :
    z ∈ sat X x0 C := by
  have hb := UF_mem X hd
  refine ⟨?_, rmul (cpt X x0 z) (UF X y), hxC, invF X (UF X y), invF_mem' X hb, (rmul_invF X hb).symm⟩
  show cpt X x0 z ∈ X.dom
  have := OrthogonalFrameDomain.rmul_mem_dom X (hCd hxC) (invF_mem' X hb)
  rwa [rmul_invF X hb] at this

theorem not_dom_rmul {C : Set (Frame X.Ψ r)} (hCd : C ⊆ X.dom) {p : Frame X.Ψ r} (hp : p ∉ X.dom)
    {y : UpI X.Ψ r → ℂ} (hd : ∀ τ b, y (dI τ b) ≠ 0) : rmul p (UF X y) ∉ C := fun h => by
  have hb := UF_mem X hd
  have := OrthogonalFrameDomain.rmul_mem_dom X (hCd h) (invF_mem' X hb)
  rw [rmul_invF X hb] at this
  exact hp this

theorem inner_le {x0 : Frame X.Ψ r} (hx0 : X.IsOrtho x0) {C : Set (Frame X.Ψ r)} (hCm : MeasurableSet C)
    (hCd : C ⊆ X.dom) {R0 : ℝ} (hR0 : ∀ x ∈ C, ∀ τ a b, ‖β0 X x τ a b‖ ≤ R0)
    {G : Frame X.Ψ r → ℝ≥0∞} (hGinv : ∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r, G (rmul x b) = G x)
    (x : LoI X.Ψ r → ℂ) :
    ∫⁻ y, (if ∀ τ b, y (dI τ b) ≠ 0 then ENNReal.ofReal (Complex.normSq (jacU y)) *
      C.indicator G (ufC X (LA (fun τ => mat x0 τ) (lu ((eS X.Ψ r).symm (x, y))))) else 0) ≤
      KR X R0 * GLo X x0 ({p | Jp X C p ≠ 0}.indicator G) x := by
  set p := rmul x0 (NF X x) with hpdef
  have hg : ∀ y, C.indicator G (ufC X (LA (fun τ => mat x0 τ) (lu ((eS X.Ψ r).symm (x, y))))) =
      C.indicator G (rmul p (UF X y)) := by
    intro y
    change C.indicator G (rmul x0 (uf X (lu ((eS X.Ψ r).symm (x, y))))) = _
    rw [uf_lu_eS, rmul_assoc']
  by_cases hp : p ∈ X.dom
  · have hmeas : Measurable fun y => fI X C (p, y) :=
      (measurable_fI X hCm).comp (measurable_const.prodMk measurable_id)
    calc _ = ∫⁻ y, G p * fI X C (p, y) := lintegral_congr fun y => by
            simp only [fI]
            split_ifs with hd
            · rw [hg y]
              by_cases hxC : rmul p (UF X y) ∈ C
              · rw [Set.indicator_of_mem hxC, Set.indicator_of_mem hxC, hGinv p hp _ (UF_mem X hd),
                  Pi.one_apply, mul_one, mul_comm]
              · simp [Set.indicator_of_notMem hxC]
            · rw [mul_zero]
      _ = G p * Jp X C p := lintegral_const_mul _ hmeas
      _ ≤ KR X R0 * GLo X x0 ({p | Jp X C p ≠ 0}.indicator G) x := by
          unfold GLo
          rw [if_pos hp]
          by_cases hJ : Jp X C p = 0
          · rw [hJ, mul_zero]; exact bot_le
          · rw [Set.indicator_of_mem (show p ∈ {p | Jp X C p ≠ 0} from hJ)]
            calc G p * Jp X C p ≤ G p * (ENNReal.ofReal (densY X p) * KR X R0) := by
                  gcongr; exact Jp_le X hCd hR0 hp (fun τ => norm_dmin_last X hx0 x τ)
              _ = KR X R0 * (G p * ENNReal.ofReal (densY X p)) := by ring
  · calc _ = ∫⁻ y, (0 : ℝ≥0∞) := lintegral_congr fun y => by
            split_ifs with hd
            · rw [hg y, Set.indicator_of_notMem (not_dom_rmul X hCd hp hd), mul_zero]
            · rfl
      _ = 0 := lintegral_zero
      _ ≤ _ := bot_le

end
end ReciprocityTheory.ChartRestriction.G.AR.Up.FM
