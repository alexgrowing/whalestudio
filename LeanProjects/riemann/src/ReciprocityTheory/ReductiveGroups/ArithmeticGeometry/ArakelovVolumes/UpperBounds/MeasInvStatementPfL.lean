import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.MeasInvStatementPfK

namespace ReciprocityTheory.ChartRestriction.G.AR.Up.MI

open NumberField Matrix MeasureTheory ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates
  ReciprocityTheory.ChartRestriction.G.AR.Up

noncomputable section

attribute [local instance] Classical.propDecidable

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)

def eLE : LoI X.Ψ r ≃ Ent X where
  toFun i := ⟨i.1.1, ⟨(i.1.2.1, i.1.2.2), i.2⟩⟩
  invFun e := ⟨(e.1, e.2.1.1, e.2.1.2), e.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

def eL : LoI X.Ψ r ≃ Fin (nd X) := (eLE X).trans (Fintype.equivFin (Ent X))

def ΦL : V (nd X) ≃ₗ[ℂ] (LoI X.Ψ r → ℂ) :=
  (WithLp.linearEquiv 2 ℂ (Fin (nd X) → ℂ)).trans (LinearEquiv.funCongrLeft ℂ ℂ (eL X))

lemma NF_ΦL (z : V (nd X)) : NF X (ΦL X z) = nmat X z := by
  funext τ a b
  simp only [NF, Nmat, nmat, Matrix.of_apply]
  split_ifs <;> rfl

def muX (x0 : Frame X.Ψ r) : Measure (V (nd X)) :=
  (volume.restrict {z | cpt X x0 z ∈ X.dom}).withDensity fun z => ENNReal.ofReal (densY X (cpt X x0 z))

def ΦC : V (nd X) ≃L[ℂ] (LoI X.Ψ r → ℂ) := (ΦL X).toContinuousLinearEquiv

lemma lintegral_ΦC (F : (LoI X.Ψ r → ℂ) → ENNReal) :
    ∫⁻ z, F (ΦC X z) = Measure.addHaarScalarFactor (volume.map (ΦC X)) volume * ∫⁻ x, F x := by
  have h1 : (∫⁻ z, F (ΦC X z)) = ∫⁻ x, F x ∂(volume.map (ΦC X)) :=
    (lintegral_map_equiv F (ΦC X).toHomeomorph.toMeasurableEquiv).symm
  calc (∫⁻ z, F (ΦC X z)) = ∫⁻ x, F x ∂(volume.map (ΦC X)) := h1
    _ = ∫⁻ x, F x ∂(Measure.addHaarScalarFactor (volume.map (ΦC X)) volume • volume) := by
        rw [← Measure.isAddLeftInvariant_eq_smul]
    _ = _ := lintegral_smul_measure _ _

lemma continuous_dmin (τ : X.Ψ) (i : Fin (r + 1)) : Continuous fun y : Frame X.Ψ r => dmin X.Gm y τ i := by
  unfold dmin lminor
  apply Continuous.matrix_det
  refine continuous_pi fun a => continuous_pi fun b => ?_
  simp only [Matrix.submatrix_apply, ReciprocityTheory.ChartRestriction.G.FD.gram, Matrix.of_apply, ReciprocityTheory.ChartRestriction.G.FD.hermC,
    ReciprocityTheory.ChartRestriction.G.FD.col, ReciprocityTheory.ChartRestriction.G.FD.mat]
  fun_prop

lemma measurable_densY : Measurable (densY X) := by
  have h : densY X = fun y => (∏ τ, ∏ i : Fin r, ‖dmin X.Gm y τ i.castSucc‖ ^ 2)⁻¹ :=
    funext fun y => densY_eq X
  rw [h]
  refine Measurable.inv ?_
  refine Finset.measurable_prod _ fun τ _ => Finset.measurable_prod _ fun i _ => ?_
  exact ((continuous_dmin X τ _).measurable.norm).pow_const 2

lemma continuous_NF : Continuous (NF X) := by
  refine continuous_pi fun τ => continuous_pi fun a => continuous_pi fun b => ?_
  by_cases h : b < a
  · have e : (fun x : LoI X.Ψ r → ℂ => NF X x τ a b) = fun x => x ⟨(τ, a, b), h⟩ := by
      funext x
      simp [NF, Nmat, h]
    rw [e]
    exact continuous_apply _
  · have e : (fun x : LoI X.Ψ r → ℂ => NF X x τ a b) = fun _ => if a = b then 1 else 0 := by
      funext x
      simp [NF, Nmat, h]
    rw [e]
    exact continuous_const

lemma cpt_eq (x0 : Frame X.Ψ r) (z : V (nd X)) : cpt X x0 z = rmul x0 (NF X (ΦC X z)) := by
  show rmul x0 (nmat X z) = rmul x0 (NF X (ΦC X z))
  rw [← NF_ΦL]
  rfl

lemma continuous_cpt (x0 : Frame X.Ψ r) : Continuous (cpt X x0) := by
  rw [show cpt X x0 = fun z => rmul x0 (NF X (ΦC X z)) from funext (cpt_eq X x0)]
  refine continuous_pi fun τ => ?_
  show Continuous fun z => mat x0 τ * mat (NF X (ΦC X z)) τ
  exact continuous_const.matrix_mul (((continuous_apply τ).comp (continuous_NF X)).comp (ΦC X).continuous)

theorem lintegral_muX {x0 : Frame X.Ψ r} {φ : Frame X.Ψ r → ENNReal} (hφm : Measurable φ) :
    ∫⁻ z, φ (cpt X x0 z) ∂muX X x0 =
      Measure.addHaarScalarFactor (volume.map (ΦC X)) volume * ∫⁻ x, GLo X x0 φ x := by
  have hdom : MeasurableSet X.dom := by
    have ho : IsOpen X.dom := by
      show IsOpen {x : Frame X.Ψ r | ∀ τ : X.Ψ, (mat x τ).det ≠ 0 ∧
        ∀ i : Fin (r + 1), 0 < psgn X.p0 i * (dmin X.Gm x τ i).re}
      simp only [Set.setOf_forall, Set.setOf_and]
      refine isOpen_iInter_of_finite fun τ => IsOpen.inter ?_ (isOpen_iInter_of_finite fun i => ?_)
      · exact isOpen_ne_fun (continuous_apply τ).matrix_det continuous_const
      · exact isOpen_lt continuous_const
          (continuous_const.mul (Complex.continuous_re.comp (continuous_dmin X τ i)))
    exact ho.measurableSet
  have hS : MeasurableSet {z : V (nd X) | cpt X x0 z ∈ X.dom} :=
    hdom.preimage (continuous_cpt X x0).measurable
  have hdens : Measurable fun z => ENNReal.ofReal (densY X (cpt X x0 z)) :=
    ENNReal.measurable_ofReal.comp ((measurable_densY X).comp (continuous_cpt X x0).measurable)
  unfold muX
  rw [lintegral_withDensity_eq_lintegral_mul _ hdens
      (show Measurable fun z => φ (cpt X x0 z) from hφm.comp (continuous_cpt X x0).measurable),
    ← lintegral_indicator hS, ← lintegral_ΦC]
  congr 1
  funext z
  simp only [GLo, Set.indicator, Set.mem_setOf_eq, Pi.mul_apply, Function.comp_apply, ← cpt_eq]
  split_ifs <;> simp [mul_comm]

theorem lintegral_cpt_muX_indep_of_isOrtho {x0 x0' : Frame X.Ψ r} (hx0 : X.IsOrtho x0) (hx0' : X.IsOrtho x0') {φ : Frame X.Ψ r → ENNReal}
    (hφm : Measurable φ) (hφ : ∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r, φ (rmul x b) = φ x) :
    ∫⁻ z, φ (cpt X x0 z) ∂muX X x0 = ∫⁻ z, φ (cpt X x0' z) ∂muX X x0' := by
  rw [lintegral_muX X hφm, lintegral_muX X hφm]
  congr 1
  have h1 := core X hx0 hφm hφ
  have h2 := core X hx0' hφm hφ
  have hK0 : K0 X.Ψ r ≠ 0 := (finrank_maxUnramifiedSubfield_padicFinExt_pos (ι := X.Ψ) (r := r)).ne'
  have hK0' : K0 X.Ψ r ≠ ⊤ := (measureConstant_lt_top (ι := X.Ψ) (r := r)).ne
  exact (ENNReal.mul_left_inj hK0 hK0').mp (h1.trans h2.symm)

end

end ReciprocityTheory.ChartRestriction.G.AR.Up.MI
