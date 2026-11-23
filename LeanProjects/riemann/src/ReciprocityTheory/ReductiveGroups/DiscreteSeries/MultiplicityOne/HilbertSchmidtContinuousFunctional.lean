import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.StCut1p
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.UnitaryGroupStructuralFacts

noncomputable section

open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal ComplexConjugate

namespace ReciprocityTheory.ChartRestriction.DS.Mult1.HilbertSchmidtFunctionals

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2 ReciprocityTheory.ChartRestriction.DS.Mult1

variable {k r : ℕ} {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]

theorem hilbertSchmidt_vec_add (A B : Wp →L[ℂ] Wp) : hsVec (A + B) = hsVec A + hsVec B := by
  ext i
  simp [hsVec]

theorem hilbertSchmidt_vec_smul (c : ℂ) (A : Wp →L[ℂ] Wp) : hsVec (c • A) = c • hsVec A := by
  ext i
  simp [hsVec]

def hilbertSchmidtFunctional (X₀ : Wp →L[ℂ] Wp) : (Wp →L[ℂ] Wp) →ₗ[ℂ] ℂ where
  toFun T := hsInner T X₀
  map_add' A B := by simp only [hsInner, hilbertSchmidt_vec_add, inner_add_right]
  map_smul' c A := by simp only [hsInner, hilbertSchmidt_vec_smul, inner_smul_right, RingHom.id_apply, smul_eq_mul]

def hilbertSchmidtContinuousFunctional (X₀ : Wp →L[ℂ] Wp) : (Wp →L[ℂ] Wp) →L[ℂ] ℂ := LinearMap.toContinuousLinearMap (hilbertSchmidtFunctional X₀)

theorem hilbertSchmidt_functional_apply (X₀ T : Wp →L[ℂ] Wp) : hilbertSchmidtContinuousFunctional X₀ T = hsInner T X₀ := by
  rfl

theorem hilbertSchmidt_inner_smul_left (c : ℂ) (A B : Wp →L[ℂ] Wp) : hsInner (c • A) B = c * hsInner A B := by
  simp only [hsInner, hilbertSchmidt_vec_smul, inner_smul_right]

section adj

variable [CompleteSpace Wp] {α β : Type*} [MeasurableSpace α] [MeasurableSpace β] {μ : Measure α} {ν : Measure β}

theorem integrable_adjoint {U : α → Wp →L[ℂ] Wp} (hU : Integrable U μ) :
    Integrable (fun a => ContinuousLinearMap.adjoint (U a)) μ := by
  refine hU.congr' (ContinuousLinearMap.adjoint.continuous.comp_aestronglyMeasurable hU.1) ?_
  exact Filter.Eventually.of_forall fun a => (ContinuousLinearMap.adjoint.norm_map (U a)).symm

theorem integral_adjoint_comm {U : α → Wp →L[ℂ] Wp} (hU : Integrable U μ) :
    ∫ a, ContinuousLinearMap.adjoint (U a) ∂μ = ContinuousLinearMap.adjoint (∫ a, U a ∂μ) := by
  exact ContinuousLinearMap.integral_comp_commSL RCLike.conj_smul
    (ContinuousLinearMap.adjoint : (Wp →L[ℂ] Wp) ≃ₗᵢ⋆[ℂ] (Wp →L[ℂ] Wp)).toContinuousLinearEquiv.toContinuousLinearMap hU

variable [SFinite μ] [SFinite ν]

theorem integrable_hilbertSchmidt_pairing (X₀ : Wp →L[ℂ] Wp) {U : α → Wp →L[ℂ] Wp} {V : β → Wp →L[ℂ] Wp}
    (hU : Integrable U μ) (hV : Integrable V ν) :
    Integrable (fun q : α × β => hilbertSchmidtContinuousFunctional X₀ ((ContinuousLinearMap.adjoint (U q.1)).comp (V q.2))) (μ.prod ν) := by
  have hG : Continuous fun x : (Wp →L[ℂ] Wp) × (Wp →L[ℂ] Wp) =>
      hilbertSchmidtContinuousFunctional X₀ ((ContinuousLinearMap.adjoint x.1).comp x.2) :=
    (hilbertSchmidtContinuousFunctional X₀).continuous.comp
      ((ContinuousLinearMap.adjoint.continuous.comp continuous_fst).clm_comp continuous_snd)
  have hm : AEStronglyMeasurable
      (fun q : α × β => hilbertSchmidtContinuousFunctional X₀ ((ContinuousLinearMap.adjoint (U q.1)).comp (V q.2))) (μ.prod ν) :=
    Continuous.comp_aestronglyMeasurable₂
      (g := fun A B : Wp →L[ℂ] Wp => hilbertSchmidtContinuousFunctional X₀ ((ContinuousLinearMap.adjoint A).comp B)) hG
      (hU.1.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_fst)
      (hV.1.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_snd)
  have hb : Integrable (fun q : α × β => ‖hilbertSchmidtContinuousFunctional X₀‖ * (‖U q.1‖ * ‖V q.2‖)) (μ.prod ν) :=
    (hU.norm.mul_prod hV.norm).const_mul _
  refine hb.mono' hm (Filter.Eventually.of_forall fun q => ?_)
  calc ‖hilbertSchmidtContinuousFunctional X₀ ((ContinuousLinearMap.adjoint (U q.1)).comp (V q.2))‖
      ≤ ‖hilbertSchmidtContinuousFunctional X₀‖ * ‖(ContinuousLinearMap.adjoint (U q.1)).comp (V q.2)‖ :=
        (hilbertSchmidtContinuousFunctional X₀).le_opNorm _
    _ ≤ ‖hilbertSchmidtContinuousFunctional X₀‖ * (‖U q.1‖ * ‖V q.2‖) := by
        gcongr
        calc ‖(ContinuousLinearMap.adjoint (U q.1)).comp (V q.2)‖
            ≤ ‖ContinuousLinearMap.adjoint (U q.1)‖ * ‖V q.2‖ := ContinuousLinearMap.opNorm_comp_le _ _
          _ = ‖U q.1‖ * ‖V q.2‖ := by rw [ContinuousLinearMap.adjoint.norm_map]

theorem integral_hilbertSchmidt_pairing (X₀ : Wp →L[ℂ] Wp) {U : α → Wp →L[ℂ] Wp} {V : β → Wp →L[ℂ] Wp}
    (hU : Integrable U μ) (hV : Integrable V ν) :
    ∫ q, hilbertSchmidtContinuousFunctional X₀ ((ContinuousLinearMap.adjoint (U q.1)).comp (V q.2)) ∂(μ.prod ν) =
      hilbertSchmidtContinuousFunctional X₀ ((ContinuousLinearMap.adjoint (∫ a, U a ∂μ)).comp (∫ b, V b ∂ν)) := by
  rw [integral_prod _ (integrable_hilbertSchmidt_pairing X₀ hU hV)]
  have hin : ∀ a, ∫ b, hilbertSchmidtContinuousFunctional X₀ ((ContinuousLinearMap.adjoint (U a)).comp (V b)) ∂ν =
      hilbertSchmidtContinuousFunctional X₀ ((ContinuousLinearMap.adjoint (U a)).comp (∫ b, V b ∂ν)) := fun a =>
    ((hilbertSchmidtContinuousFunctional X₀).comp (ContinuousLinearMap.compL ℂ Wp Wp Wp (ContinuousLinearMap.adjoint (U a)))).integral_comp_comm hV
  simp_rw [hin]
  have hout := ((hilbertSchmidtContinuousFunctional X₀).comp
    ((ContinuousLinearMap.compL ℂ Wp Wp Wp).flip (∫ b, V b ∂ν))).integral_comp_comm (integrable_adjoint hU)
  rw [integral_adjoint_comm hU] at hout
  exact hout

end adj

theorem sigmaFinite_of_haar_on {U : Set (Mat k r)} {μ : Measure (Mt k r)} (h : IsHaarOn U μ) : SigmaFinite μ := by
  have : IsFiniteMeasureOnCompacts μ := ⟨h.finite_compact⟩
  infer_instance

theorem ae_mem_big_cell (D : RealPlaceData k r Wp Wp) : ∀ᵐ p ∂D.μSS, D.inSS p := by
  have := sigmaFinite_of_haar_on D.haarW
  have := sigmaFinite_of_haar_on D.haarN
  have := sigmaFinite_of_haar_on D.haarW'
  have hW : ∀ᵐ x ∂D.μW, Matrix.of x ∈ UWset k r D.z := ae_iff.2 D.haarW.conc
  have hN : ∀ᵐ x ∂D.μN, Matrix.of x ∈ Nset k r := ae_iff.2 D.haarN.conc
  have hW' : ∀ᵐ x ∂D.μW', Matrix.of x ∈ UWset k r D.z' := ae_iff.2 D.haarW'.conc
  have h1 : ∀ᵐ p ∂D.μSS, Matrix.of p.1.1 ∈ UWset k r D.z :=
    Measure.quasiMeasurePreserving_fst.ae (Measure.quasiMeasurePreserving_fst.ae hW)
  have h2 : ∀ᵐ p ∂D.μSS, Matrix.of p.1.2 ∈ Nset k r :=
    Measure.quasiMeasurePreserving_fst.ae (Measure.quasiMeasurePreserving_snd.ae hN)
  have h3 : ∀ᵐ p ∂D.μSS, Matrix.of p.2.1 ∈ UWset k r D.z' :=
    Measure.quasiMeasurePreserving_snd.ae (Measure.quasiMeasurePreserving_fst.ae hW')
  have h4 : ∀ᵐ p ∂D.μSS, Matrix.of p.2.2 ∈ Nset k r :=
    Measure.quasiMeasurePreserving_snd.ae (Measure.quasiMeasurePreserving_snd.ae hN)
  filter_upwards [h1, h2, h3, h4] with p a b c d
  exact ⟨a, b, c, d⟩

theorem linear_form_continuous (z : Fin (2 * r + k + 1) → ℂ) : Continuous (ell k r z) := by
  unfold ell
  refine continuous_finsetSum _ fun a _ => ?_
  by_cases h : a.val + 1 < r
  · simp only [h, dite_true]
    exact continuous_id.matrix_elem _ _
  · simp only [h, dite_false]
    exact (continuous_apply (eI k r a)).comp (continuous_id.matrix_mulVec continuous_const)

theorem character_continuous (D : RealPlaceData k r Wp Wp) (τ : ℝ × ℝ) : Continuous (xiTau D τ) := by
  have hl : ∀ z : Fin (2 * r + k + 1) → ℂ, Continuous fun n : Mt k r => lam k r z (Matrix.of n) :=
    fun z => Complex.continuous_re.comp (continuous_const.mul ((linear_form_continuous z).comp continuous_id))
  unfold xiTau
  refine Complex.continuous_exp.comp (continuous_const.mul (Complex.continuous_ofReal.comp ?_))
  exact (continuous_const.mul ((hl D.z).comp (continuous_snd.comp continuous_fst))).sub
    (continuous_const.mul ((hl D.z').comp (continuous_snd.comp continuous_snd)))

theorem norm_character_eq_one (D : RealPlaceData k r Wp Wp) (τ : ℝ × ℝ) (p : SS k r) : ‖xiTau D τ p‖ = 1 := by
  unfold xiTau
  rw [mul_comm]
  exact Complex.norm_exp_ofReal_mul_I _

theorem star_character_mul_self (D : RealPlaceData k r Wp Wp) (τ : ℝ × ℝ) (p : SS k r) :
    star (xiTau D τ p) * xiTau D τ p = 1 := by
  rw [Complex.star_def, Complex.conj_mul', norm_character_eq_one]
  simp

theorem character_at_one_eq_product (D : RealPlaceData k r Wp Wp) (hz : D.z' = D.z) (p : SS k r) :
    xiTau D (1, 1) p = psiD D (Matrix.of p.1.2) * star (psiD D (Matrix.of p.2.2)) := by
  unfold xiTau psiD psi lam
  rw [hz, Complex.star_def, ← Complex.exp_conj, ← Complex.exp_add]
  congr 1
  push_cast
  simp only [map_mul, Complex.conj_I, Complex.conj_ofReal]
  ring

theorem adjoint_representation_inv [CompleteSpace Wp] (D : RealPlaceData k r Wp Wp) (hCW : IsClosedSubgroup (UWset k r D.z))
    {h : Mat k r} (hh : h ∈ UWset k r D.z) : ContinuousLinearMap.adjoint (D.π h⁻¹) = D.π h := by
  have hi : h⁻¹ ∈ UWset k r D.z := hCW.inv_mem h hh
  have h1 : (D.π h).comp (D.π h⁻¹) = 1 := by
    rw [← D.π_rep.2 h hh h⁻¹ hi, Matrix.mul_nonsing_inv _ (hCW.unit h hh), D.π_rep.1]
  have hA : (ContinuousLinearMap.adjoint (D.π h)).comp (D.π h) = 1 :=
    (ContinuousLinearMap.norm_map_iff_adjoint_comp_self (D.π h)).1 (D.π_unitary h hh)
  have hadj : ContinuousLinearMap.adjoint (D.π h) = D.π h⁻¹ := by
    calc ContinuousLinearMap.adjoint (D.π h)
        = (ContinuousLinearMap.adjoint (D.π h)).comp ((D.π h).comp (D.π h⁻¹)) := by
          rw [h1]; rfl
      _ = ((ContinuousLinearMap.adjoint (D.π h)).comp (D.π h)).comp (D.π h⁻¹) := by
          rw [ContinuousLinearMap.comp_assoc]
      _ = D.π h⁻¹ := by rw [hA]; rfl
  rw [← hadj, ContinuousLinearMap.adjoint_adjoint]

end ReciprocityTheory.ChartRestriction.DS.Mult1.HilbertSchmidtFunctionals
