import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.MatrixOfBesselTwoSidedAction
import Formalism.FormalDegreeBessel.FinalG
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselSubgroupsClosedUnitaryWCompactStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselOpNormPowerIntegralLtTopClosedSubgroupStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselModelUnitaryGroupOpNormPropertiesStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselConstantBoundsOfGeTwoNPowFiveStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselSubgroupRepTwistedIsUnitaryRepStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnimodularBesselSubgroupsUWNStatement

noncomputable section

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf
open scoped InnerProductSpace Topology

namespace GlobalTheory.SgInf.BeForm

variable {k r : ℕ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
variable {Wp : Type*} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp]

theorem isUnit_det_of_mem {g : Mat k r} (hg : g ∈ GG k r) : IsUnit g.det :=
  ((uHGroup _ (Hpk k r) (Matrix.isUnit_det_of_right_inverse (hpkFacts k r).2.1)).2.2 g hg).1

theorem mul_inv_of_mem {g : Mat k r} (hg : g ∈ GG k r) : g * g⁻¹ = 1 :=
  Matrix.mul_nonsing_inv g (GlobalTheory.SgInf.BeForm.isUnit_det_of_mem hg)

theorem continuousOn_inv : ContinuousOn (fun g : Mat k r => g⁻¹) (GG k r) := by
  intro g hg
  obtain ⟨w, hw⟩ := GlobalTheory.SgInf.BeForm.isUnit_det_of_mem hg
  refine (continuousAt_matrix_inv g ?_).continuousWithinAt
  rw [← hw]
  exact NormedRing.inverse_continuousAt w

theorem continuous_of : Continuous (fun x : Mt k r => (Matrix.of x : Mat k r)) := by
  exact continuous_id

theorem integrable_opn {μ : Measure (Mt k r)} {a : ℝ} (hint : normInt μ a < ⊤) :
    Integrable (fun x : Mt k r => opn (Matrix.of x : Mat k r) ^ (-a)) μ := by
  have hc : Continuous (fun x : Mt k r => opn (Matrix.of x : Mat k r)) :=
    (GlobalTheory.T.besselModelUnitaryGroup_opNorm_properties k r).2.2.1.comp GlobalTheory.SgInf.BeForm.continuous_of
  have hm : AEStronglyMeasurable (fun x : Mt k r => opn (Matrix.of x : Mat k r) ^ (-a)) μ :=
    (hc.measurable.pow_const (-a)).aestronglyMeasurable
  refine (lintegral_ofReal_ne_top_iff_integrable hm
    (Filter.Eventually.of_forall fun x => Real.rpow_nonneg ?_ _)).1 hint.ne
  exact norm_nonneg _

theorem integral_comp_self {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {μ : Measure (Mt k r)} {T : Mt k r → Mt k r} (hT : Measurable T) (hmap : μ.map T = μ)
    {f : Mt k r → E} (hf : AEStronglyMeasurable f μ) : ∫ x, f (T x) ∂μ = ∫ x, f x ∂μ := by
  have h := integral_map (μ := μ) (f := f) hT.aemeasurable (by rw [hmap]; exact hf)
  rw [hmap] at h
  exact h.symm

def bint (σ : Mat k r → (H →L[ℂ] H)) (P : Mat k r → (Wp →L[ℂ] Wp)) (u u' : H) (s : Mt k r) :
    Wp →L[ℂ] Wp :=
  coef σ u u' (Matrix.of s) • P (Matrix.of s)⁻¹

section Coef

variable {σ : Mat k r → (H →L[ℂ] H)} (hσ : IsURepOn (GG k r) σ)
include hσ

theorem inner_act {t : Mat k r} (ht : t ∈ GG k r) (x y : H) : ⟪σ t x, σ t y⟫_ℂ = ⟪x, y⟫_ℂ := by
  let f : H →ₗᵢ[ℂ] H := { toLinearMap := ((σ t : H →L[ℂ] H) : H →ₗ[ℂ] H), norm_map' := hσ.2.1 t ht }
  exact f.inner_map_map x y

theorem act_inv {t : Mat k r} (ht : t ∈ GG k r) (hti : t⁻¹ ∈ GG k r) (x : H) : σ t (σ t⁻¹ x) = x := by
  have h := hσ.1.2 t ht t⁻¹ hti
  rw [GlobalTheory.SgInf.BeForm.mul_inv_of_mem ht, hσ.1.1] at h
  have h2 := congrArg (fun A : H →L[ℂ] H => A x) h
  simpa using h2.symm

theorem coef_act_left {s t : Mat k r} (hs : s ∈ GG k r) (ht : t ∈ GG k r) (u v : H) :
    coef σ (σ t u) v s = coef σ u v (s * t) := by
  simp only [GlobalTheory.SgInf.coef, hσ.1.2 s hs t ht, ContinuousLinearMap.comp_apply]

theorem coef_act_right {s t : Mat k r} (hs : s ∈ GG k r) (ht : t ∈ GG k r) (hti : t⁻¹ ∈ GG k r)
    (hm : t⁻¹ * s ∈ GG k r) (u v : H) :
    coef σ u (σ t v) s = coef σ u v (t⁻¹ * s) := by
  simp only [GlobalTheory.SgInf.coef, hσ.1.2 t⁻¹ hti s hs, ContinuousLinearMap.comp_apply]
  have h := GlobalTheory.SgInf.BeForm.inner_act hσ ht v (σ t⁻¹ (σ s u))
  rw [GlobalTheory.SgInf.BeForm.act_inv hσ ht hti] at h
  exact h

theorem star_coef {s : Mat k r} (hs : s ∈ GG k r) (hsi : s⁻¹ ∈ GG k r) (u v : H) :
    star (coef σ u v s) = coef σ v u s⁻¹ := by
  simp only [GlobalTheory.SgInf.coef]
  have h := GlobalTheory.SgInf.BeForm.inner_act hσ hs u (σ s⁻¹ v)
  rw [GlobalTheory.SgInf.BeForm.act_inv hσ hs hsi] at h
  rw [← h]
  exact inner_conj_symm _ _

end Coef

section Main

variable {S : Set (Mat k r)} {σ : Mat k r → (H →L[ℂ] H)} {P : Mat k r → (Wp →L[ℂ] Wp)}
  {μ : Measure (Mt k r)} {a : ℝ}

theorem ae_mem (hμ : IsHaarOn S μ) : ∀ᵐ x ∂μ, (Matrix.of x : Mat k r) ∈ S :=
  ae_iff.2 hμ.2.2.1

theorem aesm_bint (hS : IsClosedSub k r S) (hσ : IsURepOn (GG k r) σ) (hPc : ContinuousOn P S)
    (hμ : IsHaarOn S μ) (u u' : H) : AEStronglyMeasurable (bint σ P u u') μ := by
  have hSm : MeasurableSet {x : Mt k r | (Matrix.of x : Mat k r) ∈ S} :=
    (hS.2.1.preimage GlobalTheory.SgInf.BeForm.continuous_of).measurableSet
  have h1 : ContinuousOn (fun x : Mt k r => σ (Matrix.of x : Mat k r) u)
      {x : Mt k r | (Matrix.of x : Mat k r) ∈ S} :=
    ((hσ.2.2 u).mono hS.1).comp GlobalTheory.SgInf.BeForm.continuous_of.continuousOn (fun x hx => hx)
  have h2 : ContinuousOn (fun x : Mt k r => P (Matrix.of x : Mat k r)⁻¹)
      {x : Mt k r | (Matrix.of x : Mat k r) ∈ S} :=
    hPc.comp ((GlobalTheory.SgInf.BeForm.continuousOn_inv.mono hS.1).comp
      GlobalTheory.SgInf.BeForm.continuous_of.continuousOn (fun x hx => hx)) (fun x hx => hS.2.2.2.2 _ hx)
  have hcont : ContinuousOn (bint σ P u u') {x : Mt k r | (Matrix.of x : Mat k r) ∈ S} := by
    show ContinuousOn (fun x : Mt k r => ⟪u', σ (Matrix.of x : Mat k r) u⟫_ℂ • P (Matrix.of x : Mat k r)⁻¹) _
    exact (ContinuousOn.inner (𝕜 := ℂ) continuousOn_const h1).smul h2
  have h3 := hcont.aestronglyMeasurable (μ := μ) hSm
  rwa [Measure.restrict_eq_self_of_ae_mem (s := {x : Mt k r | (Matrix.of x : Mat k r) ∈ S}) (GlobalTheory.SgInf.BeForm.ae_mem hμ)] at h3

theorem integrable_bint (hS : IsClosedSub k r S) (hσ : IsURepOn (GG k r) σ) (hPc : ContinuousOn P S)
    (hPb : ∀ s ∈ S, ‖P s‖ ≤ 1) (hμ : IsHaarOn S μ) (hint : normInt μ a < ⊤) {u u' : H} {C : ℝ}
    (hC : ∀ g ∈ GG k r, ‖coef σ u u' g‖ ≤ C * opn g ^ (-a)) : Integrable (bint σ P u u') μ := by
  refine Integrable.mono' ((GlobalTheory.SgInf.BeForm.integrable_opn hint).const_mul C)
    (GlobalTheory.SgInf.BeForm.aesm_bint hS hσ hPc hμ u u') ?_
  filter_upwards [GlobalTheory.SgInf.BeForm.ae_mem hμ] with x hx
  have hP := hPb _ (hS.2.2.2.2 _ hx)
  have hc := hC _ (hS.1 hx)
  calc ‖bint σ P u u' x‖ = ‖coef σ u u' (Matrix.of x)‖ * ‖P (Matrix.of x : Mat k r)⁻¹‖ := by
        rw [bint, norm_smul]
    _ ≤ ‖coef σ u u' (Matrix.of x)‖ * 1 := by gcongr
    _ ≤ C * opn (Matrix.of x : Mat k r) ^ (-a) := by rw [mul_one]; exact hc

theorem be_left (hS : IsClosedSub k r S) (hσ : IsURepOn (GG k r) σ) (hP : IsURepOn S P)
    (hμ : IsHaarOn S μ) (hU : IsUnimod S μ) {u u' : H} (hI : Integrable (bint σ P u u') μ)
    {t : Mat k r} (ht : t ∈ S) :
    ∫ s, bint σ P (σ t u) u' s ∂μ = (P t).comp (∫ s, bint σ P u u' s ∂μ) := by
  have htG : t ∈ GG k r := hS.1 ht
  have hL := ContinuousLinearMap.integral_comp_comm (ContinuousLinearMap.compL ℂ Wp Wp Wp (P t)) hI
  simp only [ContinuousLinearMap.compL_apply] at hL
  rw [← hL]
  have hm : AEStronglyMeasurable (fun s => (P t).comp (bint σ P u u' s)) μ :=
    (ContinuousLinearMap.compL ℂ Wp Wp Wp (P t)).continuous.comp_aestronglyMeasurable hI.1
  rw [← GlobalTheory.SgInf.BeForm.integral_comp_self (continuous_rmulM t).measurable (hU.1 t ht) hm]
  refine integral_congr_ae ?_
  filter_upwards [GlobalTheory.SgInf.BeForm.ae_mem hμ] with s hs
  have hsG : (Matrix.of s : Mat k r) ∈ GG k r := hS.1 hs
  have hti : t⁻¹ ∈ S := hS.2.2.2.2 _ ht
  have hsi : (Matrix.of s : Mat k r)⁻¹ ∈ S := hS.2.2.2.2 _ hs
  have hmem : t⁻¹ * (Matrix.of s : Mat k r)⁻¹ ∈ S := hS.2.2.2.1 _ hti _ hsi
  have hof : (Matrix.of (rmulM t s) : Mat k r) = Matrix.of s * t := rfl
  simp only [bint, hof, ContinuousLinearMap.comp_smul]
  rw [GlobalTheory.SgInf.BeForm.coef_act_left hσ hsG htG, Matrix.mul_inv_rev, ← hP.1.2 t ht _ hmem,
    ← mul_assoc, GlobalTheory.SgInf.BeForm.mul_inv_of_mem htG, one_mul]

theorem be_right (hS : IsClosedSub k r S) (hσ : IsURepOn (GG k r) σ) (hP : IsURepOn S P)
    (hμ : IsHaarOn S μ) {u u' : H} (hI : Integrable (bint σ P u u') μ)
    {t : Mat k r} (ht : t ∈ S) :
    ∫ s, bint σ P u (σ t u') s ∂μ = (∫ s, bint σ P u u' s ∂μ).comp (P t⁻¹) := by
  have htG : t ∈ GG k r := hS.1 ht
  have hti : t⁻¹ ∈ S := hS.2.2.2.2 _ ht
  have htiG : t⁻¹ ∈ GG k r := hS.1 hti
  have hL := ContinuousLinearMap.integral_comp_comm
    ((ContinuousLinearMap.compL ℂ Wp Wp Wp).flip (P t⁻¹)) hI
  simp only [ContinuousLinearMap.flip_apply, ContinuousLinearMap.compL_apply] at hL
  rw [← hL]
  have hm : AEStronglyMeasurable (fun s => (bint σ P u u' s).comp (P t⁻¹)) μ :=
    ((ContinuousLinearMap.compL ℂ Wp Wp Wp).flip (P t⁻¹)).continuous.comp_aestronglyMeasurable hI.1
  have hTc : Continuous (lmulM t⁻¹ : Mt k r → Mt k r) := by
    show Continuous (fun x : Mt k r => (t⁻¹ * Matrix.of x : Mat k r))
    exact continuous_const.matrix_mul GlobalTheory.SgInf.BeForm.continuous_of
  rw [← GlobalTheory.SgInf.BeForm.integral_comp_self hTc.measurable (hμ.2.2.2 _ hti) hm]
  refine integral_congr_ae ?_
  filter_upwards [GlobalTheory.SgInf.BeForm.ae_mem hμ] with s hs
  have hsG : (Matrix.of s : Mat k r) ∈ GG k r := hS.1 hs
  have hm1 : t⁻¹ * (Matrix.of s : Mat k r) ∈ S := hS.2.2.2.1 _ hti _ hs
  have hm2 : (t⁻¹ * (Matrix.of s : Mat k r))⁻¹ ∈ S := hS.2.2.2.2 _ hm1
  have hof : (Matrix.of (lmulM t⁻¹ s) : Mat k r) = t⁻¹ * Matrix.of s := rfl
  simp only [bint, hof, ContinuousLinearMap.smul_comp]
  rw [GlobalTheory.SgInf.BeForm.coef_act_right hσ hsG htG htiG (hS.1 hm1)]
  congr 1
  rw [← hP.1.2 _ hm2 _ hti, ← Matrix.mul_inv_rev, ← mul_assoc, GlobalTheory.SgInf.BeForm.mul_inv_of_mem htG,
    one_mul]

def adjR (Wp : Type*) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] :
    (Wp →L[ℂ] Wp) →L[ℝ] (Wp →L[ℂ] Wp) :=
  LinearMap.mkContinuous
    { toFun := fun A => ContinuousLinearMap.adjoint A
      map_add' := fun A B => map_add _ A B
      map_smul' := fun c A => by
        have : (c • A : Wp →L[ℂ] Wp) = (c : ℂ) • A := by ext x; simp
        rw [this, map_smulₛₗ]
        ext x
        simp } 1
    (fun A => by simp)

theorem be_adjoint (hS : IsClosedSub k r S) (hσ : IsURepOn (GG k r) σ)
    (hPa : ∀ s ∈ S, ContinuousLinearMap.adjoint (P s) = P s⁻¹)
    (hμ : IsHaarOn S μ) (hU : IsUnimod S μ) {u u' : H} (hI : Integrable (bint σ P u u') μ)
    (hI' : Integrable (bint σ P u' u) μ) :
    ContinuousLinearMap.adjoint (∫ s, bint σ P u u' s ∂μ) = ∫ s, bint σ P u' u s ∂μ := by
  have h1 := ContinuousLinearMap.integral_comp_comm (adjR Wp) hI
  change adjR Wp (∫ s, bint σ P u u' s ∂μ) = _
  rw [← h1, ← GlobalTheory.SgInf.BeForm.integral_comp_self measurable_invM hU.2 hI'.1]
  refine integral_congr_ae ?_
  filter_upwards [GlobalTheory.SgInf.BeForm.ae_mem hμ] with s hs
  have hsG : (Matrix.of s : Mat k r) ∈ GG k r := hS.1 hs
  have hsi : (Matrix.of s : Mat k r)⁻¹ ∈ S := hS.2.2.2.2 _ hs
  have hsiG : (Matrix.of s : Mat k r)⁻¹ ∈ GG k r := hS.1 hsi
  have hof : (Matrix.of (invM s) : Mat k r) = (Matrix.of s : Mat k r)⁻¹ := rfl
  change ContinuousLinearMap.adjoint (bint σ P u u' s) = _
  simp only [bint, hof, map_smulₛₗ, hPa _ hsi]
  congr 1
  exact GlobalTheory.SgInf.BeForm.star_coef hσ hsG hsiG u u'

theorem be_continuousOn (hS : IsClosedSub k r S) (hσ : IsURepOn (GG k r) σ) (hPc : ContinuousOn P S)
    (hPb : ∀ s ∈ S, ‖P s‖ ≤ 1) (hμ : IsHaarOn S μ) (hint : normInt μ a < ⊤) (ha : 0 < a)
    {u u' : H} {C : ℝ} (hC : ∀ g ∈ GG k r, ‖coef σ u u' g‖ ≤ C * opn g ^ (-a)) :
    ContinuousOn (fun x => ∫ s, bint σ P (σ x u) u' s ∂μ) (GG k r) := by
  have hop := GlobalTheory.T.besselModelUnitaryGroup_opNorm_properties k r
  have hdet : IsUnit (Hpk k r).det := Matrix.isUnit_det_of_right_inverse (hpkFacts k r).2.1
  have : FirstCountableTopology (Mat k r) := inferInstanceAs (FirstCountableTopology (Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → ℂ))
  intro x0 hx0
  have hev : ∀ᶠ x in 𝓝[GG k r] x0, x ∈ GG k r ∧ opn x ≤ opn x0 + 1 := by
    have h1 : ∀ᶠ x in 𝓝 x0, opn x < opn x0 + 1 :=
      hop.2.2.1.continuousAt.eventually_lt continuousAt_const (lt_add_one _)
    filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds h1] with x hx hx'
    exact ⟨hx, hx'.le⟩
  refine continuousWithinAt_of_dominated
    (bound := fun s : Mt k r => |C| * (opn x0 + 1) ^ a * opn (Matrix.of s : Mat k r) ^ (-a)) ?_ ?_ ?_ ?_
  · filter_upwards [hev] with x hx
    exact GlobalTheory.SgInf.BeForm.aesm_bint hS hσ hPc hμ (σ x u) u'
  · filter_upwards [hev] with x hx
    filter_upwards [GlobalTheory.SgInf.BeForm.ae_mem hμ] with s hs
    have hsG : (Matrix.of s : Mat k r) ∈ GG k r := hS.1 hs
    have hsi : (Matrix.of s : Mat k r)⁻¹ ∈ S := hS.2.2.2.2 _ hs
    have hxG : x ∈ GG k r := hx.1
    have hsxG : (Matrix.of s : Mat k r) * x ∈ GG k r := (uHGroup _ (Hpk k r) hdet).2.1 _ hsG _ hxG
    have hp : 1 ≤ opn (Matrix.of s : Mat k r) := (hop.1 _ hsG).2
    have hq : 1 ≤ opn x := (hop.1 _ hxG).2
    have hw1 : 1 ≤ opn ((Matrix.of s : Mat k r) * x) := (hop.1 _ hsxG).2
    have hw : opn (Matrix.of s : Mat k r) / opn x ≤ opn ((Matrix.of s : Mat k r) * x) :=
      (hop.2.2.2.2.2.2.1 _ hsG _ hxG).1
    have hpq : 0 < opn (Matrix.of s : Mat k r) / opn x := div_pos (by linarith) (by linarith)
    have key : opn ((Matrix.of s : Mat k r) * x) ^ (-a) ≤
        (opn x0 + 1) ^ a * opn (Matrix.of s : Mat k r) ^ (-a) := by
      calc opn ((Matrix.of s : Mat k r) * x) ^ (-a) ≤ (opn (Matrix.of s : Mat k r) / opn x) ^ (-a) :=
            Real.rpow_le_rpow_of_nonpos hpq hw (by linarith)
        _ = opn x ^ a * opn (Matrix.of s : Mat k r) ^ (-a) := by
            rw [Real.div_rpow (by linarith) (by linarith), Real.rpow_neg (by linarith : (0:ℝ) ≤ opn x),
              div_inv_eq_mul, mul_comm]
        _ ≤ (opn x0 + 1) ^ a * opn (Matrix.of s : Mat k r) ^ (-a) :=
            mul_le_mul_of_nonneg_right (Real.rpow_le_rpow (by linarith) hx.2 ha.le)
              (Real.rpow_nonneg (by linarith) _)
    have hc := hC _ hsxG
    have hPn := hPb _ hsi
    have hwpos : 0 ≤ opn ((Matrix.of s : Mat k r) * x) ^ (-a) := Real.rpow_nonneg (by linarith) _
    calc ‖bint σ P (σ x u) u' s‖
        = ‖coef σ (σ x u) u' (Matrix.of s)‖ * ‖P (Matrix.of s : Mat k r)⁻¹‖ := by rw [bint, norm_smul]
      _ ≤ ‖coef σ (σ x u) u' (Matrix.of s)‖ * 1 := by gcongr
      _ = ‖coef σ u u' ((Matrix.of s : Mat k r) * x)‖ := by
          rw [mul_one, GlobalTheory.SgInf.BeForm.coef_act_left hσ hsG hxG]
      _ ≤ C * opn ((Matrix.of s : Mat k r) * x) ^ (-a) := hc
      _ ≤ |C| * opn ((Matrix.of s : Mat k r) * x) ^ (-a) :=
          mul_le_mul_of_nonneg_right (le_abs_self C) hwpos
      _ ≤ |C| * ((opn x0 + 1) ^ a * opn (Matrix.of s : Mat k r) ^ (-a)) :=
          mul_le_mul_of_nonneg_left key (abs_nonneg C)
      _ = |C| * (opn x0 + 1) ^ a * opn (Matrix.of s : Mat k r) ^ (-a) := by ring
  · exact (GlobalTheory.SgInf.BeForm.integrable_opn hint).const_mul _
  · refine Filter.Eventually.of_forall (fun s => ?_)
    show ContinuousWithinAt
      (fun x => ⟪u', σ (Matrix.of s : Mat k r) (σ x u)⟫_ℂ • P (Matrix.of s : Mat k r)⁻¹) (GG k r) x0
    exact (ContinuousWithinAt.inner (𝕜 := ℂ) continuousWithinAt_const
      ((σ (Matrix.of s : Mat k r)).continuous.continuousAt.comp_continuousWithinAt ((hσ.2.2 u) x0 hx0))).smul
      continuousWithinAt_const

end Main

theorem be_converges_equivariant_hermitian_continuous : ∀ (k r : ℕ) {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp] [CompleteSpace Wp] (σ : Mat k r → (H →L[ℂ] H)) (w : H) (a : ℝ) (μG : Measure (Mt k r)) (d : ℝ) (z : Fin (2 * r + k + 1) → ℂ) (c : Fin r → ℂ) (π : Mat k r → (Wp →L[ℂ] Wp)) (μS : Measure (Mt k r)) , Std σ w a μG d → Side z π μS → ∀ V : Set H, (∀ g ∈ GG k r, ∀ v ∈ V, σ g v ∈ V) → Decay σ V a → ∀ u ∈ V, ∀ u' ∈ V, Integrable (fun s : Mt k r => coef σ u u' (Matrix.of s) • PiS (psiGen k r z c) π (Matrix.of s)⁻¹) μS ∧ (∀ t ∈ Sset k r z, be (psiGen k r z c) π μS σ (σ t u) u' = (PiS (psiGen k r z c) π t).comp (be (psiGen k r z c) π μS σ u u') ∧ be (psiGen k r z c) π μS σ u (σ t u') = (be (psiGen k r z c) π μS σ u u').comp (PiS (psiGen k r z c) π t⁻¹)) ∧ ContinuousLinearMap.adjoint (be (psiGen k r z c) π μS σ u u') = be (psiGen k r z c) π μS σ u' u ∧ ContinuousOn (fun x => be (psiGen k r z c) π μS σ (σ x u) u') (GG k r) := by
  intro k r H _ _ _ Wp _ _ _ _ σ w a μG d z c π μS hStd hSide V hV hDec u hu u' hu'
  obtain ⟨hk, hσ, -, -, -, -, ha5, -, -⟩ := hStd
  obtain ⟨hz, hT, hπ, hHaar, -⟩ := hSide
  have hS : IsClosedSub k r (Sset k r z) := (GlobalTheory.T.bessel_subgroups_closed_unitaryW_compact k r z hz hT).2.2.2.1
  have h47 := GlobalTheory.T.besselSubgroupRepTwisted_isUnitaryRep k r z c π hz hT hπ
  have hU : IsUnimod (Sset k r z) μS := (GlobalTheory.T.unimodular_besselSubgroups_UW_N k r z hz hT μS).1 hHaar
  have hb := GlobalTheory.T.bessel_constant_bounds_of_ge_two_n_pow_five k r a hk ha5
  have hn : (0:ℝ) ≤ 2 * ((2 * r + k + 1 : ℕ) : ℝ) ^ 2 := by positivity
  have hapos : 0 < a := by linarith [hb.1]
  have hint : normInt μS a < ⊤ := GlobalTheory.T.besselOpNormPowerIntegral_lt_top_closedSubgroup k r _ μS a hS hHaar (by linarith [hb.1])
  obtain ⟨C, hC⟩ := hDec u hu u' hu'
  obtain ⟨C', hC'⟩ := hDec u' hu' u hu
  have hPc := h47.2.2.2.1
  have hPb : ∀ s ∈ Sset k r z, ‖PiS (psiGen k r z c) π s‖ ≤ 1 := fun s hs => (h47.2.2.1 s hs).1
  have hPa : ∀ s ∈ Sset k r z, ContinuousLinearMap.adjoint (PiS (psiGen k r z c) π s) =
      PiS (psiGen k r z c) π s⁻¹ := fun s hs => (h47.2.2.1 s hs).2
  have hI := GlobalTheory.SgInf.BeForm.integrable_bint hS hσ hPc hPb hHaar hint hC
  have hI' := GlobalTheory.SgInf.BeForm.integrable_bint hS hσ hPc hPb hHaar hint hC'
  refine ⟨hI, fun t ht => ⟨?_, ?_⟩, ?_, ?_⟩
  · exact GlobalTheory.SgInf.BeForm.be_left hS hσ h47.2.1 hHaar hU hI ht
  · exact GlobalTheory.SgInf.BeForm.be_right hS hσ h47.2.1 hHaar hI ht
  · exact GlobalTheory.SgInf.BeForm.be_adjoint hS hσ hPa hHaar hU hI hI'
  · exact GlobalTheory.SgInf.BeForm.be_continuousOn hS hσ hPc hPb hHaar hint hapos hC

end GlobalTheory.SgInf.BeForm
