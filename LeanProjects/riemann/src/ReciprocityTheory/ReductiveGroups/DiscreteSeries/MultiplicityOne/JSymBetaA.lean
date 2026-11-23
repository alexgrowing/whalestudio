import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.StDefs
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.UnitaryGroupStructuralFacts

noncomputable section

open MeasureTheory Matrix Filter Topology
open scoped ENNReal

namespace ReciprocityTheory.ChartRestriction.DS.Mult1.SymBetaA

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ}

theorem deriv_smul_const_any {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (h : ℝ → ℂ) (T : E) :
    deriv (fun t => h t • T) 0 = deriv h 0 • T := by
  by_cases hT : T = 0
  · subst hT
    simp
  by_cases hd : DifferentiableAt ℝ h 0
  · exact deriv_smul_const hd T
  · have hnd : ¬ DifferentiableAt ℝ (fun t => h t • T) 0 := by
      intro hd'
      apply hd
      obtain ⟨φ, -, hφ⟩ := exists_dual_vector ℂ T (norm_ne_zero_iff.mpr hT)
      have hφT : φ T ≠ 0 := by
        rw [hφ]
        exact Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hT)
      have he : h = fun t => (φ T)⁻¹ * φ (h t • T) := by
        funext t
        rw [map_smul, smul_eq_mul]
        field_simp
      rw [he]
      exact DifferentiableAt.const_mul ((φ.restrictScalars ℝ).differentiableAt.comp (0 : ℝ) hd') _
    rw [deriv_zero_of_not_differentiableAt hnd, deriv_zero_of_not_differentiableAt hd, zero_smul]

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem LdV_smul (X : Mat k r) (φ : Mat k r → ℂ) (T : E) :
    LdV X (fun g => φ g • T) = fun g => LdV X φ g • T := by
  funext g
  exact deriv_smul_const_any _ T

theorem RdV_smul (X : Mat k r) (φ : Mat k r → ℂ) (T : E) :
    RdV X (fun g => φ g • T) = fun g => RdV X φ g • T := by
  funext g
  exact deriv_smul_const_any _ T

theorem Rw_smul (v : List (Mat k r)) (φ : Mat k r → ℂ) (T : E) :
    Rw v (fun g => φ g • T) = fun g => Rw v φ g • T := by
  induction v with
  | nil => rfl
  | cons X v ih =>
    show RdV X (Rw v (fun g => φ g • T)) = fun g => RdV X (Rw v φ) g • T
    rw [ih]
    exact RdV_smul X (Rw v φ) T

theorem dLR_smul (u v : List (Mat k r)) (φ : Mat k r → ℂ) (T : E) :
    dLR u v (fun g => φ g • T) = fun g => dLR u v φ g • T := by
  induction u with
  | nil => exact Rw_smul v φ T
  | cons X u ih =>
    show LdV X (dLR u v (fun g => φ g • T)) = fun g => LdV X (dLR u v φ) g • T
    rw [ih]
    exact LdV_smul X (dLR u v φ) T

theorem ccle_scalF {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] {A : ℝ} {m : ℕ}
    {f : Mat k r → ℂ} {c : ℝ} (hf : CCle A m f c) : CCle A m (scalF Wp f) c := by
  obtain ⟨hck, hb⟩ := hf
  refine ⟨?_, fun u v hu hv hl g hg => ?_⟩
  · intro g₀ hg₀
    obtain ⟨U, f', hU, hgU, hcd, heq⟩ := hck g₀ hg₀
    refine ⟨U, fun g => f' g • ContinuousLinearMap.id ℂ Wp, hU, hgU, hcd.smul contDiffOn_const,
      fun g hgU' hgG => ?_⟩
    simp only [scalF, heq g hgU' hgG]
  · have h1 := hb u v hu hv hl g hg
    have hsc : dLR u v (scalF Wp f) g = dLR u v f g • ContinuousLinearMap.id ℂ Wp :=
      congrFun (dLR_smul u v f (ContinuousLinearMap.id ℂ Wp)) g
    rw [hsc, norm_smul]
    have hid : ‖ContinuousLinearMap.id ℂ Wp‖ ≤ 1 := ContinuousLinearMap.norm_id_le
    have hg0 : 0 ≤ gN g ^ A := Real.rpow_nonneg (Real.sqrt_nonneg _) A
    calc gN g ^ A * (‖dLR u v f g‖ * ‖ContinuousLinearMap.id ℂ Wp‖) ≤ gN g ^ A * ‖dLR u v f g‖ := by
          apply mul_le_mul_of_nonneg_left _ hg0
          exact mul_le_of_le_one_right (norm_nonneg _) hid
      _ ≤ c := h1

theorem inCC_scalF {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] {A : ℝ} {m : ℕ}
    {f : Mat k r → ℂ} (hf : InCC A m f) : InCC A m (scalF Wp f) := by
  obtain ⟨c, hc⟩ := hf
  exact ⟨c, ccle_scalF hc⟩

theorem inCC_five_four' {A : ℝ} {f : Mat k r → E} (h : InCC A 5 f) : InCC A 4 f := by
  obtain ⟨c, hck, hb⟩ := h
  refine ⟨c, ?_, fun u v hu hv hl g hg => hb u v hu hv (by omega) g hg⟩
  intro g₀ hg₀
  obtain ⟨U, f', hU, hgU, hcd, heq⟩ := hck g₀ hg₀
  exact ⟨U, f', hU, hgU, hcd.of_le (WithTop.coe_le_coe.mpr (Nat.cast_le.mpr (by norm_num))), heq⟩

theorem continuousOn_of_ckOn {m : ℕ∞} {f : Mat k r → E} (h : CkOn m (GV k r) f) :
    ContinuousOn f (GV k r) := by
  intro g₀ hg₀
  obtain ⟨U, f', hU, hgU, hcd, heq⟩ := h g₀ hg₀
  have hc : ContinuousAt f' g₀ := hcd.continuousOn.continuousAt (hU.mem_nhds hgU)
  refine (hc.continuousWithinAt (s := GV k r)).congr_of_eventuallyEq ?_ (heq g₀ hgU hg₀)
  filter_upwards [inter_mem_nhdsWithin (GV k r) (hU.mem_nhds hgU)] with g hg
  exact heq g hg.2 hg.1

theorem integrable_of_inCC (hInt : GNIntSharp) (hLow : GNLower) (hCl : ClosedG) {Wp Wq : Type}
    [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    (D : RealPlaceData k r Wp Wq) {A : ℝ} (hA : AB k r ≤ A) {f : Mat k r → ℂ} (hf : InCC A 5 f) :
    Integrable (fun g : Mt k r => f (Matrix.of g)) D.μG := by
  obtain ⟨c, hCk, hbd⟩ := hf
  have hb0 : ∀ g ∈ GV k r, ‖f g‖ ≤ c * gN g ^ (-A) := by
    intro g hg
    have h1 := hbd [] [] (by simp) (by simp) (by simp) g hg
    have hgN : 0 < gN g := lt_of_lt_of_le one_pos (hLow k r g hg)
    have hpow : 0 < gN g ^ A := Real.rpow_pos_of_pos hgN A
    rw [Real.rpow_neg hgN.le, ← div_eq_mul_inv, le_div_iff₀ hpow]
    have h2 : gN g ^ A * ‖f g‖ ≤ c := h1
    linarith [mul_comm (gN g ^ A) ‖f g‖]
  have hae : ∀ᵐ g ∂D.μG, Matrix.of g ∈ GV k r := ae_iff.mpr D.haarG.conc
  have hGm : MeasurableSet {g : Mt k r | Matrix.of g ∈ GV k r} :=
    (show IsClosed {g : Mt k r | Matrix.of g ∈ GV k r} from (hCl k r).closed).measurableSet
  have hgNc : Continuous fun g : Mt k r => gN (Matrix.of g) := by
    unfold gN
    exact Real.continuous_sqrt.comp (continuous_finset_sum _ fun i _ => continuous_finset_sum _ fun j _ =>
      Complex.continuous_normSq.comp ((continuous_apply j).comp (continuous_apply i)))
  have hint : Integrable (fun g : Mt k r => gN (Matrix.of g) ^ (-A)) D.μG := by
    refine ⟨(hgNc.measurable.pow_const (-A)).aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall fun g => by
      show (0 : ℝ) ≤ gN (Matrix.of g) ^ (-A)
      unfold gN
      exact Real.rpow_nonneg (Real.sqrt_nonneg _) _)]
    exact hInt k r D.μG A D.haarG hA
  have hcont : ContinuousOn (fun g : Mt k r => f (Matrix.of g)) {g : Mt k r | Matrix.of g ∈ GV k r} :=
    continuousOn_of_ckOn hCk
  have hmeas : AEStronglyMeasurable (fun g : Mt k r => f (Matrix.of g)) D.μG := by
    have := hcont.aestronglyMeasurable (μ := D.μG) hGm
    rwa [Measure.restrict_eq_self_of_ae_mem (s := {g : Mt k r | Matrix.of g ∈ GV k r}) hae] at this
  refine (hint.const_mul c).mono' hmeas (hae.mono fun g hg => ?_)
  exact hb0 _ hg

theorem volume_normSq_eq (c : ℝ) :
    volume {q : (Fin r → ℂ) × ℂ | Complex.normSq q.2 = c} = 0 := by
  have hsub : {q : (Fin r → ℂ) × ℂ | Complex.normSq q.2 = c} ⊆
      Set.univ ×ˢ Metric.sphere (0 : ℂ) (Real.sqrt c) := by
    rintro ⟨a, z⟩ hz
    simp only [Set.mem_setOf_eq] at hz
    refine ⟨Set.mem_univ _, ?_⟩
    rw [mem_sphere_zero_iff_norm, ← hz, Complex.normSq_eq_norm_sq, Real.sqrt_sq (norm_nonneg _)]
  refine measure_mono_null hsub ?_
  rw [Measure.volume_eq_prod, Measure.prod_prod, Measure.addHaar_sphere, mul_zero]

theorem bcWeight_nonneg (T T' : ℝ) (q : (Fin r → ℂ) × ℂ) : 0 ≤ bcWeight k r T T' q := by
  unfold bcWeight
  split_ifs with h
  · exact mul_nonneg (Finset.prod_nonneg fun a _ => by positivity) (pow_nonneg (by linarith) _)
  · exact le_rfl

end ReciprocityTheory.ChartRestriction.DS.Mult1.SymBetaA
