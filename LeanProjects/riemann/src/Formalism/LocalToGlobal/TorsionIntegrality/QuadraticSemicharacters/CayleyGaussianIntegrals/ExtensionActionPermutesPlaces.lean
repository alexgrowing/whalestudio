import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.KerPNonzero
import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.CayleyGaussianIntegrals.MatrixFormFourfoldBlock

noncomputable section
open scoped BigOperators ComplexConjugate

namespace Formalism.L2.Th1.H

section SlopeTestRemainingChoices

variable {V : Type*} [AddCommGroup V] [Module ℂ V]

theorem herm_self_real (H : Sesq V) (hH : IsHerm H) (z : V) : (((H z z).re : ℝ) : ℂ) = H z z := by
  exact Complex.conj_eq_iff_re.1 (hH z z).symm

theorem wt_eq_cexp (H : Sesq V) (hH : IsHerm H) (z : V) :
    (wt H z : ℂ) = Complex.exp (-(Real.pi : ℂ) * H z z) := by
  rw [wt, Complex.ofReal_exp]
  push_cast
  rw [herm_self_real H hH z]

end SlopeTestRemainingChoices

theorem diagonalTerm : DiagTerm := by
  intro V _ _ H hH v z
  rw [opU, kerK, wt_eq_cexp H hH, ← Complex.exp_add, ← Complex.exp_add, ← Complex.exp_add]
  congr 1
  have hc : H z v = conj (H v z) := hH v z
  have hw : conj (H v z) = H v z - 2 * Complex.I * ((H v z).im : ℂ) := by
    apply Complex.ext <;> simp
    all_goals ring
  simp only [map_add, LinearMap.add_apply, hc, hw, altE]
  ring

theorem kernelTermShift : TermShift := by
  intro V _ _ H hH α δ Ae hI hA
  have hi : ∀ a b, H (δ a) (δ b) = H a b := fun a b => hI a b
  refine ⟨fun x z => ?_, fun z => ?_⟩
  · obtain ⟨v, rfl⟩ : ∃ v, x = Ae (δ v) := ⟨δ.symm (Ae.symm x), by simp⟩
    obtain ⟨y, rfl⟩ : ∃ y, z = δ y := ⟨δ.symm z, by simp⟩
    simp only [termT, phiC, gq, opU, kerK, cayC, wt_eq_cexp H hH, LinearEquiv.symm_apply_apply]
    simp only [← Complex.exp_add, mul_assoc]
    congr 2
    simp only [hA, LinearEquiv.symm_apply_apply, map_sub, map_add, map_smul, LinearMap.sub_apply,
      LinearMap.add_apply, LinearMap.smul_apply, hi, smul_eq_mul]
    ring
  · obtain ⟨y, rfl⟩ : ∃ y, z = δ y := ⟨δ.symm z, by simp⟩
    rw [gq, Complex.norm_exp]
    congr 1
    have hc : H (δ y) y = conj (H y (δ y)) := hH y (δ y)
    simp only [hA, LinearEquiv.symm_apply_apply, map_sub, LinearMap.sub_apply, hi, hc, neg_mul,
      Complex.neg_re, Complex.re_ofReal_mul, Complex.sub_re, Complex.conj_re]
    ring

theorem formNormEquiv : FormNorm := by
  intro V _ _ _ H hH hpos
  haveI : ProperSpace V := FiniteDimensional.proper ℂ V
  have hhom : ∀ (r : ℝ) (z : V), (H ((r : ℂ) • z) ((r : ℂ) • z)).re = r ^ 2 * (H z z).re := by
    intro r z
    simp only [map_smul, map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, Complex.conj_ofReal]
    rw [Complex.re_ofReal_mul, Complex.re_ofReal_mul]; ring
  let b := Module.finBasis ℂ V
  have hexp : ∀ z, H z z = ∑ i, ∑ j, conj (b.repr z i) * (b.repr z j * H (b j) (b i)) := by
    intro z
    conv_lhs => rw [← b.sum_repr z]
    simp only [map_sum, map_smul, map_smulₛₗ, LinearMap.sum_apply, LinearMap.smul_apply,
      smul_eq_mul, Finset.mul_sum]
  have hcont : Continuous fun z : V => (H z z).re := by
    have hc : ∀ i, Continuous fun z : V => b.repr z i := fun i => (b.coord i).continuous_of_finiteDimensional
    have e : (fun z : V => (H z z).re)
        = fun z => (∑ i, ∑ j, conj (b.repr z i) * (b.repr z j * H (b j) (b i))).re := by
      funext z; rw [hexp z]
    rw [e]
    exact Complex.continuous_re.comp (continuous_finset_sum _ fun i _ => continuous_finset_sum _ fun j _ =>
      (Complex.continuous_conj.comp (hc i)).mul ((hc j).mul continuous_const))
  have hunit : ∀ w : V, w ≠ 0 → ((‖w‖⁻¹ : ℝ) : ℂ) • w ∈ Metric.sphere (0 : V) 1 := fun w hw => by
    rw [mem_sphere_zero_iff_norm, norm_smul, Complex.norm_real, norm_inv, norm_norm,
      inv_mul_cancel₀ (norm_ne_zero_iff.2 hw)]
  by_cases hV : ∃ v : V, v ≠ 0
  swap
  · push_neg at hV
    refine ⟨1, 1, one_pos, one_pos, fun z => ?_⟩
    rw [hV z]; simp
  obtain ⟨v, hv⟩ := hV
  have hsph : IsCompact (Metric.sphere (0 : V) 1) := isCompact_sphere 0 1
  have hne : (Metric.sphere (0 : V) 1).Nonempty := ⟨_, hunit v hv⟩
  obtain ⟨a, ha, hamin⟩ := hsph.exists_isMinOn hne hcont.continuousOn
  obtain ⟨m, hm, hmmax⟩ := hsph.exists_isMaxOn hne hcont.continuousOn
  have ha0 : a ≠ 0 := by
    intro h; rw [h, mem_sphere_zero_iff_norm, norm_zero] at ha; exact zero_ne_one ha
  have hcpos : 0 < (H a a).re := hpos a ha0
  refine ⟨(H a a).re, (H m m).re, hcpos, lt_of_lt_of_le hcpos (isMaxOn_iff.1 hmmax a ha), fun z => ?_⟩
  by_cases hz : z = 0
  · subst hz; simp
  have hr : 0 < ‖z‖ := norm_pos_iff.2 hz
  have h1 := isMinOn_iff.1 hamin _ (hunit z hz)
  have h2 := isMaxOn_iff.1 hmmax _ (hunit z hz)
  rw [hhom] at h1 h2
  have e : (‖z‖⁻¹) ^ 2 * (H z z).re * ‖z‖ ^ 2 = (H z z).re := by field_simp
  have hr2 : 0 ≤ ‖z‖ ^ 2 := by positivity
  constructor
  · calc (H a a).re * ‖z‖ ^ 2 ≤ (‖z‖⁻¹) ^ 2 * (H z z).re * ‖z‖ ^ 2 := mul_le_mul_of_nonneg_right h1 hr2
      _ = (H z z).re := e
  · calc (H z z).re = (‖z‖⁻¹) ^ 2 * (H z z).re * ‖z‖ ^ 2 := e.symm
      _ ≤ (H m m).re * ‖z‖ ^ 2 := mul_le_mul_of_nonneg_right h2 hr2

end Formalism.L2.Th1.H
