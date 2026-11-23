import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.PetIPSmulRight
import Development.AbelianVarietyTheory.Definitions.Foundations.RepL
import CompanionTheory.EightfoldTheory.VariationTheory.AutomorphicForms.Newform
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

noncomputable section

namespace GlobalTheory.EisM

theorem lipschitz_periodic : ∀ (j L : ℕ) (φ : ZMod L → ℂ) (z : ℂ), 2 ≤ j → 0 < L → 0 < z.im → Tendsto (fun R : ℕ => ∑ d ∈ Finset.Icc (-(R : ℤ)) R, φ (d : ZMod L) * trm j 0 (z + d)) atTop (𝓝 ((-2 * π * Complex.I / L) ^ j / (j - 1).factorial * ∑' m : ℕ, ((m + 1 : ℕ) : ℂ) ^ (j - 1) * hat φ (m + 1 : ℕ) * cexp (2 * π * Complex.I * (m + 1 : ℕ) * z / L))) := by
  intro j L φ z hj hL hz
  haveI : NeZero L := ⟨hL.ne'⟩
  obtain ⟨k, rfl⟩ : ∃ k, j = k + 2 := ⟨j - 2, by omega⟩
  have htrm : ∀ w : ℂ, trm (k + 2) 0 w = (w ^ (k + 2))⁻¹ := fun w => by simp [trm]
  set f : ℤ → ℂ := fun d => φ (d : ZMod L) * ((z + d) ^ (k + 2))⁻¹ with hf_def
  obtain ⟨M, hM⟩ : ∃ M, ∀ x, ‖φ x‖ ≤ M := ⟨∑ x, ‖φ x‖, fun x =>
    Finset.single_le_sum (f := fun x => ‖φ x‖) (fun _ _ => norm_nonneg _) (Finset.mem_univ x)⟩
  have hs0 : ∀ w : ℂ, Summable fun d : ℤ => ((w + d) ^ (k + 2))⁻¹ := fun w => by
    have := EisensteinSeries.linear_right_summable w 1 (k := ((k + 2 : ℕ) : ℤ)) (by push_cast; omega)
    simp only [Int.cast_one, one_mul, zpow_natCast] at this
    exact this
  have hfs : Summable f := by
    refine Summable.of_norm_bounded ((hs0 z).norm.mul_left M) fun d => ?_
    simp only [f, norm_mul]
    exact mul_le_mul_of_nonneg_right (hM _) (norm_nonneg _)
  have hlim : Tendsto (fun R : ℕ => ∑ d ∈ Finset.Icc (-(R : ℤ)) R, f d) atTop (𝓝 (∑' d, f d)) :=
    hfs.hasSum.comp (tendsto_atTop_finset_of_monotone
      (fun a b hab => Finset.Icc_subset_Icc (by omega) (by omega)) fun x => ⟨x.natAbs, Finset.mem_Icc.mpr
        ⟨by rw [Int.natCast_natAbs]; exact neg_abs_le x, by rw [Int.natCast_natAbs]; exact le_abs_self x⟩⟩)
  have hval : ∑' d, f d = (-2 * π * Complex.I / L) ^ (k + 2) / (k + 2 - 1).factorial *
      ∑' m : ℕ, ((m + 1 : ℕ) : ℂ) ^ (k + 2 - 1) * hat φ (m + 1 : ℕ) * cexp (2 * π * Complex.I * (m + 1 : ℕ) * z / L) := by
    set C : ℂ := (-2 * π * Complex.I) ^ (k + 2) / (k + 1).factorial with hC
    set w : ℕ → ℂ := fun r => (z + r) / L with hw_def
    have hLc : (L : ℂ) ≠ 0 := by exact_mod_cast hL.ne'
    have hwim : ∀ r : ℕ, 0 < (w r).im := fun r => by
      simp only [w, Complex.div_natCast_im, Complex.add_im, Complex.natCast_im, add_zero]; positivity
    set q : ℕ → ℂ := fun r => cexp (2 * π * Complex.I * w r) with hq_def
    have hq : ∀ r, ‖q r‖ < 1 := fun r => UpperHalfPlane.norm_exp_two_pi_I_lt_one ⟨w r, hwim r⟩
    set g : ℕ → ℕ → ℂ := fun r m => ((m + 1 : ℕ) : ℂ) ^ (k + 1) * q r ^ (m + 1) with hg_def
    have hgs : ∀ r, Summable (g r) := fun r => by
      have h0 : Summable (fun n : ℕ => (n : ℂ) ^ (k + 1) * q r ^ n) :=
        summable_pow_mul_geometric_of_norm_lt_one (k + 1) (hq r)
      have h1 := (summable_nat_add_iff (f := fun n : ℕ => (n : ℂ) ^ (k + 1) * q r ^ n) 1).mpr h0
      refine h1.congr fun m => ?_
      simp only [g, Nat.cast_add, Nat.cast_one]
    have hres : ∀ r : Fin L, HasSum (fun n : ℤ => f (n * L + (r : ℕ)))
        (φ ((r : ℕ) : ZMod L) * ((L : ℂ)⁻¹) ^ (k + 2) * (C * ∑' m, g r m)) := by
      intro r
      have hid := EisensteinSeries.qExpansion_identity_pnat (k := k + 1) (by omega) ⟨w r, hwim r⟩
      rw [tsum_pnat_eq_tsum_succ (f := fun n : ℕ => (n : ℂ) ^ (k + 1) *
        cexp (2 * π * Complex.I * ((⟨w r, hwim r⟩ : ℍ) : ℂ)) ^ n)] at hid
      have h1 : HasSum (fun n : ℤ => ((w r + n) ^ (k + 2))⁻¹) (C * ∑' m, g r m) := by
        convert (hs0 (w r)).hasSum using 1
        simp only [one_div, UpperHalfPlane.coe_mk_subtype] at hid
        rw [hid]
      have h2 := h1.mul_left (φ ((r : ℕ) : ZMod L) * ((L : ℂ)⁻¹) ^ (k + 2))
      refine (congrArg (fun F => HasSum F _) (funext fun n => ?_)).mpr h2
      simp only [f]
      have e1 : (((n * L + (r : ℕ) : ℤ)) : ZMod L) = ((r : ℕ) : ZMod L) := by push_cast; simp
      have e2 : z + (((n * L + (r : ℕ) : ℤ)) : ℂ) = L * (w r + n) := by
        simp only [w]; push_cast; field_simp; ring
      rw [e1, e2, mul_pow, mul_inv, inv_pow]; ring
    let e : Fin L × ℤ ≃ ℤ := (Equiv.prodComm _ _).trans (Int.divModEquiv L).symm
    have he : ∀ p : Fin L × ℤ, e p = p.2 * L + ((p.1 : ℕ) : ℤ) := fun p => by
      simp [e, Int.divModEquiv_symm_apply]
    have hfe : HasSum (f ∘ e) (∑' d, f d) := by rw [e.hasSum_iff]; exact hfs.hasSum
    have hg2 : HasSum (fun r : Fin L => φ ((r : ℕ) : ZMod L) * ((L : ℂ)⁻¹) ^ (k + 2) * (C * ∑' m, g r m))
        (∑' d, f d) :=
      hfe.prod_fiberwise fun r => by
        convert hres r using 1
        funext n; simp only [Function.comp_apply, he]
    have hsum : ∑ r : Fin L, φ ((r : ℕ) : ZMod L) * ∑' m, g r m = ∑' m : ℕ, ((m + 1 : ℕ) : ℂ) ^ (k + 1) *
        hat φ (m + 1 : ℕ) * cexp (2 * π * Complex.I * (m + 1 : ℕ) * z / L) := by
      simp_rw [← tsum_mul_left]
      rw [← Summable.tsum_finsetSum (f := fun (r : Fin L) m => φ ((r : ℕ) : ZMod L) * g r m)
        (fun r _ => (hgs r).mul_left _)]
      refine tsum_congr fun m => ?_
      rw [Fin.sum_univ_eq_sum_range (fun y => φ (y : ZMod L) * g y m) L]
      simp only [hat, Finset.mul_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun y _ => ?_
      have : q y ^ (m + 1) = cexp (2 * π * Complex.I * (y * (((m + 1 : ℕ) : ℤ) : ℂ)) / L) *
          cexp (2 * π * Complex.I * (m + 1 : ℕ) * z / L) := by
        rw [hq_def, ← Complex.exp_nat_mul, ← Complex.exp_add]
        congr 1
        simp only [w]; push_cast; field_simp; ring
      simp only [g, this]; ring
    rw [hg2.unique (hasSum_fintype _), show k + 2 - 1 = k + 1 by omega, ← hsum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [hC, div_pow]; ring
  rw [← hval]
  refine hlim.congr fun R => Finset.sum_congr rfl fun d _ => ?_
  simp [f, htrm]

end GlobalTheory.EisM
