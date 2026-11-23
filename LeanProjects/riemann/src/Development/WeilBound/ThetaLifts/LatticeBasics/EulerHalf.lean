import Mathlib
import Development.WeilBound.ThetaLifts.LatticeBasics.HodgeTateFromSandwich
import ReciprocityTheory.Chebotarev.EulerSum

noncomputable section

namespace GlobalTheory.ThK.Dbl

open NumberField IsDedekindDomain GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

theorem euler_half {ι : Type} (q : ι → ℕ) (hq : ∀ v, 2 ≤ q v) (hs : ∀ s : ℝ, 1 < s → Summable fun v => (q v : ℝ) ^ (-s))
    (c : ι → ℂ) (hc : ∀ v, ‖c v‖ ≤ 1) (k : ℕ) : ∃ d : ℂ → ℂ, DifferentiableOn ℂ d {z | 0 < z.re} ∧ ∀ z : ℂ, 0 < z.re →
      d z ≠ 0 ∧ HasProd (fun v => (1 - c v * (q v : ℂ) ^ (-(2 * z + (k + 1 : ℕ))))⁻¹) (d z) := by
  let x : ι → ℂ → ℂ := fun v z => -(c v * (q v : ℂ) ^ (-(2 * z + (k + 1 : ℕ))))
  have h1 : ∀ v, (1 : ℝ) ≤ q v := fun v => by exact_mod_cast one_le_two.trans (hq v)
  have hx : ∀ v z (t : ℝ), t ≤ 2 * z.re + 1 → ‖x v z‖ ≤ (q v : ℝ) ^ (-t) := fun v z t ht => by
    rw [norm_neg, norm_mul, Complex.norm_natCast_cpow_of_pos (two_pos.trans_le (hq v))]
    refine (mul_le_of_le_one_left (by positivity) (hc v)).trans (Real.rpow_le_rpow_of_exponent_le (h1 v) ?_)
    have : (0 : ℝ) ≤ k := k.cast_nonneg
    simp only [Complex.neg_re, Complex.add_re, Complex.natCast_re, Complex.mul_re, Complex.re_ofNat, Complex.im_ofNat]
    push_cast
    linarith
  have hh : ∀ v z, 0 < z.re → ‖x v z‖ ≤ 1 / 2 := fun v z hz => by
    refine (hx v z 1 (by linarith)).trans ?_
    rw [Real.rpow_neg_one, one_div]
    exact inv_anti₀ two_pos (by exact_mod_cast hq v)
  have hb : ∀ v z (t : ℝ), 0 < z.re → t ≤ 2 * z.re + 1 → ‖Complex.log (1 + x v z)‖ ≤ 3 / 2 * (q v : ℝ) ^ (-t) :=
    fun v z t hz ht => (Complex.norm_log_one_add_half_le_self (hh v z hz)).trans (by gcongr; exact hx v z t ht)
  have hsl : ∀ v z, 0 < z.re → 1 + x v z ∈ Complex.slitPlane := fun v z hz =>
    Complex.mem_slitPlane_of_norm_lt_one ((hh v z hz).trans_lt (by norm_num))
  refine ⟨fun z => Complex.exp (-∑' v, Complex.log (1 + x v z)), fun z hz => ?_, fun z hz => ⟨Complex.exp_ne_zero _, ?_⟩⟩
  · have hz' : 0 < z.re := hz
    have ho : IsOpen {w : ℂ | z.re / 2 < w.re} := isOpen_lt continuous_const Complex.continuous_re
    have := Complex.differentiableOn_tsum_of_summable_norm (F := fun v w => Complex.log (1 + x v w))
      ((hs (z.re + 1) (by linarith)).mul_left (3 / 2)) (fun v w hw => ?_) ho
      fun v w (hw : z.re / 2 < w.re) => hb v w _ (by linarith) (by linarith)
    · exact (this.differentiableAt (ho.mem_nhds (show z.re / 2 < z.re by linarith))).neg.cexp.differentiableWithinAt
    · have hw' : z.re / 2 < w.re := hw
      have hw0 : 0 < w.re := by linarith
      refine (DifferentiableAt.clog (f := fun w => 1 + x v w) ?_ (hsl v w hw0)).differentiableWithinAt
      have : (q v : ℂ) ≠ 0 := by exact_mod_cast (two_pos.trans_le (hq v)).ne'
      exact (((by fun_prop : DifferentiableAt ℂ (fun z : ℂ => -(2 * z + (k + 1 : ℕ))) w).const_cpow
        (Or.inl this)).const_mul _).neg.const_add _
  · have := (Summable.of_norm_bounded ((hs (2 * z.re + 1) (by linarith)).mul_left (3 / 2))
      fun v => hb v z _ hz le_rfl).hasSum.neg.cexp
    convert this using 2 with v
    rw [Function.comp, Complex.exp_neg, Complex.exp_log (Complex.slitPlane_ne_zero (hsl v z hz)), sub_eq_add_neg]

open Classical in
theorem dProd : DProd := by
  intro F E _ _ _ _ _ n T
  choose d h1 h2 using fun i => euler_half (ι := {v : Pl F // v ∉ T}) (fun v => Ideal.absNorm v.1.asIdeal)
    (fun v => NumberField.HeightOneSpectrum.one_lt_absNorm v.1)
    (fun s hs => (ReciprocityTheory.Cheb.summable_absNorm_rpow_ideal F hs).comp_injective
      (HeightOneSpectrum.asIdeal_injective.comp Subtype.val_injective))
    (fun v => (if Nonempty (E →ₐ[F] Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v.1) then 1 else -1) ^ (n - (i + 1)))
    (fun v => by split_ifs <;> simp) i
  exact ⟨fun z => ∏ i ∈ Finset.range n, d i z, DifferentiableOn.fun_finsetProd fun i _ => h1 i, fun z hz =>
    ⟨Finset.prod_ne_zero_iff.2 fun i _ => (h2 i z hz).1, hasProd_prod fun i _ => (h2 i z hz).2⟩⟩

end GlobalTheory.ThK.Dbl

end
