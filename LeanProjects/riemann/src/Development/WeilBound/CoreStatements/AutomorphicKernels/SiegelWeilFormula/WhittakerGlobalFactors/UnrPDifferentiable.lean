import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.WhitGenOf
import Development.WeilBound.ThetaLifts.LatticeBasics.EulerHalf

noncomputable section

namespace PositivityTheory.SiegelWeilFormula.Gen.W

open HeckeCharacterZeroLocus.SiegelWeilU NumberField IsDedekindDomain MeasureTheory GlobalTheory.Cont PositivityTheory.PfSWUS.Loc PositivityTheory.Rg.Sw Filter
open scoped TensorProduct Matrix

theorem euler_prod {ι : Type} (q : ι → ℕ) (hq : ∀ v, 2 ≤ q v) (hs : ∀ s : ℝ, 1 < s → Summable fun v => (q v : ℝ) ^ (-s))
    (c : ι → ℂ) (hc : ∀ v, ‖c v‖ ≤ 1) (k : ℕ) : ∃ d : ℂ → ℂ, DifferentiableOn ℂ d {z | 0 < z.re} ∧ ∀ z : ℂ, 0 < z.re →
      HasProd (fun v => 1 - c v * (q v : ℂ) ^ (-(2 * z + (k + 1 : ℕ)))) (d z) := by
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
  refine ⟨fun z => Complex.exp (∑' v, Complex.log (1 + x v z)), fun z hz => ?_, fun z hz => ?_⟩
  · have hz' : 0 < z.re := hz
    have ho : IsOpen {w : ℂ | z.re / 2 < w.re} := isOpen_lt continuous_const Complex.continuous_re
    have := Complex.differentiableOn_tsum_of_summable_norm (F := fun v w => Complex.log (1 + x v w))
      ((hs (z.re + 1) (by linarith)).mul_left (3 / 2)) (fun v w hw => ?_) ho
      fun v w (hw : z.re / 2 < w.re) => hb v w _ (by linarith) (by linarith)
    · exact (this.differentiableAt (ho.mem_nhds (show z.re / 2 < z.re by linarith))).cexp.differentiableWithinAt
    · have hw' : z.re / 2 < w.re := hw
      have hw0 : 0 < w.re := by linarith
      refine (DifferentiableAt.clog (f := fun w => 1 + x v w) ?_ (hsl v w hw0)).differentiableWithinAt
      have : (q v : ℂ) ≠ 0 := by exact_mod_cast (two_pos.trans_le (hq v)).ne'
      exact (((by fun_prop : DifferentiableAt ℂ (fun z : ℂ => -(2 * z + (k + 1 : ℕ))) w).const_cpow
        (Or.inl this)).const_mul _).neg.const_add _
  · have := (Summable.of_norm_bounded ((hs (2 * z.re + 1) (by linarith)).mul_left (3 / 2))
      fun v => hb v z _ hz le_rfl).hasSum.cexp
    convert this using 2 with v
    rw [Function.comp_apply, Complex.exp_log (Complex.slitPlane_ne_zero (hsl v z hz)), sub_eq_add_neg]

def unrP (n M : ℕ) (e : ℤˣ) (q : ℕ) (z : ℂ) : ℂ :=
  ∏ i : Fin n, (1 - ((e : ℤ) : ℂ) ^ (M + (i : ℕ)) * (q : ℂ) ^ (-(2 * z + n - (i : ℕ))))

theorem unramifiedPart_differentiable (n M : ℕ) (e : ℤˣ) (q : ℕ) (hq : q ≠ 0) : Differentiable ℂ (unrP n M e q) := by
  have hq' : (q : ℂ) ≠ 0 := by exact_mod_cast hq
  unfold unrP
  refine Differentiable.fun_finsetProd fun i _ => ?_
  exact (differentiable_const _).sub ((differentiable_const _).mul
    ((by fun_prop : Differentiable ℂ (fun z : ℂ => -(2 * z + n - (i : ℕ)))).const_cpow (Or.inl hq')))

theorem norm_unit_pow (e : ℤˣ) (k : ℕ) : ‖((e : ℤ) : ℂ) ^ k‖ ≤ 1 := by
  rcases Int.units_eq_one_or e with h | h <;> simp [h]

theorem unr_prod {F : Type} [Field F] [NumberField F] (n M : ℕ) (S : Set (HeightOneSpectrum (𝓞 F)))
    (e : HeightOneSpectrum (𝓞 F) → ℤˣ) :
    ∃ D : ℂ → ℂ, DifferentiableOn ℂ D {z | 0 < z.re} ∧ ∀ z : ℂ, 0 < z.re →
      HasProd (fun v : ↥Sᶜ => unrP n M (e v) (Ideal.absNorm v.1.asIdeal) z) (D z) := by
  have key : ∀ i : Fin n, ∃ d : ℂ → ℂ, DifferentiableOn ℂ d {z | 0 < z.re} ∧ ∀ z : ℂ, 0 < z.re →
      HasProd (fun v : ↥Sᶜ => 1 - ((e v : ℤ) : ℂ) ^ (M + (i : ℕ)) * (Ideal.absNorm v.1.asIdeal : ℂ) ^
        (-(2 * z + n - (i : ℕ)))) (d z) := by
    intro i
    obtain ⟨d, hd, hp⟩ := euler_prod (ι := ↥Sᶜ) (fun v => Ideal.absNorm v.1.asIdeal)
      (fun v => NumberField.HeightOneSpectrum.one_lt_absNorm v.1)
      (fun s hs => (ReciprocityTheory.Cheb.summable_absNorm_rpow_ideal F hs).comp_injective
        (HeightOneSpectrum.asIdeal_injective.comp Subtype.val_injective))
      (fun v => ((e v : ℤ) : ℂ) ^ (M + (i : ℕ))) (fun v => norm_unit_pow _ _) (n - 1 - i)
    refine ⟨d, hd, fun z hz => ?_⟩
    convert hp z hz using 4 with v
    have hi : (n - 1 - (i : ℕ) + 1 : ℕ) = n - i := by omega
    rw [hi, Nat.cast_sub i.2.le]
    ring_nf
  choose d hd hp using key
  refine ⟨fun z => ∏ i, d i z, DifferentiableOn.fun_finsetProd fun i _ => hd i, fun z hz => ?_⟩
  exact hasProd_prod fun i _ => hp i z hz

theorem eq_of_eqOn_right {f g : ℂ → ℂ} (hf : Differentiable ℂ f) (hg : Differentiable ℂ g) (t : ℝ)
    (h : ∀ z : ℂ, t < z.re → f z = g z) : f = g := by
  have ho : IsOpen {w : ℂ | t < w.re} := isOpen_lt continuous_const Complex.continuous_re
  have hz : ((t + 1 : ℝ) : ℂ) ∈ {w : ℂ | t < w.re} := by simp
  have hev : f =ᶠ[nhds ((t + 1 : ℝ) : ℂ)] g := Filter.eventually_of_mem (ho.mem_nhds hz) fun w hw => h w hw
  have := AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq (f := f) (g := g) (U := Set.univ)
    (fun z _ => hf.analyticAt z) (fun z _ => hg.analyticAt z) isPreconnected_univ (Set.mem_univ _) hev
  funext z
  exact this (Set.mem_univ z)

theorem hasProd_split {α : Type} (f : α → ℂ) (S : Finset α) (D : ℂ)
    (h : HasProd (fun v : ↥((↑S : Set α)ᶜ) => f v) D) : HasProd f ((∏ v ∈ S, f v) * D) := by
  have ha : HasProd (fun v : ↥(↑S : Set α) => f v) (∏ v ∈ S, f v) := by
    convert hasProd_fintype (fun v : ↥(↑S : Set α) => f v) using 1
    exact (Finset.prod_coe_sort S f).symm
  exact ha.mul_compl h

end PositivityTheory.SiegelWeilFormula.Gen.W

end
