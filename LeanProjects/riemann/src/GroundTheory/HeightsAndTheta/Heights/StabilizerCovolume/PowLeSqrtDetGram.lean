import Mathlib
import GroundTheory.HeightsAndTheta.Heights.CovolumeGram
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.NineStatements

open MeasureTheory Module

theorem pow_le_sqrt_det_gram {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    {m : ℕ} (b : Fin m → V) (hb : LinearIndependent ℝ b) {lam : ℝ} (hlam : 0 ≤ lam)
    (hmin : ∀ x ∈ Submodule.span ℤ (Set.range b), x ≠ 0 → lam ≤ ‖x‖) :
    (lam / Real.sqrt m) ^ m ≤ Real.sqrt (Matrix.gram ℝ b).det := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp
  set W := Submodule.span ℝ (Set.range b)
  let B : Basis (Fin m) ℝ W := Basis.span hb
  have : FiniteDimensional ℝ W := FiniteDimensional.span_of_finite ℝ (Set.finite_range b)
  let _ : MeasurableSpace W := borel W
  have : BorelSpace W := ⟨rfl⟩
  have hBW : ∀ i, ((B i : W) : V) = b i := fun i => congrArg Subtype.val (Basis.span_apply hb i)
  have hfin : finrank ℝ W = m := by rw [finrank_eq_card_basis B, Fintype.card_fin]
  let Λ : Submodule ℤ W := Submodule.span ℤ (Set.range B)
  have hcov : ZLattice.covolume Λ = Real.sqrt (Matrix.gram ℝ b).det := by
    rw [GroundTheory.Heights₂.Heights.covolume_eq_sqrt_det_gram Λ (B.restrictScalars ℤ)]
    congr 2
    ext i j
    simp only [Matrix.gram, Matrix.of_apply]
    rw [Basis.restrictScalars_apply, Basis.restrictScalars_apply]
    exact congrArg₂ (inner ℝ) (hBW i) (hBW j)
  have hF := ZSpan.isAddFundamentalDomain' B (volume : Measure W)
  have hFvol : volume (ZSpan.fundamentalDomain B) =
      ENNReal.ofReal (Real.sqrt (Matrix.gram ℝ b).det) := by
    rw [← hcov, ZLattice.covolume_eq_measure_fundamentalDomain Λ volume
      (ZSpan.isAddFundamentalDomain B volume), measureReal_def, ENNReal.ofReal_toReal]
    exact (ZSpan.fundamentalDomain_isBounded B).measure_lt_top.ne
  let o : OrthonormalBasis (Fin m) ℝ W := (stdOrthonormalBasis ℝ W).reindex (finCongr hfin)
  set r := lam / Real.sqrt m with hr
  let f : W →ₗ[ℝ] (Fin m → ℝ) :=
    (WithLp.linearEquiv 2 ℝ (Fin m → ℝ)).toLinearMap ∘ₗ o.repr.toLinearEquiv.toLinearMap
  have hf : ∀ x, f x = WithLp.ofLp (o.repr x) := fun x => rfl
  let s : Set W := f ⁻¹' Set.univ.pi fun _ => Set.Ioo (-r) r
  have hs_symm : ∀ x ∈ s, -x ∈ s := by
    intro x hx i _
    have := hx i (Set.mem_univ i)
    simp only [map_neg, Pi.neg_apply, Set.mem_Ioo] at this ⊢
    constructor <;> linarith [this.1, this.2]
  have hs_conv : Convex ℝ s :=
    (convex_pi fun i _ => convex_Ioo (-r) r).linear_preimage f
  have hs_vol : volume s = ENNReal.ofReal (2 * r) ^ m := by
    have h1 : s = o.repr ⁻¹' (WithLp.ofLp ⁻¹' Set.univ.pi fun _ => Set.Ioo (-r) r) := rfl
    rw [h1, (o.measurePreserving_repr).measure_preimage
      (((MeasurableSet.univ_pi fun _ => measurableSet_Ioo).preimage
        (PiLp.volume_preserving_ofLp (Fin m)).measurable).nullMeasurableSet),
      (PiLp.volume_preserving_ofLp (Fin m)).measure_preimage
        (MeasurableSet.univ_pi fun _ => measurableSet_Ioo).nullMeasurableSet,
      Real.volume_pi_Ioo, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    congr 2
    ring
  have hs_lat : ∀ x : W, x ∈ Λ → x ∈ s → x = 0 := by
    intro x hxΛ hxs
    by_contra hx0
    have hxV : (x : V) ∈ Submodule.span ℤ (Set.range b) := by
      obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).1 hxΛ
      refine (Submodule.mem_span_range_iff_exists_fun ℤ).2 ⟨c, ?_⟩
      rw [← hc, Submodule.coe_sum]
      simp [hBW]
    have hxV0 : (x : V) ≠ 0 := fun h => hx0 (Subtype.ext h)
    have hr0 : 0 < r := by
      have := hxs ⟨0, hm⟩ (Set.mem_univ _)
      exact neg_lt_self_iff.1 (this.1.trans this.2)
    have hnorm : ‖(x : V)‖ < lam := by
      have hxn : ‖(x : V)‖ = ‖o.repr x‖ := by
        rw [LinearIsometryEquiv.norm_map]
        rfl
      rw [hxn, EuclideanSpace.norm_eq]
      have hsum : ∑ i, ‖(o.repr x) i‖ ^ 2 < ∑ _i : Fin m, r ^ 2 := by
        have : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
        refine Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty fun i _ => ?_
        have := hxs i (Set.mem_univ i)
        rw [hf] at this
        rw [Real.norm_eq_abs, sq_abs]
        exact sq_lt_sq' this.1 this.2
      have hlam_eq : lam = Real.sqrt (∑ _i : Fin m, r ^ 2) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
          Real.sqrt_mul (Nat.cast_nonneg m), Real.sqrt_sq hr0.le, hr,
          mul_div_cancel₀ _ (Real.sqrt_pos.2 (by exact_mod_cast hm)).ne']
      rw [hlam_eq]
      exact Real.sqrt_lt_sqrt (Finset.sum_nonneg fun i _ => by positivity) hsum
    exact absurd (hmin _ hxV hxV0) (not_le.2 hnorm)
  by_contra hlt
  push Not at hlt
  have hr_nonneg : 0 ≤ r := div_nonneg hlam (Real.sqrt_nonneg _)
  have hreal : Real.sqrt (Matrix.gram ℝ b).det * 2 ^ m < (2 * r) ^ m := by
    rw [mul_pow, mul_comm]
    exact mul_lt_mul_of_pos_left hlt (by positivity)
  have h2 : (2 : ENNReal) ^ m = ENNReal.ofReal ((2 : ℝ) ^ m) := by
    rw [ENNReal.ofReal_pow (by norm_num)]
    simp
  have hbig : volume (ZSpan.fundamentalDomain B) * 2 ^ finrank ℝ W < volume s := by
    rw [hFvol, hs_vol, hfin, h2, ← ENNReal.ofReal_mul (Real.sqrt_nonneg _),
      ← ENNReal.ofReal_pow (by positivity)]
    exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg (by positivity)).2 hreal
  have : Countable (Submodule.span ℤ (Set.range B)).toAddSubgroup :=
    inferInstanceAs (Countable (Submodule.span ℤ (Set.range B)))
  obtain ⟨x, hx0, hxs⟩ := exists_ne_zero_mem_lattice_of_measure_mul_two_pow_lt_measure hF hs_symm hs_conv hbig
  exact hx0 (Subtype.ext (hs_lat _ x.2 hxs))

end GroundTheory.Heights₂.Heights.NineStatements
