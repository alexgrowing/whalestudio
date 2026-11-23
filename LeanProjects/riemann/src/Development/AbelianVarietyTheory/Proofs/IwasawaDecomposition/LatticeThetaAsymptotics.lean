import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NonemptyRayDataOfNeZero
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.SummableLatticeExpNegPiMulNormSqDiv

open Complex Filter Asymptotics
open scoped RealInnerProductSpace

namespace GlobalTheory.PlaneTheta

theorem exists_pos_le_of_summable {ι : Type*} {q : ι → ℝ}
    (h : Summable fun i => Real.exp (-q i)) : ∃ δ : ℝ, 0 < δ ∧ ∀ i, 0 < q i → δ ≤ q i := by
  have h1 := h.tendsto_cofinite_zero.eventually (gt_mem_nhds (Real.exp_pos (-1)))
  rw [Filter.eventually_cofinite] at h1
  have h2 : {i | ¬ Real.exp (-q i) < Real.exp (-1) ∧ 0 < q i}.Finite := h1.subset fun i hi => hi.1
  have h3 : ∀ᶠ δ in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      ∀ i ∈ {i | ¬ Real.exp (-q i) < Real.exp (-1) ∧ 0 < q i}, δ < q i :=
    (Filter.eventually_all_finite h2).2 fun i hi => nhdsWithin_le_nhds (gt_mem_nhds hi.2)
  have h4 : ∀ᶠ δ in nhdsWithin (0 : ℝ) (Set.Ioi 0), δ < 1 :=
    nhdsWithin_le_nhds (gt_mem_nhds one_pos)
  obtain ⟨δ, ⟨h5, h6⟩, h7⟩ := ((h3.and h4).and self_mem_nhdsWithin).exists
  refine ⟨δ, h7, fun i hi => ?_⟩
  by_cases hc : Real.exp (-q i) < Real.exp (-1)
  · rw [Real.exp_lt_exp] at hc
    linarith
  · exact (h5 i ⟨hc, hi⟩).le

theorem abs_tsum_le {ι : Type*} {q f : ι → ℝ} {δ s : ℝ} (hs : 1 ≤ s)
    (h : Summable fun i => Real.exp (-q i)) (hf : ∀ i, |f i| ≤ Real.exp (-(s * q i)))
    (hδ : ∀ i, f i ≠ 0 → δ ≤ q i) :
    |∑' i, f i| ≤ (Real.exp δ * ∑' i, Real.exp (-q i)) * Real.exp (-δ * s) := by
  have hb : ∀ i, ‖f i‖ ≤ Real.exp δ * Real.exp (-q i) * Real.exp (-δ * s) := by
    intro i
    by_cases h0 : f i = 0
    · rw [h0, norm_zero]; positivity
    · refine (hf i).trans ?_
      rw [← Real.exp_add, ← Real.exp_add, Real.exp_le_exp]
      nlinarith [hδ i h0]
  have := tsum_of_norm_bounded ((h.hasSum.mul_left (Real.exp δ)).mul_right (Real.exp (-δ * s))) hb
  exact this

section Lattice

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]

omit [MeasurableSpace E] [BorelSpace E] [IsZLattice ℝ L] in
theorem atTop_bound (u : E) (hu : ∀ x : L, (x : E) + u ≠ 0) :
    ∃ c : ℝ, 0 < c ∧ (fun t : ℝ => ∑' x : L, Real.exp (-Real.pi * t * ‖(x : E) + u‖ ^ 2))
      =O[atTop] (fun t => Real.exp (-c * t)) := by
  have h : Summable fun x : L => Real.exp (-(Real.pi * ‖(x : E) + u‖ ^ 2)) := by
    simpa only [neg_mul] using summable_lattice_exp_neg_mul_norm_add_sq L Real.pi_pos u
  obtain ⟨δ, hδ, hq⟩ := exists_pos_le_of_summable h
  refine ⟨δ, hδ, IsBigO.of_bound (Real.exp δ * ∑' x : L, Real.exp (-(Real.pi * ‖(x : E) + u‖ ^ 2))) ?_⟩
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with t ht
  rw [Real.norm_of_nonneg (Real.exp_pos _).le, Real.norm_eq_abs]
  refine abs_tsum_le ht h (fun x => ?_) (fun x _ => hq x ?_)
  · rw [abs_of_pos (Real.exp_pos _)]
    apply le_of_eq; congr 1; ring
  · have := norm_pos_iff.2 (hu x)
    have := Real.pi_pos
    positivity

theorem zero_bound (hE : Module.finrank ℝ E = 2) (u : E) :
    ∃ c : ℝ, 0 < c ∧ (fun t : ℝ => (∑' x : L, Real.exp (-Real.pi * t * ‖(x : E) + u‖ ^ 2))
      - 1 / (t * ZLattice.covolume L))
      =O[nhdsWithin 0 (Set.Ioi 0)] (fun t => Real.exp (-c / t)) := by
  classical
  have h : Summable fun y : dualLattice L => Real.exp (-(Real.pi * ‖(y : E)‖ ^ 2)) := by
    simpa only [neg_mul] using summable_lattice_exp_neg_mul_norm_sq (dualLattice L) Real.pi_pos
  obtain ⟨δ, hδ, hq⟩ := exists_pos_le_of_summable h
  have hV := ZLattice.covolume_pos L MeasureTheory.volume
  set C := Real.exp δ * ∑' y : dualLattice L, Real.exp (-(Real.pi * ‖(y : E)‖ ^ 2)) with hC
  have hC0 : 0 ≤ C := mul_nonneg (Real.exp_pos _).le (tsum_nonneg fun _ => (Real.exp_pos _).le)
  refine ⟨δ / 2, by positivity, IsBigO.of_bound ((ZLattice.covolume L)⁻¹ * (2 / δ) * C) ?_⟩
  have h4 : ∀ᶠ t in nhdsWithin (0 : ℝ) (Set.Ioi 0), t < 1 :=
    nhdsWithin_le_nhds (gt_mem_nhds one_pos)
  filter_upwards [h4, self_mem_nhdsWithin] with t ht1 ht
  have ht : 0 < t := ht
  obtain ⟨h1, h2⟩ := poisson_gaussian_lattice_cos L ht u
  rw [h2, h1.tsum_eq_add_tsum_ite 0, hE]
  have hs : 1 ≤ t⁻¹ := (one_le_inv₀ ht).2 ht1.le
  have h5 := abs_tsum_le (δ := δ) (f := fun y : dualLattice L => if y = 0 then 0 else
      Real.exp (-Real.pi * ‖(y : E)‖ ^ 2 / t) * Real.cos (2 * Real.pi * ⟪(y : E), u⟫)) hs h
      (fun y => ?_) (fun y hy => hq y ?_)
  · generalize (∑' y : dualLattice L, if y = 0 then 0 else
      Real.exp (-Real.pi * ‖(y : E)‖ ^ 2 / t) * Real.cos (2 * Real.pi * ⟪(y : E), u⟫)) = S at h5 ⊢
    rw [← hC] at h5
    have h6 : t ^ (-(((2 : ℕ) : ℝ) / 2)) = t⁻¹ := by
      rw [← Real.rpow_neg_one]; norm_num
    rw [h6]
    have h7 : (ZLattice.covolume L)⁻¹ * t⁻¹ * (Real.exp (-Real.pi * ‖((0 : dualLattice L) : E)‖ ^ 2 / t) *
        Real.cos (2 * Real.pi * ⟪((0 : dualLattice L) : E), u⟫) + S) - 1 / (t * ZLattice.covolume L)
        = (ZLattice.covolume L)⁻¹ * t⁻¹ * S := by
      simp only [ZeroMemClass.coe_zero, norm_zero, inner_zero_left]
      simp
      ring
    rw [h7, Real.norm_of_nonneg (Real.exp_pos _).le, Real.norm_eq_abs, abs_mul,
      abs_of_pos (by positivity)]
    have h8 : t⁻¹ ≤ 2 / δ * Real.exp (δ / 2 * t⁻¹) := by
      have := Real.add_one_le_exp (δ / 2 * t⁻¹)
      rw [div_mul_eq_mul_div, le_div_iff₀ hδ]
      nlinarith
    calc (ZLattice.covolume L)⁻¹ * t⁻¹ * |S|
        ≤ (ZLattice.covolume L)⁻¹ * (2 / δ * Real.exp (δ / 2 * t⁻¹)) * (C * Real.exp (-δ * t⁻¹)) := by
          gcongr
      _ = (ZLattice.covolume L)⁻¹ * (2 / δ) * C * (Real.exp (δ / 2 * t⁻¹) * Real.exp (-δ * t⁻¹)) := by
          ring
      _ = (ZLattice.covolume L)⁻¹ * (2 / δ) * C * Real.exp (-(δ / 2) / t) := by
          rw [← Real.exp_add]; congr 2; ring
  · split_ifs
    · rw [abs_zero]; positivity
    · rw [abs_mul, abs_of_pos (Real.exp_pos _)]
      refine (mul_le_of_le_one_right (Real.exp_pos _).le (Real.abs_cos_le_one _)).trans ?_
      apply le_of_eq; congr 1; ring
  · have hy0 : y ≠ 0 := fun h0 => hy (if_pos h0)
    have : 0 < ‖(y : E)‖ := norm_pos_iff.2 (by simpa using hy0)
    have := Real.pi_pos
    positivity

end Lattice

theorem covolume_lattice (L : PeriodPair) :
    ZLattice.covolume L.lattice = |(starRingEnd ℂ L.ω₁ * L.ω₂).im| := by
  rw [ZLattice.covolume_eq_det_mul_measureReal _ _ L.latticeBasis Complex.orthonormalBasisOneI.toBasis,
    MeasureTheory.measureReal_congr (ZSpan.fundamentalDomain_ae_parallelepiped _ _),
    MeasureTheory.Measure.real, OrthonormalBasis.coe_toBasis,
    Complex.orthonormalBasisOneI.volume_parallelepiped, ENNReal.toReal_one, _root_.mul_one]
  congr 1
  rw [Module.Basis.det_apply, Matrix.det_fin_two]
  simp [Module.Basis.toMatrix_apply]
  ring

theorem theta_asymptotics : ∀ (w₁ w₂ x₀ : ℂ), (starRingEnd ℂ w₁ * w₂).im ≠ 0 → (∀ m n : ℤ, x₀ + m * w₁ + n * w₂ ≠ 0) → ∃ c : ℝ, 0 < c ∧ (fun t : ℝ => ∑' p : ℤ × ℤ, Real.exp (-Real.pi * t * ‖x₀ + p.1 * w₁ + p.2 * w₂‖ ^ 2)) =O[atTop] (fun t => Real.exp (-c * t)) ∧ (fun t : ℝ => (∑' p : ℤ × ℤ, Real.exp (-Real.pi * t * ‖x₀ + p.1 * w₁ + p.2 * w₂‖ ^ 2)) - 1 / (t * |(starRingEnd ℂ w₁ * w₂).im|)) =O[nhdsWithin 0 (Set.Ioi 0)] (fun t => Real.exp (-c / t)) := by
  intro w₁ w₂ x₀ hw hx
  let L : PeriodPair := ⟨w₁, w₂, by
    rw [LinearIndependent.pair_iff]
    intro s t e
    have e1 := congrArg Complex.re e
    have e2 := congrArg Complex.im e
    simp at e1 e2 hw
    constructor
    · apply mul_left_cancel₀ hw
      linear_combination w₂.im * e1 - w₂.re * e2
    · apply mul_left_cancel₀ hw
      linear_combination w₁.re * e2 - w₁.im * e1⟩
  have hsum : ∀ t : ℝ, ∑' p : ℤ × ℤ, Real.exp (-Real.pi * t * ‖x₀ + p.1 * w₁ + p.2 * w₂‖ ^ 2) =
      ∑' x : L.lattice, Real.exp (-Real.pi * t * ‖(x : ℂ) + x₀‖ ^ 2) := by
    intro t
    rw [← L.latticeEquivProd.symm.toEquiv.tsum_eq]
    refine tsum_congr fun p => ?_
    have := L.latticeEquiv_symm_apply p
    have e : ((L.latticeEquivProd.symm.toEquiv p : L.lattice) : ℂ) + x₀
        = x₀ + p.1 * w₁ + p.2 * w₂ := by
      change (L.latticeEquivProd.symm p).1 + x₀ = _
      rw [this]
      ring
    rw [e]
  have hu : ∀ x : L.lattice, (x : ℂ) + x₀ ≠ 0 := by
    intro x h
    obtain ⟨m, n, hmn⟩ := PeriodPair.mem_lattice.1 x.2
    apply hx m n
    rw [← h, ← hmn]
    ring
  obtain ⟨c₁, hc₁, h₁⟩ := atTop_bound L.lattice x₀ hu
  obtain ⟨c₂, hc₂, h₂⟩ := zero_bound L.lattice Complex.finrank_real_complex x₀
  rw [covolume_lattice] at h₂
  simp only [hsum]
  refine ⟨min c₁ c₂, lt_min hc₁ hc₂, h₁.trans (IsBigO.of_bound' ?_), h₂.trans (IsBigO.of_bound' ?_)⟩
  · filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
    rw [Real.norm_of_nonneg (Real.exp_pos _).le, Real.norm_of_nonneg (Real.exp_pos _).le,
      Real.exp_le_exp]
    nlinarith [min_le_left c₁ c₂]
  · filter_upwards [self_mem_nhdsWithin] with t ht
    have ht : 0 < t := ht
    rw [Real.norm_of_nonneg (Real.exp_pos _).le, Real.norm_of_nonneg (Real.exp_pos _).le,
      Real.exp_le_exp]
    gcongr
    exact min_le_right _ _

end GlobalTheory.PlaneTheta
