import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.CompletedLStripBounds
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormWt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaussZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousTerm
open NumberField MeasureTheory

noncomputable section

namespace GlobalTheory.HeckeShift

theorem hmon_mul_unit {ζ : ℂ} (hζ : ‖ζ‖ = 1) (n : ℤ) (v : ℂ) :
    GlobalTheory.HeckeTheta.hmon n (ζ * v) = ζ ^ (-n) * GlobalTheory.HeckeTheta.hmon n v := by
  have hζ0 : ζ ≠ 0 := by rintro rfl; simp at hζ
  unfold GlobalTheory.HeckeTheta.hmon
  split_ifs with h
  · have hc : starRingEnd ℂ ζ = ζ⁻¹ := by
      rw [Complex.inv_def, Complex.normSq_eq_norm_sq, hζ]; simp
    rw [map_mul, mul_pow, hc, inv_pow, ← zpow_natCast, ← zpow_neg, Int.toNat_of_nonneg h]
  · rw [mul_pow, ← zpow_natCast ζ, Int.toNat_of_nonneg (by omega)]

theorem factor_shift (n : ℤ) (y : ℝ) {z : ℂ} (hz : z ≠ 0) (w : ℂ) :
    GlobalTheory.HeckeTheta.hmon n ((Real.exp (y / 2) : ℂ) * (z * w)) *
                 Complex.exp ((-2 * Real.pi * ‖(Real.exp (y / 2) : ℂ) * (z * w)‖ ^ 2 : ℝ) : ℂ) =
      (z / ((‖z‖ : ℝ) : ℂ)) ^ (-n) *
        (GlobalTheory.HeckeTheta.hmon n ((Real.exp ((y + Real.log (‖z‖ ^ 2)) / 2) : ℂ) * w) *
          Complex.exp ((-2 * Real.pi * ‖(Real.exp ((y + Real.log (‖z‖ ^ 2)) / 2) : ℂ) * w‖ ^ 2 : ℝ) : ℂ)) := by
  have hn0 : (0 : ℝ) < ‖z‖ := norm_pos_iff.2 hz
  have hE : Real.exp ((y + Real.log (‖z‖ ^ 2)) / 2) = Real.exp (y / 2) * ‖z‖ := by
    rw [Real.log_pow, add_div, Real.exp_add]
    congr 1
    rw [show ((2 : ℕ) : ℝ) * Real.log ‖z‖ / 2 = Real.log ‖z‖ by push_cast; ring, Real.exp_log hn0]
  have hzc : ((‖z‖ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hn0.ne'
  have hζ : ‖z / ((‖z‖ : ℝ) : ℂ)‖ = 1 := by
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_norm, div_self hn0.ne']
  have hv : (Real.exp (y / 2) : ℂ) * (z * w) =
      (z / ((‖z‖ : ℝ) : ℂ)) * ((Real.exp ((y + Real.log (‖z‖ ^ 2)) / 2) : ℂ) * w) := by
    rw [hE]; push_cast; field_simp
  rw [hv, hmon_mul_unit hζ, norm_mul, hζ, one_mul, mul_assoc]

theorem sum_ulog {K : Type} [Field K] [NumberField K] [IsTotallyComplex K] {I : Type} [Fintype I]
    (φ : I → K →+* ℂ) (hφ : GlobalTheory.CMVal.IsCMType φ) (u : (𝓞 K)ˣ) : ∑ i, GlobalTheory.HeckeTheta.ulog φ u i = 0 := by
  have hbij : Function.Bijective (fun i => InfinitePlace.mk (φ i)) := by
    constructor
    · intro i j hij
      obtain ⟨k, _, hk⟩ := hφ (φ i)
      have hi := hk i (Or.inl rfl)
      rcases InfinitePlace.mk_eq_iff.1 hij with h | h
      · rw [hi, hk j (Or.inl h)]
      · rw [hi, hk j (Or.inr (by rw [← h]; ext x; simp [ComplexEmbedding.conjugate_coe_eq]))]
    · intro w
      obtain ⟨k, hk, _⟩ := hφ w.embedding
      refine ⟨k, ?_⟩
      rcases hk with h | h
      · simp only; rw [← h, InfinitePlace.mk_embedding]
      · simp only; rw [← InfinitePlace.mk_conjugate_eq (φ k), ← h, InfinitePlace.mk_embedding]
  have h0 := NumberField.Units.sum_mult_mul_log u
  rw [← (Equiv.ofBijective _ hbij).sum_comp] at h0
  rw [← h0]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hm : (InfinitePlace.mk (φ i)).mult = 2 :=
    InfinitePlace.mult_isComplex ⟨_, IsTotallyComplex.isComplex _⟩
  simp only [Equiv.ofBijective_apply, InfinitePlace.apply, hm, GlobalTheory.HeckeTheta.ulog, Real.log_pow]

end GlobalTheory.HeckeShift

theorem GlobalTheory.HeckeShift.term_unit_mul : ∀ (K : Type) [Field K] [NumberField K] [NumberField.IsTotallyComplex K] (I : Type) [Fintype I]
    (φ : I → K →+* ℂ), GlobalTheory.CMVal.IsCMType φ → ∀ (n : I → ℤ) (s : ℂ) (u : (𝓞 K)ˣ) (α : K) (y : I → ℝ),
    GlobalTheory.HeckeMellin.term n s (GlobalTheory.HeckeTheta.emb φ (((u : 𝓞 K) : K) * α)) y =
      GlobalTheory.HeckeStrip.wt φ n ((u : 𝓞 K) : K) *
        GlobalTheory.HeckeMellin.term n s (GlobalTheory.HeckeTheta.emb φ α) (y + GlobalTheory.HeckeTheta.ulog φ u) := by
  intro K _ _ _ I _ φ hφ n s u α y
  have hsum : (∑ i, (y + GlobalTheory.HeckeTheta.ulog φ u) i) = ∑ i, y i := by
    simp only [Pi.add_apply, Finset.sum_add_distrib, GlobalTheory.HeckeShift.sum_ulog φ hφ u, add_zero]
  have hu0 : ((u : 𝓞 K) : K) ≠ 0 := by
    intro h
    exact (Units.ne_zero u) (by exact_mod_cast h)
  unfold GlobalTheory.HeckeMellin.term
  rw [hsum, ← mul_assoc]
  congr 1
  unfold GlobalTheory.HeckeTheta.gauss GlobalTheory.HeckeStrip.wt
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  simp only [GlobalTheory.HeckeTheta.dil, GlobalTheory.HeckeTheta.emb, GlobalTheory.HeckeTheta.ulog, Pi.add_apply, map_mul]
  exact GlobalTheory.HeckeShift.factor_shift (n i) (y i) ((map_ne_zero _).2 hu0) (φ i α)
