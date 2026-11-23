import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.OneMemNbh
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DiscreteBranchingUpq
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.L2OpNormConjTransposeExpMulSignMulExpSubLe

noncomputable section

namespace GlobalTheory.MatLog

open NormedSpace

def lc (k : ℕ) : ℂ := (-1) ^ k / (k + 1)

theorem norm_lc_le (k : ℕ) : ‖lc k‖ ≤ 1 := by
  have h : ‖((k : ℂ) + 1)‖ = (k : ℝ) + 1 := by
    rw [show ((k : ℂ) + 1) = ((k + 1 : ℕ) : ℂ) by push_cast; ring, Complex.norm_natCast]; push_cast; ring
  rw [lc, norm_div, norm_pow, norm_neg, norm_one, one_pow, h]
  rw [div_le_one (by positivity)]; linarith [(Nat.cast_nonneg k : (0:ℝ) ≤ k)]

theorem lc_mul (k : ℕ) : lc k * ((k : ℂ) + 1) = (-1) ^ k := by
  have : ((k : ℂ) + 1) ≠ 0 := by
    rw [show ((k : ℂ) + 1) = ((k + 1 : ℕ) : ℂ) by push_cast; ring]; exact_mod_cast Nat.succ_ne_zero k
  rw [lc, div_mul_cancel₀ _ this]

section Gen

variable {A : Type*} [NormedRing A] [NormedAlgebra ℂ A] [CompleteSpace A]

def logS (y : A) : A := ∑' k : ℕ, lc k • y ^ (k + 1)

theorem norm_term_le (y : A) (k : ℕ) : ‖lc k • y ^ (k + 1)‖ ≤ ‖y‖ * ‖y‖ ^ k := by
  rw [norm_smul, ← pow_succ']
  calc ‖lc k‖ * ‖y ^ (k + 1)‖ ≤ 1 * ‖y‖ ^ (k + 1) :=
        mul_le_mul (norm_lc_le k) (norm_pow_le' y (Nat.succ_pos k)) (norm_nonneg _) zero_le_one
    _ = ‖y‖ ^ (k + 1) := one_mul _

theorem summable_logS {y : A} (hy : ‖y‖ < 1) : Summable fun k : ℕ => lc k • y ^ (k + 1) :=
  Summable.of_norm_bounded ((summable_geometric_of_lt_one (norm_nonneg y) hy).mul_left ‖y‖) (norm_term_le y)

theorem norm_logS_le {y : A} (hy : ‖y‖ < 1) : ‖logS y‖ ≤ ‖y‖ * (1 - ‖y‖)⁻¹ :=
  tsum_of_norm_bounded ((hasSum_geometric_of_lt_one (norm_nonneg y) hy).mul_left ‖y‖) (norm_term_le y)

theorem norm_logS_le' {y : A} (hy : ‖y‖ ≤ 1 / 4) : ‖logS y‖ ≤ 4 / 3 * ‖y‖ := by
  have h0 := norm_nonneg y
  refine (norm_logS_le (by linarith)).trans ?_
  have h1 : (1 - ‖y‖)⁻¹ ≤ 4 / 3 := by
    rw [inv_le_comm₀ (by linarith) (by norm_num)]; linarith
  nlinarith

end Gen

end GlobalTheory.MatLog

namespace GlobalTheory.MatLog

open NormedSpace

section Comm

variable {A : Type*} [NormedCommRing A] [NormedAlgebra ℂ A] [CompleteSpace A]

theorem exp_add_comm (x y : A) : exp (x + y) = exp x * exp y :=
  exp_add_of_commute_of_mem_ball (𝕂 := ℂ) (Commute.all x y) ((expSeries_radius_eq_top ℂ A).symm ▸ edist_lt_top _ _)
    ((expSeries_radius_eq_top ℂ A).symm ▸ edist_lt_top _ _)

theorem exp_logS_comm (y : A) (hy : ‖y‖ ≤ 1 / 4) : exp (logS y) = 1 + y := by
  have hy0 := norm_nonneg y
  set s : Set ℂ := Metric.ball 0 2 with hs
  let g : ℕ → ℂ → A := fun k t => (lc k * t ^ (k + 1)) • y ^ (k + 1)
  let g' : ℕ → ℂ → A := fun k t => ((-t) ^ k) • y ^ (k + 1)
  have hg : ∀ k t, t ∈ s → HasDerivAt (g k) (g' k t) t := by
    intro k t _
    refine (((hasDerivAt_pow (k + 1) t).const_mul (lc k)).smul_const (y ^ (k + 1))).congr_deriv ?_
    simp only [g', Nat.add_sub_cancel]
    congr 1
    push_cast
    rw [← mul_assoc, lc_mul, ← neg_pow]
  have hu : Summable fun k : ℕ => (1 / 2 : ℝ) ^ k := summable_geometric_of_lt_one (by norm_num) (by norm_num)
  have hg' : ∀ k t, t ∈ s → ‖g' k t‖ ≤ (1 / 2 : ℝ) ^ k := by
    intro k t ht
    have ht' : ‖t‖ ≤ 2 := by
      have := Metric.mem_ball.1 ht; rw [dist_zero_right] at this; linarith
    calc ‖g' k t‖ = ‖t‖ ^ k * ‖y ^ (k + 1)‖ := by simp [g', norm_smul, norm_neg, norm_pow]
      _ ≤ 2 ^ k * (1 / 4) ^ (k + 1) := by
          gcongr
          exact (norm_pow_le' y (Nat.succ_pos k)).trans (pow_le_pow_left₀ hy0 hy _)
      _ = (1 / 2) ^ k * (1 / 4) := by rw [pow_succ, ← mul_assoc, ← mul_pow]; norm_num
      _ ≤ (1 / 2) ^ k := by
          have : (0 : ℝ) ≤ (1 / 2) ^ k := by positivity
          linarith
  have h0s : (0 : ℂ) ∈ s := Metric.mem_ball_self (by norm_num)
  have hg0 : Summable fun k => g k 0 := by
    have : (fun k => g k 0) = fun _ => 0 := by funext k; simp [g]
    rw [this]; exact summable_zero
  have hl : ∀ t ∈ s, HasDerivAt (fun z => ∑' k, g k z) (∑' k, g' k t) t := fun t ht =>
    hasDerivAt_tsum_of_isPreconnected hu Metric.isOpen_ball (convex_ball _ _).isPreconnected hg hg' h0s hg0 ht
  have hmul : ∀ t ∈ s, (∑' k, g' k t) * (1 + t • y) = y := by
    intro t ht
    have ht' : ‖t‖ < 2 := by have := Metric.mem_ball.1 ht; rwa [dist_zero_right] at this
    have hx : ‖-(t • y)‖ < 1 := by
      rw [norm_neg, norm_smul]; nlinarith
    have hsum : (∑' k, g' k t) = (∑' k : ℕ, (-(t • y)) ^ k) * y := by
      rw [← (summable_geometric_of_norm_lt_one hx).tsum_mul_right]
      congr 1; funext k
      simp only [g', ← neg_smul, smul_pow, smul_mul_assoc, pow_succ]
    rw [hsum, mul_right_comm, show (1 : A) + t • y = 1 - -(t • y) by abel, geom_series_mul_neg _ hx]
    simp
  let G : ℂ → A := fun t => exp (-(∑' k, g k t)) * (1 + t • y)
  have hG : ∀ t ∈ s, HasDerivAt G 0 t := by
    intro t ht
    have h1 : HasDerivAt (fun z => exp (-(∑' k, g k z)))
        (exp (-(∑' k, g k t)) * (-(∑' k, g' k t))) t := by
      have := (hasFDerivAt_exp (𝕂 := ℂ) (x := -(∑' k, g k t))).comp_hasDerivAt t (hl t ht).neg
      refine this.congr_deriv ?_
      simp
    have h2 : HasDerivAt (fun z : ℂ => (1 : A) + z • y) ((1 : ℂ) • y) t :=
      ((hasDerivAt_id t).smul_const y).const_add 1
    have h3 := (h1.mul h2).congr_deriv (show _ = (0 : A) by
      rw [one_smul, mul_assoc, neg_mul, hmul t ht]; ring)
    exact h3
  have hconst := Metric.isOpen_ball.is_const_of_deriv_eq_zero (𝕜 := ℂ) (f := G)
    (convex_ball _ _).isPreconnected (fun t ht => (hG t ht).differentiableAt.differentiableWithinAt)
    (fun t ht => (hG t ht).deriv) (show (1 : ℂ) ∈ s from by rw [hs, Metric.mem_ball, dist_zero_right]; norm_num) h0s
  have e1 : (∑' k, g k 1) = logS y := by simp [g, logS]
  have e0 : (∑' k, g k 0) = 0 := by simp [g]
  simp only [G, e1, e0, neg_zero, NormedSpace.exp_zero, zero_smul, add_zero, one_mul, one_smul] at hconst
  calc exp (logS y) = exp (logS y) * (exp (-logS y) * (1 + y)) := by rw [hconst, mul_one]
    _ = 1 + y := by rw [← mul_assoc, ← exp_add_comm, add_neg_cancel, NormedSpace.exp_zero, one_mul]

end Comm

end GlobalTheory.MatLog

namespace GlobalTheory.MatLog

open NormedSpace

theorem eq_zero_of_exp_eq_one {A : Type*} [NormedRing A] [NormedAlgebra ℂ A] [CompleteSpace A] {z : A}
    (hz : ‖z‖ ≤ 2 / 3) (he : exp z = 1) : z = 0 := by
  have h1 := GlobalTheory.norm_exp_sub_one_sub_le z
  rw [he, sub_self, zero_sub, norm_neg] at h1
  have h0 := norm_nonneg z
  have h2 := Real.abs_exp_sub_one_sub_id_le (x := ‖z‖) (by rw [abs_of_nonneg h0]; linarith)
  have h3 := le_abs_self (Real.exp ‖z‖ - 1 - ‖z‖)
  have : ‖z‖ = 0 := by nlinarith
  exact norm_eq_zero.1 this

theorem logS_inv {A : Type*} [NormedCommRing A] [NormedAlgebra ℂ A] [CompleteSpace A] (y w : A) (hy : ‖y‖ ≤ 1 / 4)
    (hw' : ‖w - 1‖ ≤ 1 / 4) (hw : w * (1 + y) = 1) : logS (w - 1) = -logS y := by
  have e3 : exp (logS y + logS (w - 1)) = 1 := by
    rw [exp_add_comm, exp_logS_comm y hy, exp_logS_comm _ hw', add_sub_cancel, mul_comm, hw]
  have hz : ‖logS y + logS (w - 1)‖ ≤ 2 / 3 := by
    have a1 := norm_logS_le' hy
    have a2 := norm_logS_le' hw'
    linarith [norm_add_le (logS y) (logS (w - 1))]
  rw [eq_neg_iff_add_eq_zero, add_comm]; exact eq_zero_of_exp_eq_one hz e3

end GlobalTheory.MatLog

namespace GlobalTheory.MatLog

open NormedSpace

theorem map_logS {A B : Type*} [NormedRing A] [NormedAlgebra ℂ A] [CompleteSpace A] [NormedRing B] [NormedAlgebra ℂ B]
    [CompleteSpace B] (φ : A →ₐ[ℂ] B) (hφ : Continuous φ) {y : A} (hy : ‖y‖ < 1) : φ (logS y) = logS (φ y) := by
  rw [logS, logS, ← ((summable_logS hy).hasSum.map φ hφ).tsum_eq]
  congr 1; funext k
  simp [map_smul, map_pow]

theorem star_lc (k : ℕ) : star (lc k) = lc k := by
  simp [lc, map_div₀, map_pow, map_neg, map_one]

end GlobalTheory.MatLog

noncomputable section

open MeasureTheory Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Ell
open scoped InnerProductSpace
open GlobalTheory.SepReal

namespace GlobalTheory.SepReal.LogNearPf

open NormedSpace GlobalTheory.MatLog

theorem hsn_J_conj {m : ℕ} (ε : Fin m → Bool) (A : Mat m) : hsn (Jm ε * Aᴴ * Jm ε) = hsn A := by
  have hd : ∀ a, ‖(if ε a = true then (1 : ℂ) else -1)‖ = 1 := fun a => by split_ifs <;> simp
  unfold hsn; congr 1
  simp only [Formalism.REAL.Jm, Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.conjTranspose_apply, norm_mul, hd, one_mul,
    mul_one, norm_star]
  exact Finset.sum_comm

theorem J_pow {m : ℕ} (ε : Fin m → Bool) (C : Mat m) (n : ℕ) : (Jm ε * C * Jm ε) ^ n = Jm ε * C ^ n * Jm ε := by
  have hJJ : Jm ε * Jm ε = 1 := Formalism.REAL.Jm_mul_self ε
  induction n with
  | zero => simp [hJJ]
  | succ n ih =>
    rw [pow_succ, ih, pow_succ]
    calc Jm ε * C ^ n * Jm ε * (Jm ε * C * Jm ε) = Jm ε * C ^ n * (Jm ε * Jm ε) * C * Jm ε := by noncomm_ring
      _ = _ := by rw [hJJ, mul_one, mul_assoc (Jm ε) (C ^ n) C]

section Frob

open scoped Matrix.Norms.Frobenius

theorem hsn_eq_norm {m : ℕ} (A : Mat m) : hsn A = ‖A‖ := by
  rw [hsn, Matrix.frobenius_norm_def, Real.sqrt_eq_rpow]
  simp_rw [Real.rpow_two]

theorem logS_J_conj {m : ℕ} (ε : Fin m → Bool) {Y : Mat m} (hY : ‖Y‖ < 1) :
    Jm ε * (logS Y)ᴴ * Jm ε = logS (Jm ε * Yᴴ * Jm ε) := by
  let φ : Mat m →+ Mat m :=
    { toFun := fun A => Jm ε * Aᴴ * Jm ε
      map_zero' := by simp
      map_add' := fun A B => by simp [Matrix.conjTranspose_add, Matrix.mul_add, Matrix.add_mul] }
  have hφ : Continuous φ := AddMonoidHomClass.continuous_of_bound φ 1 fun A => by
    show ‖Jm ε * Aᴴ * Jm ε‖ ≤ 1 * ‖A‖
    rw [← hsn_eq_norm, ← hsn_eq_norm, hsn_J_conj, one_mul]
  have h := ((summable_logS hY).hasSum.map φ hφ).tsum_eq
  rw [logS, logS]
  refine h.symm.trans ?_
  congr 1; funext k
  show Jm ε * (lc k • Y ^ (k + 1))ᴴ * Jm ε = lc k • (Jm ε * Yᴴ * Jm ε) ^ (k + 1)
  rw [Matrix.conjTranspose_smul, star_lc, Matrix.conjTranspose_pow, J_pow, Matrix.mul_smul, Matrix.smul_mul]

end Frob

end GlobalTheory.SepReal.LogNearPf

namespace GlobalTheory.SepReal

open NormedSpace GlobalTheory.MatLog GlobalTheory.SepReal.LogNearPf

section Main

open scoped Matrix.Norms.Frobenius

theorem logNear_holds : LogNear := by
  intro m ε δ hδ g hg hgd
  have hJJ : Jm ε * Jm ε = 1 := Formalism.REAL.Jm_mul_self ε
  have hgu : gᴴ * Jm ε * g = Jm ε := hg
  have hleft : Jm ε * gᴴ * Jm ε * g = 1 := by
    calc Jm ε * gᴴ * Jm ε * g = Jm ε * (gᴴ * Jm ε * g) := by noncomm_ring
      _ = 1 := by rw [hgu, hJJ]
  have hginv : g⁻¹ = Jm ε * gᴴ * Jm ε := Matrix.inv_eq_left_inv hleft
  set Y : Mat m := g - 1 with hYdef
  have hgY : g = 1 + Y := by rw [hYdef]; abel
  have hYn : ‖Y‖ ≤ δ := by rw [← hsn_eq_norm]; exact hgd
  have hY4 : ‖Y‖ ≤ 1 / 4 := hYn.trans hδ
  let S : Subalgebra ℂ (Mat m) := Algebra.elemental ℂ Y
  letI : NormedCommRing S := { SubringClass.toNormedRing S with mul_comm := mul_comm }
  letI : NormedAlgebra ℂ S := inferInstance
  haveI : CompleteSpace S := inferInstance
  let y : S := ⟨Y, Algebra.elemental.self_mem ℂ Y⟩
  have hy : ‖y‖ = ‖Y‖ := rfl
  have hy1 : ‖-y‖ < 1 := (norm_neg y).trans_lt (hy.trans_lt (by linarith))
  let u : Sˣ := Units.oneSub (-y) hy1
  let w : S := ↑u⁻¹
  have hu : (u : S) = 1 + y := by simp [u, Units.oneSub]
  have hw : w * (1 + y) = 1 := by rw [← hu]; exact u.inv_mul
  have hwg : (w : Mat m) * g = 1 := by
    have := congrArg Subtype.val hw
    rw [hgY]; simpa using this
  have hwv : (w : Mat m) = g⁻¹ := (Matrix.inv_eq_left_inv hwg).symm
  let y' : S := w - 1
  have hy'v : (y' : Mat m) = Jm ε * Yᴴ * Jm ε := by
    show (w : Mat m) - 1 = _
    rw [hwv, hginv, hYdef, Matrix.conjTranspose_sub, Matrix.conjTranspose_one, Matrix.mul_sub, Matrix.sub_mul, mul_one, hJJ]
  have hy' : ‖y'‖ = ‖Y‖ := by
    show ‖(y' : Mat m)‖ = ‖Y‖
    rw [hy'v, ← hsn_eq_norm, ← hsn_eq_norm, hsn_J_conj]
  have hy4 : ‖y‖ ≤ 1 / 4 := by rw [hy]; exact hY4
  have hy'4 : ‖y'‖ ≤ 1 / 4 := by rw [hy']; exact hY4
  have e1 := exp_logS_comm y hy4
  have hneg : logS y' = -logS y := logS_inv y w hy4 hy'4 hw
  have hval : Continuous S.val := continuous_subtype_val
  have m1 : S.val (logS y) = logS Y := map_logS S.val hval (by linarith)
  have m2 : S.val (logS y') = logS (Jm ε * Yᴴ * Jm ε) := by
    rw [map_logS S.val hval (by linarith)]; exact congrArg logS hy'v
  refine ⟨logS Y, ?_, ?_, ?_⟩
  · show (logS Y)ᴴ * Jm ε + Jm ε * logS Y = 0
    have hc : Jm ε * (logS Y)ᴴ * Jm ε = -logS Y := by
      rw [logS_J_conj ε (by linarith), ← m2, hneg, map_neg, m1]
    calc (logS Y)ᴴ * Jm ε + Jm ε * logS Y = Jm ε * (Jm ε * (logS Y)ᴴ * Jm ε) + Jm ε * logS Y := by
          rw [← mul_assoc, ← mul_assoc, hJJ, one_mul]
      _ = 0 := by rw [hc, mul_neg, neg_add_cancel]
  · rw [hsn_eq_norm, ← m1]
    have := norm_logS_le' hy4
    show ‖logS y‖ ≤ 2 * δ
    rw [hy] at this; linarith [norm_nonneg Y]
  · have := map_exp_of_mem_ball (𝕂 := ℂ) S.val hval (logS y) ((expSeries_radius_eq_top ℂ S).symm ▸ edist_lt_top _ _)
    rw [m1] at this
    have h2 : S.val (1 + y) = 1 + Y := by rw [map_add, map_one]; rfl
    rw [hgY, ← h2]
    exact this.symm.trans (congrArg S.val e1)

end Main

end GlobalTheory.SepReal
