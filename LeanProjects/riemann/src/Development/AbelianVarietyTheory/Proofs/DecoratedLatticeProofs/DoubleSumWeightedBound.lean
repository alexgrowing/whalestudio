import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsQuasiFam
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.RealSizeNonneg
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.UnifModGrowthOfIsUnifModerate
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ThetaAbsoluteSum
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.TransvectionAction
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.WeilDatumExistence
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf
open scoped ComplexOrder ENNReal NNReal ContDiff
noncomputable section
variable {D : D7}

namespace GlobalTheory.Unf.DoubleSum

theorem realSize_nsmul (θ : InfFam D) {m k : ℕ} (n : ℕ) (x : Mx D m k) :
    realSize θ (n • x) = n * realSize θ x := by
  unfold realSize
  rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun τ _ => ?_
  rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun j _ => ?_
  have : compAt θ τ (n • x) i j = (n : ℂ) * compAt θ τ x i j := by
    simp only [compAt, Matrix.map_apply, Matrix.smul_apply, nsmul_eq_mul, map_mul, map_natCast]
  rw [this, norm_mul, Complex.norm_natCast]

theorem pointwise (θ : InfFam D) {a b c e : ℕ} (K : Set (Mx D a b)) (K' : Set (Mx D c e)) (N N' n : ℕ) (hn : 0 < n)
    (B : ℝ≥0∞) (F : ratMx D a b → ratMx D c e → ℝ≥0∞)
    (hF : ∀ x y, F x y ≠ 0 → InBox K (n • (x : Mx D a b)) ∧ InBox K' (n • (y : Mx D c e)))
    (h1 : ∀ x y, F x y * ENNReal.ofReal ((1 + realSize θ (x : Mx D a b)) ^ (N + N')) ≤ B)
    (h2 : ∀ x y, F x y * ENNReal.ofReal ((1 + realSize θ (y : Mx D c e)) ^ (N + N')) ≤ B) (x : ratMx D a b) (y : ratMx D c e) :
    F x y ≤ (n : ℝ≥0∞) ^ (N + N') * B * (ENNReal.ofReal (maj θ K N (n • (x : Mx D a b))) *
      ENNReal.ofReal (maj θ K' N' (n • (y : Mx D c e)))) := by
  by_cases h0 : F x y = 0
  · rw [h0]; exact bot_le
  obtain ⟨hx, hy⟩ := hF x y h0
  set s := 1 + realSize θ (x : Mx D a b) with hs
  set t := 1 + realSize θ (y : Mx D c e) with ht
  have s1 : 1 ≤ s := by have := realSize_nonneg θ (x : Mx D a b); linarith
  have t1 : 1 ≤ t := by have := realSize_nonneg θ (y : Mx D c e); linarith
  set M := max s t with hM
  have M1 : 1 ≤ M := le_trans s1 (le_max_left _ _)
  have Mpos : 0 < M := by linarith
  have hFM : F x y * ENNReal.ofReal (M ^ (N + N')) ≤ B := by
    rcases le_total s t with h | h
    · rw [hM, max_eq_right h]; exact h2 x y
    · rw [hM, max_eq_left h]; exact h1 x y
  have hMp : 0 < M ^ (N + N') := pow_pos Mpos _
  have hF' : F x y ≤ B * ENNReal.ofReal ((M ^ (N + N'))⁻¹) := by
    rw [ENNReal.ofReal_inv_of_pos hMp, ← div_eq_mul_inv]
    exact ENNReal.le_div_iff_mul_le (Or.inl (by simpa using hMp)) (Or.inl ENNReal.ofReal_ne_top) |>.2 hFM
  refine hF'.trans ?_
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hnx : 1 + realSize θ (n • (x : Mx D a b)) ≤ n * M := by
    rw [realSize_nsmul]
    have := realSize_nonneg θ (x : Mx D a b)
    calc 1 + n * realSize θ (x : Mx D a b) ≤ n * s := by rw [hs]; nlinarith
      _ ≤ n * M := by gcongr; exact le_max_left _ _
  have hny : 1 + realSize θ (n • (y : Mx D c e)) ≤ n * M := by
    rw [realSize_nsmul]
    have := realSize_nonneg θ (y : Mx D c e)
    calc 1 + n * realSize θ (y : Mx D c e) ≤ n * t := by rw [ht]; nlinarith
      _ ≤ n * M := by gcongr; exact le_max_right _ _
  have px : 0 < 1 + realSize θ (n • (x : Mx D a b)) := by have := realSize_nonneg θ (n • (x : Mx D a b)); linarith
  have py : 0 < 1 + realSize θ (n • (y : Mx D c e)) := by have := realSize_nonneg θ (n • (y : Mx D c e)); linarith
  have key : (M ^ (N + N'))⁻¹ ≤ (n : ℝ) ^ (N + N') * (((1 + realSize θ (n • (x : Mx D a b))) ^ N)⁻¹ *
      ((1 + realSize θ (n • (y : Mx D c e))) ^ N')⁻¹) := by
    have e1 : ((n * M) ^ N)⁻¹ ≤ ((1 + realSize θ (n • (x : Mx D a b))) ^ N)⁻¹ :=
      inv_anti₀ (pow_pos px _) (pow_le_pow_left₀ px.le hnx _)
    have e2 : ((n * M) ^ N')⁻¹ ≤ ((1 + realSize θ (n • (y : Mx D c e))) ^ N')⁻¹ :=
      inv_anti₀ (pow_pos py _) (pow_le_pow_left₀ py.le hny _)
    have npos : (0 : ℝ) < n := by linarith
    calc (M ^ (N + N'))⁻¹ = (n : ℝ) ^ (N + N') * (((n * M) ^ N)⁻¹ * ((n * M) ^ N')⁻¹) := by
          rw [mul_pow, mul_pow, pow_add, pow_add]; field_simp
      _ ≤ _ := by gcongr
  unfold maj
  rw [if_pos hx, if_pos hy, mul_assoc, ← ENNReal.ofReal_mul (by positivity),
    show (n : ℝ≥0∞) ^ (N + N') = ENNReal.ofReal ((n : ℝ) ^ (N + N')) by
      rw [ENNReal.ofReal_pow (Nat.cast_nonneg _), ENNReal.ofReal_natCast],
    mul_left_comm, ← ENNReal.ofReal_mul (by positivity)]
  gcongr

end GlobalTheory.Unf.DoubleSum

end

theorem GlobalTheory.Unf.doubleSum_le_maj : ∀ (D : D7) (θ : InfFam D) (a b c e : ℕ) (K : Set (Mx D a b)) (K' : Set (Mx D c e)) (N N' n : ℕ), 0 < n → ∀ (B : ℝ≥0∞) (F : ratMx D a b → ratMx D c e → ℝ≥0∞), (∀ x y, F x y ≠ 0 → InBox K (n • (x : Mx D a b)) ∧ InBox K' (n • (y : Mx D c e))) → (∀ x y, F x y * ENNReal.ofReal ((1 + realSize θ (x : Mx D a b)) ^ (N + N')) ≤ B) → (∀ x y, F x y * ENNReal.ofReal ((1 + realSize θ (y : Mx D c e)) ^ (N + N')) ≤ B) → ∑' x, ∑' y, F x y ≤ (n : ℝ≥0∞) ^ (N + N') * B * ((∑' x : ratMx D a b, ENNReal.ofReal (maj θ K N x)) * ∑' y : ratMx D c e, ENNReal.ofReal (maj θ K' N' y)) := by
  intro D θ a b c e K K' N N' n hn B F hF h1 h2
  have hinj : Function.Injective (fun x : ratMx D a b => n • x) := by
    intro u v huv
    obtain ⟨γ, hγ⟩ := u.2; obtain ⟨δ, hδ⟩ := v.2
    have e1 : ((n • u : ratMx D a b) : Mx D a b) = n • (u : Mx D a b) := AddSubgroup.coe_nsmul _ _ _
    have e2 : ((n • v : ratMx D a b) : Mx D a b) = n • (v : Mx D a b) := AddSubgroup.coe_nsmul _ _ _
    have h := congrArg Subtype.val huv
    simp only at h
    rw [e1, e2] at h
    apply Subtype.ext
    have hr : rat (n • γ) = rat (n • δ) := by
      have r1 : rat (n • γ) = n • rat γ := by
        funext i j; simp [rat, Matrix.smul_apply, nsmul_eq_mul, map_mul, map_natCast]
      have r2 : rat (n • δ) = n • rat δ := by
        funext i j; simp [rat, Matrix.smul_apply, nsmul_eq_mul, map_mul, map_natCast]
      rw [r1, r2]
      have hγ' : rat γ = (u : Mx D a b) := hγ
      have hδ' : rat δ = (v : Mx D a b) := hδ
      rw [hγ', hδ']; exact h
    have hγδ : γ = δ := by
      have := rat_injective hr
      funext i j
      have hij := congrFun (congrFun this i) j
      simp only [Matrix.smul_apply, nsmul_eq_mul] at hij
      exact mul_left_cancel₀ (Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hn)) hij
    have hγ' : rat γ = (u : Mx D a b) := hγ
    have hδ' : rat δ = (v : Mx D a b) := hδ
    rw [← hγ', ← hδ', hγδ]
  have hinj' : Function.Injective (fun y : ratMx D c e => n • y) := by
    intro u v huv
    obtain ⟨γ, hγ⟩ := u.2; obtain ⟨δ, hδ⟩ := v.2
    have e1 : ((n • u : ratMx D c e) : Mx D c e) = n • (u : Mx D c e) := AddSubgroup.coe_nsmul _ _ _
    have e2 : ((n • v : ratMx D c e) : Mx D c e) = n • (v : Mx D c e) := AddSubgroup.coe_nsmul _ _ _
    have h := congrArg Subtype.val huv
    simp only at h
    rw [e1, e2] at h
    apply Subtype.ext
    have hr : rat (n • γ) = rat (n • δ) := by
      have r1 : rat (n • γ) = n • rat γ := by
        funext i j; simp [rat, Matrix.smul_apply, nsmul_eq_mul, map_mul, map_natCast]
      have r2 : rat (n • δ) = n • rat δ := by
        funext i j; simp [rat, Matrix.smul_apply, nsmul_eq_mul, map_mul, map_natCast]
      rw [r1, r2]
      have hγ' : rat γ = (u : Mx D c e) := hγ
      have hδ' : rat δ = (v : Mx D c e) := hδ
      rw [hγ', hδ']; exact h
    have hγδ : γ = δ := by
      have := rat_injective hr
      funext i j
      have hij := congrFun (congrFun this i) j
      simp only [Matrix.smul_apply, nsmul_eq_mul] at hij
      exact mul_left_cancel₀ (Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hn)) hij
    have hγ' : rat γ = (u : Mx D c e) := hγ
    have hδ' : rat δ = (v : Mx D c e) := hδ
    rw [← hγ', ← hδ', hγδ]
  have hx : ∑' x : ratMx D a b, ENNReal.ofReal (maj θ K N (n • (x : Mx D a b))) ≤
      ∑' x : ratMx D a b, ENNReal.ofReal (maj θ K N x) := by
    have := ENNReal.tsum_comp_le_tsum_of_injective hinj (fun x : ratMx D a b => ENNReal.ofReal (maj θ K N x))
    simpa only [AddSubgroup.coe_nsmul] using this
  have hy : ∑' y : ratMx D c e, ENNReal.ofReal (maj θ K' N' (n • (y : Mx D c e))) ≤
      ∑' y : ratMx D c e, ENNReal.ofReal (maj θ K' N' y) := by
    have := ENNReal.tsum_comp_le_tsum_of_injective hinj' (fun y : ratMx D c e => ENNReal.ofReal (maj θ K' N' y))
    simpa only [AddSubgroup.coe_nsmul] using this
  calc ∑' x, ∑' y, F x y ≤ ∑' (x : ratMx D a b), ∑' (y : ratMx D c e), (n : ℝ≥0∞) ^ (N + N') * B * (ENNReal.ofReal (maj θ K N (n • (x : Mx D a b))) *
        ENNReal.ofReal (maj θ K' N' (n • (y : Mx D c e)))) :=
        ENNReal.tsum_le_tsum fun x => ENNReal.tsum_le_tsum fun y =>
          GlobalTheory.Unf.DoubleSum.pointwise θ K K' N N' n hn B F hF h1 h2 x y
    _ = (n : ℝ≥0∞) ^ (N + N') * B * ((∑' x : ratMx D a b, ENNReal.ofReal (maj θ K N (n • (x : Mx D a b)))) *
        ∑' y : ratMx D c e, ENNReal.ofReal (maj θ K' N' (n • (y : Mx D c e)))) := by
        simp_rw [ENNReal.tsum_mul_left, ENNReal.tsum_mul_right]
    _ ≤ _ := by gcongr
