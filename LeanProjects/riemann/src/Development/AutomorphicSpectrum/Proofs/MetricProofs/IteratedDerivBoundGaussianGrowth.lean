import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsThetaMeanSquareNorm
import Development.AutomorphicSpectrum.Statements.GeometryStatements.ZhangDimensionPushDownGrassmannianHeightBounds
import GroundTheory.HeightsAndTheta.Heights.KernelsLattice
import GroundTheory.HeightsAndTheta.Heights.LatticeLemmas.StatementsBundles
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights TensorProduct
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Sl

namespace GlobalTheory.CompanionTheory.Ar.Sl

theorem norm_iteratedDeriv_zero_le_of_gaussian_growth
    (f : ℂ → ℂ) (M lam : ℝ) (n n' i : ℕ) (hf : Differentiable ℂ f) (hlam : 0 < lam)
    (hn : 1 ≤ n) (hn' : 1 ≤ n') (hi : i ≤ n')
    (hb : ∀ τ, ‖f τ‖ ≤ M * Real.exp (n * ‖τ‖ ^ 2 * lam ^ 2 / 2)) :
    ‖iteratedDeriv i f 0‖ ≤ Real.sqrt (Real.exp 1 * n * n') ^ i * lam ^ i * M := by
  have h0 : ‖f 0‖ ≤ M := by simpa using hb 0
  have hM : 0 ≤ M := (norm_nonneg _).trans h0
  rcases Nat.eq_zero_or_pos i with rfl | hi0
  · simpa using h0
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hi0' : (0 : ℝ) < i := by exact_mod_cast hi0
  have hlam2 : (0 : ℝ) < lam ^ 2 := pow_pos hlam 2
  have hq : (0 : ℝ) < i / (n * lam ^ 2) := div_pos hi0' (mul_pos hn0 hlam2)
  set R : ℝ := Real.sqrt (i / (n * lam ^ 2)) with hR
  have hR2 : R ^ 2 = i / (n * lam ^ 2) := Real.sq_sqrt hq.le
  have hRpos : 0 < R := Real.sqrt_pos.2 hq
  have hsph : ∀ z ∈ Metric.sphere (0 : ℂ) R, ‖f z‖ ≤ M * Real.exp (i / 2) := by
    intro z hz
    have hz' : ‖z‖ = R := mem_sphere_zero_iff_norm.1 hz
    have e : (n : ℝ) * ‖z‖ ^ 2 * lam ^ 2 / 2 = i / 2 := by
      rw [hz', hR2]
      field_simp
    calc ‖f z‖ ≤ M * Real.exp (n * ‖z‖ ^ 2 * lam ^ 2 / 2) := hb z
      _ = M * Real.exp (i / 2) := by rw [e]
  have hC := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le i hRpos hf.diffContOnCl hsph
  refine hC.trans ?_
  have hA : 0 ≤ (i.factorial : ℝ) * (M * Real.exp (i / 2)) / R ^ i :=
    div_nonneg (mul_nonneg (Nat.cast_nonneg _) (mul_nonneg hM (Real.exp_pos _).le)) (pow_nonneg hRpos.le _)
  have hB : 0 ≤ Real.sqrt (Real.exp 1 * n * n') ^ i * lam ^ i * M :=
    mul_nonneg (mul_nonneg (pow_nonneg (Real.sqrt_nonneg _) _) (pow_nonneg hlam.le _)) hM
  refine (pow_le_pow_iff_left₀ hA hB two_ne_zero).1 ?_
  have hs1 : (Real.sqrt (Real.exp 1 * n * n') ^ i) ^ 2 = (Real.exp 1 * n * n') ^ i := by
    rw [← pow_mul, mul_comm i 2, pow_mul, Real.sq_sqrt (by positivity)]
  have hs2 : (R ^ i) ^ 2 = (i / (n * lam ^ 2)) ^ i := by
    rw [← pow_mul, mul_comm i 2, pow_mul, hR2]
  have hs3 : Real.exp (i / 2) ^ 2 = Real.exp 1 ^ i := by
    rw [← Real.exp_nat_mul, ← Real.exp_nat_mul]
    congr 1
    push_cast
    ring
  have key : ((i.factorial : ℝ)) ^ 2 ≤ ((i : ℝ) * n') ^ i := by
    have h1 : (i.factorial : ℝ) ≤ (i : ℝ) ^ i := by exact_mod_cast Nat.factorial_le_pow i
    have h2 : ((i : ℝ) ^ i) ^ 2 ≤ ((i : ℝ) * n') ^ i := by
      rw [← pow_mul, mul_comm i 2, pow_mul, sq]
      exact pow_le_pow_left₀ (by positivity)
        (mul_le_mul_of_nonneg_left (by exact_mod_cast hi) hi0'.le) i
    exact (pow_le_pow_left₀ (Nat.cast_nonneg _) h1 2).trans h2
  have hin : (i : ℝ) ^ i ≠ 0 := pow_ne_zero _ hi0'.ne'
  have hnl : ((n : ℝ) * lam ^ 2) ^ i ≠ 0 := pow_ne_zero _ (mul_pos hn0 hlam2).ne'
  have lhs : ((i.factorial : ℝ) * (M * Real.exp (i / 2)) / R ^ i) ^ 2 =
      (M ^ 2 * Real.exp 1 ^ i * (n : ℝ) ^ i * (lam ^ 2) ^ i) * (i.factorial : ℝ) ^ 2 / (i : ℝ) ^ i := by
    rw [div_pow, mul_pow, mul_pow, hs3, hs2, div_pow]
    field_simp
    ring
  have rhs : (Real.sqrt (Real.exp 1 * n * n') ^ i * lam ^ i * M) ^ 2 =
      (M ^ 2 * Real.exp 1 ^ i * (n : ℝ) ^ i * (lam ^ 2) ^ i) * ((i : ℝ) * n') ^ i / (i : ℝ) ^ i := by
    rw [mul_pow, mul_pow, hs1]
    field_simp
    ring
  rw [lhs, rhs]
  exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left key (by positivity)) (pow_nonneg hi0'.le _)

end GlobalTheory.CompanionTheory.Ar.Sl
