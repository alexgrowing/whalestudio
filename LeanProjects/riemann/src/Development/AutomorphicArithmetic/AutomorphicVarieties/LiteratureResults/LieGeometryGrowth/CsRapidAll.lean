import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.CsStmt
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.CsRapidEig
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.QhtFacts
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.ExpOfDeriv
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.OneReal
open UpperTheory.V.Lit.Geo.Cs

private theorem le_div_one_add_pow_succ_of_mul_le {x K Q A C F : ℝ} {N : ℕ} (hQ : 1 ≤ Q) (hA : 0 ≤ A) (hN : A * C ≤ N)
    (hF : F ≤ C * (1 + Real.log Q)) (hx : 0 ≤ x) (h : x * Q ^ N ≤ K) :
    x ≤ K * Real.exp (A * C) * Real.exp (-(A * F)) := by
  have hQ0 : 0 < Q := lt_of_lt_of_le one_pos hQ
  have hl : 0 ≤ Real.log Q := Real.log_nonneg hQ
  have hp : Q ^ N = Real.exp (N * Real.log Q) := by
    rw [Real.exp_nat_mul, Real.exp_log hQ0]
  have h1 : A * F - A * C ≤ N * Real.log Q := by
    have := mul_le_mul_of_nonneg_left hF hA
    have := mul_le_mul_of_nonneg_right hN hl
    nlinarith
  have h2 : x * Real.exp (A * F - A * C) ≤ K := by
    refine le_trans ?_ h
    rw [hp]
    exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 h1) hx
  have h3 : x = x * Real.exp (A * F - A * C) * (Real.exp (A * C) * Real.exp (-(A * F))) := by
    rw [mul_assoc, ← Real.exp_add, ← Real.exp_add, show A * F - A * C + (A * C + -(A * F)) = 0 by ring,
      Real.exp_zero, mul_one]
  rw [h3, mul_assoc K]
  exact mul_le_mul_of_nonneg_right h2 (by positivity)

open GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af GlobalTheory.UnitaryBC GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
  GroundTheory.Automorphic.CuspidalSpectrum in
theorem UpperTheory.V.Lit.Geo.Cs.rapidAll :
    RapidAll := by
  intro E _ _ _ a U Ξ f lam C hlam hf q α hα hR
  obtain ⟨r, hr⟩ := UpperTheory.V.Lit.Bor.oneReal E a Ξ
  obtain ⟨hq1, hq2, -⟩ := UpperTheory.V.Lit.Geo.qhtFacts E a
  refine ⟨|r|, abs_nonneg r, fun A hA X j l => ?_⟩
  obtain ⟨he, hv⟩ := UpperTheory.V.Lit.Geo.Cs.rapidEig E a U Ξ r hr q α hα X j l
  obtain ⟨K, hK⟩ := hR l X ⌈A * C⌉₊
  refine ⟨K * Real.exp (A * C), fun g => ?_⟩
  obtain ⟨g₁, hs⟩ : ∃ g₁ : KernelIndexFullLattice.G1 E a, splitCentre E a (lam g) * g₁.1 = g := ⟨_, hlam.split g⟩
  have hK' := hK g₁
  have hq : qht g = qht (E := E) (a := a) g₁.1 := by
    have := hq2 1 (lam g) g₁.1
    rw [map_one, one_mul, hs] at this
    exact this
  have ha := UpperTheory.V.Lit.Bor.aInv E a _ _ he (lam g) g₁.1
  rw [hs] at ha
  rw [← hq] at hK'
  have hb := le_div_one_add_pow_succ_of_mul_le (hq1 g) hA (Nat.le_ceil (A * C)) (hf g) (norm_nonneg _)
    (le_trans (mul_le_mul_of_nonneg_right (norm_le_pi_norm _ j) (pow_nonneg (zero_le_one.trans (hq1 g)) _)) hK')
  have hb' : ‖((l.map (lie E a)).prod (Bor.cmp j (α X))).1 g₁.1‖ ≤
      K * Real.exp (A * C) * Real.exp (-(A * f g)) := by
    rw [← hv]
    exact hb
  have hc : ‖Complex.exp (-(r : ℂ) * (lam g : ℂ))‖ ≤ Real.exp (|r| * |lam g|) := by
    rw [Complex.norm_exp, Real.exp_le_exp, ← abs_mul]
    simpa using neg_le_abs (r * lam g)
  rw [ha, norm_mul, sub_eq_add_neg, Real.exp_add, mul_left_comm]
  exact mul_le_mul hc hb' (norm_nonneg _) (Real.exp_pos _).le
