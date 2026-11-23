import Mathlib
import GroundTheory.HeightsAndTheta.Heights.Antisymmetric.Statements
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.ExistsUniqueStatement
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.HeckeSectionsIsotropicCommutatorPairingPower
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterNamed
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.KleimanNefness.KleimanSt
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.CutoffCoefficientsBoundStatement
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.TowerHeightIdentityExpansionStatement
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.HomogeneousPowerSumDecompositionStatement
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.TestPolynomialShiftTotalStatement
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.TestPolynomialRemainderBoundStatement
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar.Top

namespace GlobalTheory.CompanionTheory.Ar.Top

theorem lower_bound_key_inequality (K f m x L C h R : ℝ) (hK : 0 < K) (hf : 1 ≤ f) (hm : 1 ≤ m)
    (h1 : -(C * f * m * L) * K ≤ h - x * (f * (K * m)) + R) (l : ℝ) (h2 : h ≤ K * (f * (m / 2 * l)))
    (h3 : |R| ≤ 1.6 * K) : x ≤ C * L + l / 2 + 1.6 := by
  have hR : R ≤ 1.6 * K := (le_abs_self R).trans h3
  have hfm : 1 ≤ f * m := by nlinarith
  have hP : 0 < f * (K * m) := mul_pos (by linarith) (mul_pos hK (by linarith))
  have hKfm : K ≤ K * (f * m) := by nlinarith
  have key : x * (f * (K * m)) ≤ (C * L + l / 2 + 1.6) * (f * (K * m)) := by
    nlinarith
  exact le_of_mul_le_mul_right key hP

theorem lower_bound_finite_arith (N m A M : ℝ) (hm : 0 < m) (hM : 0 ≤ M) (hN : N ≤ 2 * m) (h : -(N * M) ≤ m * A) : -(2 * M) ≤ A := by
  have h' : m * (-(2 * M)) ≤ m * A := by nlinarith
  exact le_of_mul_le_mul_left h' hm

theorem test_height_bound_slope_flat : ∀ II : IntersectionSystem, ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) (T : RootTower Ψ N) [Nonempty Ψ] (hh : RP Ψ N →ₗ[ℝ] ℝ) (frob : ℕ → Ψ → ℕ → Ψ ⊕ Ψ) (C C' rd Lval : ℝ), 0 ≤ C → 0 ≤ C' → 1 ≤ rd → T.Proportional → I9 (Ψ := Ψ) (N := N) hh → T.PropF II C' rd Lval → T.SlopeLower II C rd Lval → hh (testPoly T.j) ≤ ((dimX Ψ N T.j : ℝ) + 1) * testDeg Ψ N T.j * (Fintype.card Ψ * ((min T.j (N - T.j) : ℕ) / 2 * Real.log (N + 1))) → T.LowerBoundAtBase II hh frob (2 * (C + C') + 3) rd Lval := by
  intro II Ψ _ _ N T _ hh frob C C' rd Lval hC hC' hrd hprop hI9 hPF hSL hhh B₀ A₀ b₀ hB128 hB4 hbad hId
  have hj1 := T.j_pos
  have hjN := T.j_lt
  obtain ⟨hhom, htd, hcase1, hcase2⟩ := GlobalTheory.T.test_polynomial_shift_total Ψ N T.j hj1 hjN
  obtain ⟨Q, hQ1, hQ2⟩ := GlobalTheory.T.homogeneous_power_sum_decomposition Ψ N (testPoly T.j) (by omega) hhom
  have hdec : IsDecomp (testPoly T.j) Q := ⟨hQ1, hQ2⟩
  have hPP := GlobalTheory.T.tower_height_identity_expansion II Ψ N T hh frob B₀ A₀ b₀ (testPoly T.j) Q hId hdec
  have hR := GlobalTheory.T.test_polynomial_remainder_bound Ψ N T.j T.bad frob B₀ Q hj1 hjN hB4 hdec
  have hAb := GlobalTheory.T.cutoff_coefficients_bound II Ψ N T hh frob C' rd Lval B₀ A₀ b₀ hprop hI9 hPF hB128 hbad hId
  have hSL' := hSL B₀ hB128 hB4 hbad
  have hvol : 0 < T.volT := by
    show 0 < ∑ c, T.vol c
    exact Finset.sum_pos (fun c _ => hprop.1 c) Finset.univ_nonempty
  have hcard : 1 ≤ Fintype.card Ψ := Fintype.card_pos
  have hf : (1:ℝ) ≤ (Fintype.card Ψ : ℝ) := by exact_mod_cast hcard
  have hN1 : N + 1 ≤ B₀ := by nlinarith
  have hlogB : Real.log (B₀:ℝ) ≤ bigLam (B₀:ℝ) rd Lval := by
    show Real.log (B₀:ℝ) ≤ Real.log ((B₀:ℝ) * rd) + |Lval|
    have hB0 : (0:ℝ) < B₀ := by exact_mod_cast (show 0 < B₀ by omega)
    have := Real.log_le_log hB0 (le_mul_of_one_le_right hB0.le hrd)
    linarith [abs_nonneg Lval]
  have hl : Real.log ((N:ℝ) + 1) ≤ Real.log (B₀:ℝ) :=
    Real.log_le_log (by positivity) (by exact_mod_cast hN1)
  have hl0 : 0 ≤ Real.log ((N:ℝ) + 1) := Real.log_nonneg (by linarith [(Nat.cast_nonneg N : (0:ℝ) ≤ N)])
  have h16 : 1.6 ≤ Real.log (B₀:ℝ) := by
    have h128 : Real.log 128 = 7 * Real.log 2 := by
      rw [show (128:ℝ) = 2 ^ 7 by norm_num, Real.log_pow]; norm_num
    have : Real.log 128 ≤ Real.log (B₀:ℝ) :=
      Real.log_le_log (by norm_num) (by exact_mod_cast hB128)
    linarith [Real.log_two_gt_d9]
  set Λ := bigLam (B₀:ℝ) rd Lval with hΛ
  set R := ∑ τ, ∑ k ∈ Finset.Icc 1 N, restSum T.j T.bad frob B₀ τ k (Q τ k) with hRdef
  set f : ℝ := (Fintype.card Ψ : ℝ) with hfdef
  set D : ℝ := (dimX Ψ N T.j : ℝ) with hD
  set td := testDeg Ψ N T.j with htddef
  set l := Real.log ((N:ℝ) + 1) with hldef
  have hK : 0 < (D + 1) * td := mul_pos (by positivity) htd
  have hM0 : 0 ≤ C * Λ + l / 2 + 1.6 + C' * Λ := by
    have := mul_nonneg hC (show 0 ≤ Λ by linarith)
    have := mul_nonneg hC' (show 0 ≤ Λ by linarith)
    linarith
  have hfinal : ∀ A : ℝ, -(2 * (C * Λ + l / 2 + 1.6 + C' * Λ)) ≤ A →
      -((2 * (C + C') + 3) * Λ) ≤ A := by
    intro A hA
    nlinarith
  apply hfinal
  have hAb' := abs_le.mp hAb
  by_cases hc : N - T.j ≤ T.j
  · have hs := hcase1 hc
    have hmin : min T.j (N - T.j) = N - T.j := min_eq_right hc
    rw [hmin] at hSL' hhh
    have hm1 : (1:ℝ) ≤ ((N - T.j : ℕ) : ℝ) := by
      have : 1 ≤ N - T.j := by omega
      exact_mod_cast this
    set m : ℝ := ((N - T.j : ℕ) : ℝ) with hmdef
    have hSh : ∑ σ : Ψ, Sh (N := N) T.j σ (testPoly T.j) = 0 := Finset.sum_eq_zero (fun σ _ => (hs σ).1)
    have hTot : ∑ σ : Ψ, Tot (N := N) σ (testPoly T.j) = f * ((D + 1) * td * m) := by
      rw [Finset.sum_congr rfl (fun σ _ => (hs σ).2), Finset.sum_const, Finset.card_univ,
        nsmul_eq_mul]
      ring
    rw [hPP, hSh, hTot] at hSL'
    have h1 : -(C * f * m * Λ) * ((D + 1) * td) ≤
        hh (testPoly T.j) - b₀ * (f * ((D + 1) * td * m)) + R := by
      refine le_of_mul_le_mul_left ?_ hvol
      calc T.volT * (-(C * f * m * Λ) * ((D + 1) * td))
          = -(C * f * m * Λ) * ((D + 1) * (T.volT * td)) := by ring
        _ ≤ _ := hSL'
        _ = T.volT * (hh (testPoly T.j) - b₀ * (f * ((D + 1) * td * m)) + R) := by ring
    have hb := lower_bound_key_inequality ((D + 1) * td) f m b₀ Λ C (hh (testPoly T.j)) R hK hf hm1 h1 l hhh hR
    have hj0 : (0:ℝ) < (T.j : ℝ) := by
      have : 0 < T.j := by omega
      exact_mod_cast this
    have hNj : (N:ℝ) ≤ 2 * (T.j : ℝ) := by
      have : N ≤ 2 * T.j := by omega
      exact_mod_cast this
    refine lower_bound_finite_arith (N:ℝ) (T.j:ℝ) A₀ _ hj0 hM0 hNj ?_
    have hNb := mul_le_mul_of_nonneg_left hb (Nat.cast_nonneg (α := ℝ) N)
    nlinarith
  · have hs := hcase2 hc
    have hmin : min T.j (N - T.j) = T.j := min_eq_left (by omega)
    rw [hmin] at hSL' hhh
    have hm1 : (1:ℝ) ≤ (T.j : ℝ) := by exact_mod_cast hj1
    set m : ℝ := (T.j : ℝ) with hmdef
    have hSh : ∑ σ : Ψ, Sh (N := N) T.j σ (testPoly T.j) = f * (-((D + 1) * m * td)) := by
      rw [Finset.sum_congr rfl (fun σ _ => (hs σ).1), Finset.sum_const, Finset.card_univ,
        nsmul_eq_mul]
    have hTot : ∑ σ : Ψ, Tot (N := N) σ (testPoly T.j) = f * (-((D + 1) * m * td)) := by
      rw [Finset.sum_congr rfl (fun σ _ => (hs σ).2), Finset.sum_const, Finset.card_univ,
        nsmul_eq_mul]
    rw [hPP, hSh, hTot] at hSL'
    have h1 : -(C * f * m * Λ) * ((D + 1) * td) ≤
        hh (testPoly T.j) - (-(A₀ + b₀)) * (f * ((D + 1) * td * m)) + R := by
      refine le_of_mul_le_mul_left ?_ hvol
      calc T.volT * (-(C * f * m * Λ) * ((D + 1) * td))
          = -(C * f * m * Λ) * ((D + 1) * (T.volT * td)) := by ring
        _ ≤ _ := hSL'
        _ = T.volT * (hh (testPoly T.j) - (-(A₀ + b₀)) * (f * ((D + 1) * td * m)) + R) := by ring
    have hb := lower_bound_key_inequality ((D + 1) * td) f m (-(A₀ + b₀)) Λ C (hh (testPoly T.j)) R hK hf hm1 h1 l hhh hR
    have hcast : ((N - T.j : ℕ) : ℝ) = (N:ℝ) - (T.j:ℝ) := by
      rw [Nat.cast_sub (by omega)]
    have hpos : (0:ℝ) < ((N - T.j : ℕ) : ℝ) := by
      have : 0 < N - T.j := by omega
      exact_mod_cast this
    have hNj : (N:ℝ) ≤ 2 * ((N - T.j : ℕ) : ℝ) := by
      have : N ≤ 2 * (N - T.j) := by omega
      exact_mod_cast this
    refine lower_bound_finite_arith (N:ℝ) ((N - T.j : ℕ) : ℝ) A₀ _ hpos hM0 hNj ?_
    rw [hcast]
    have hNb := mul_le_mul_of_nonneg_left hb (Nat.cast_nonneg (α := ℝ) N)
    nlinarith

end GlobalTheory.CompanionTheory.Ar.Top
