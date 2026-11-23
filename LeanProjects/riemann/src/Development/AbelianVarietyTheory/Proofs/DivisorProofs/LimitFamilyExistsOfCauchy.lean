import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SlopeTestRemainingChoices
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ComponentMean
import Formalism.SharpRestriction.Divisibility.LatticeTransfer
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFormOfFunctional
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinFormPowEqSumMonomial
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MvPolynomialEqZeroOfEvalEqZeroOnOpen
open MvPolynomial Formalism.DegreeFormula Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.MainNotions Formalism.MainNotions.WeightThresholdDefs Filter Topology Classical GlobalTheory.FlagPoly GlobalTheory.FlagAr GlobalTheory.Mean4
open scoped ComplexOrder

namespace GlobalTheory.Mean4

theorem exists_tendsto_of_log_pow_div_sqrt_bound (F : ℝ → ℝ) (C R₀ : ℝ) (d : ℕ)
    (h : ∀ R R' : ℝ, R₀ ≤ R → R ≤ R' → |F R - F R'| ≤ C * Real.log R ^ d / Real.sqrt R) :
    ∃ L, Tendsto F atTop (𝓝 L) := by
  have h0 : Tendsto (fun R : ℝ => C * Real.log R ^ d / Real.sqrt R) atTop (𝓝 0) := by
    have h1 := (isLittleO_log_rpow_rpow_atTop (d : ℝ) (s := 1 / 2) (by norm_num)).tendsto_div_nhds_zero
    have h2 := h1.const_mul C
    rw [mul_zero] at h2
    refine h2.congr fun R => ?_
    rw [Real.sqrt_eq_rpow, Real.rpow_natCast, mul_div_assoc]
  have hc : CauchySeq F := by
    rw [Metric.cauchySeq_iff']
    intro ε hε
    obtain ⟨R, hR1, hR2⟩ := ((h0.eventually (gt_mem_nhds hε)).and (eventually_ge_atTop R₀)).exists
    refine ⟨R, fun R' hR' => ?_⟩
    rw [dist_comm, Real.dist_eq]
    exact (h R R' hR2 hR').trans_lt hR1
  exact cauchySeq_tendsto_of_complete hc

theorem exists_limit_functional {ι : Type} [Fintype ι] [DecidableEq ι] {N : ℕ} (d : ℕ)
    (G : ℝ → (Pol ι N →ₗ[ℝ] ℝ))
    (hG : ∀ R (P : Pol ι N) (e : ℕ), e ≠ d → P.IsHomogeneous e → G R P = 0)
    (U : Set (ι × Fin N → ℝ)) (hU : IsOpen U) (hne : U.Nonempty)
    (hl : ∀ x ∈ U, ∃ L, Tendsto (fun R => G R (linRoot (fun τ i => x (τ, i)) ^ d)) atTop (𝓝 L)) :
    ∃ Φ : Pol ι N →ₗ[ℝ] ℝ, ∀ F, Tendsto (fun R => G R F) atTop (𝓝 (Φ F)) := by
  choose P hP hev using fun R => exists_form_of_functional ι N d (G R)
  obtain ⟨Q, -, hQ, -⟩ := GlobalTheory.exists_poly_limit_of_tendsto_on_open (ι × Fin N) d P U hU hne
    (fun R => (hP R).totalDegree_le) (fun x hx => by
      obtain ⟨L, hL⟩ := hl x hx
      exact ⟨L, hL.congr fun R => (hev R _).symm⟩)
  have hm : ∀ m : (ι × Fin N) →₀ ℕ, ∃ L, Tendsto (fun R => G R (monomial m 1)) atTop (𝓝 L) := by
    intro m
    by_cases hd : m.degree = d
    · have hc : ((-1 : ℝ) ^ d * (Nat.multinomial Finset.univ m : ℝ)) ≠ 0 :=
        mul_ne_zero (pow_ne_zero _ (by norm_num)) (by exact_mod_cast (Nat.multinomial_pos _ _).ne')
      refine ⟨_, ((hQ m).div_const ((-1 : ℝ) ^ d * (Nat.multinomial Finset.univ m : ℝ))).congr fun R => ?_⟩
      rw [(coeff_eq_of_polarisation ι N d (G R) (P R) (hev R) m hd).1, mul_div_cancel_left₀ _ hc]
    · exact ⟨0, tendsto_const_nhds.congr fun R => (hG R _ _ hd (isHomogeneous_monomial _ rfl)).symm⟩
  choose L hL using hm
  refine ⟨(basisMonomials (ι × Fin N) ℝ).constr ℝ L, fun F => ?_⟩
  induction F using MvPolynomial.induction_on' with
  | monomial m a =>
    have h1 : (monomial m a : Pol ι N) = a • monomial m 1 := by rw [smul_monomial, smul_eq_mul, mul_one]
    have h2 : (basisMonomials (ι × Fin N) ℝ).constr ℝ L (monomial m 1) = L m := by
      simpa using (basisMonomials (ι × Fin N) ℝ).constr_basis ℝ L m
    simp only [h1, map_smul, smul_eq_mul, h2]
    exact (hL m).const_mul a
  | add p q hp hq =>
    simp only [map_add]
    exact hp.add hq

theorem exists_limFam_of_cauchy : ∀ (D : D7) (Y : ShimX D.what₂.Tau), (∀ B : ℝ, 2 ≤ B → ∀ u : Wt Y, CptGaps Y 0 u → supAbs Y u ≤ 1 → ∃ C R₀ : ℝ, ∀ R R' : ℝ, R₀ ≤ R → R ≤ R' → |Y.arDeg (setB Y B) R (linRoot u ^ (dimFl D.what₂.Tau Y.N + 1)) - Y.arDeg (setB Y B) R' (linRoot u ^ (dimFl D.what₂.Tau Y.N + 1))| ≤ C * Real.log R ^ (dimY Y + 1) / Real.sqrt R) → ∃ Φ : ℝ → Fn Y, LimFam Φ := by
  intro D Y h
  let U : Set (D.what₂.Tau × Fin Y.N → ℝ) :=
    (⋂ τ, ⋂ a : Fin Y.N, ⋂ b : Fin Y.N, {x | a < b → x (τ, b) < x (τ, a)}) ∩ ⋂ y, {x | |x y| < 1}
  have hU : IsOpen U := by
    refine IsOpen.inter (isOpen_iInter_of_finite fun τ => isOpen_iInter_of_finite fun a =>
      isOpen_iInter_of_finite fun b => ?_) (isOpen_iInter_of_finite fun y => ?_)
    · by_cases hab : a < b
      · simp only [hab, forall_true_left]
        exact isOpen_lt (continuous_apply _) (continuous_apply _)
      · simp [hab]
    · exact isOpen_lt (continuous_apply y).abs continuous_const
  have hne : U.Nonempty := by
    refine ⟨fun y => -((y.2 : ℕ) : ℝ) / Y.N, ?_, ?_⟩
    · simp only [Set.mem_iInter, Set.mem_setOf_eq]
      intro τ a b hab
      have hN : (0 : ℝ) < Y.N := by exact_mod_cast a.pos
      have : ((a : ℕ) : ℝ) < (b : ℕ) := by exact_mod_cast hab
      exact div_lt_div_of_pos_right (by linarith) hN
    · simp only [Set.mem_iInter, Set.mem_setOf_eq]
      intro y
      have hN : (0 : ℝ) < Y.N := by exact_mod_cast y.2.pos
      have : ((y.2 : ℕ) : ℝ) < Y.N := by exact_mod_cast y.2.2
      rw [abs_div, abs_neg, Nat.abs_cast, Nat.abs_cast, div_lt_one hN]
      exact this
  have key : ∀ B : ℝ, ∃ Φ : Fn Y, 2 ≤ B → IsLimDeg Y B Φ := by
    intro B
    by_cases hB : 2 ≤ B
    · obtain ⟨Φ, hΦ⟩ := exists_limit_functional (dimFl D.what₂.Tau Y.N + 1) (fun R => Y.arDeg (setB Y B) R)
        (fun R P e he hP => Y.arDeg_homog _ R P e he hP) U hU hne (fun x hx => by
          obtain ⟨hx1, hx2⟩ := hx
          simp only [Set.mem_iInter, Set.mem_setOf_eq] at hx1 hx2
          obtain ⟨C, R₀, hC⟩ := h B hB (fun τ i => x (τ, i))
            (fun τ a b hab _ => sub_nonneg.2 (hx1 τ a b (by rw [Fin.lt_def]; omega)).le)
            (Real.iSup_le (fun y => (hx2 y).le) zero_le_one)
          exact exists_tendsto_of_log_pow_div_sqrt_bound _ C R₀ _ hC)
      exact ⟨Φ, fun _ => hΦ⟩
    · exact ⟨0, fun h => absurd h hB⟩
  choose Φ hΦ using key
  exact ⟨Φ, hΦ⟩

end GlobalTheory.Mean4
