import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.SplitRigidity.SplitRigidAlt
import Development.WeilBound.RepresentationTheoryGL.JacquetShalikaBounds.AbsoluteRigidity.LandauIteratedDerivatives.LandauL
import Development.WeilBound.RepresentationTheoryGL.JacquetShalikaBounds.AbsoluteRigidity.EulerLogarithms.EulerProductLogBound
import Development.WeilBound.RepresentationTheoryGL.JacquetShalikaBounds.AbsoluteRigidity.DiagonalTermNorms.ConvergenceOfLandauEuler
open PositivityTheory.RgJS UpperTheory.V.Z.Tf.GOne UpperTheory.V.Z.Tf.SR
open scoped ComplexConjugate

private theorem UpperTheory.V.Z.Tf.SR.lterm_scale {W A B G : Type} [Fintype A] [Fintype B] [Fintype G] (q : W → ℕ)
    (α : W → A → ℂ) (β : W → B → ℂ) (γ : W → G → ℂ) (s : ℂ) (p : W × ℕ) (u v : ℂ)
    (hα : ∑ a, α p.1 a ^ (p.2 + 1) = u * ∑ a, γ p.1 a ^ (p.2 + 1))
    (hβ : ∑ b, β p.1 b ^ (p.2 + 1) = v * ∑ a, γ p.1 a ^ (p.2 + 1)) :
    lterm q α β s p = u * conj v * lterm q γ γ s p := by
  simp only [lterm]
  rw [hα, hβ, map_mul]
  ring

private theorem UpperTheory.V.Z.Tf.SR.sum_mul_conj {M : ℕ} (a : Fin M → ℂ) (t : ℂ) :
    ∑ i, ∑ j, a i * conj (a j) * t = (Complex.normSq (∑ i, a i) : ℂ) * t := by
  rw [← Complex.mul_conj, map_sum, Finset.sum_mul_sum, Finset.sum_mul]
  exact Finset.sum_congr rfl fun i _ => by rw [Finset.sum_mul]

theorem UpperTheory.V.Z.Tf.SR.shareBd :
    LogTwo → CrossUp → ShareBd := by
  intro hLog hCross W q X d A hS x I M z c hM hz hc hc1 hpow
  have hconv := convergence_of_landau_euler landauL euler_product_log_bound W q X d A hS
  have h2 := hS.primes.two
  have bound : ∀ i j : Fin M, ∃ D : ℝ, ∀ σ : ℝ, 1 < σ → σ ≤ 2 →
      (∑' p, lterm q (A (z i)) (A (z j)) σ p).re ≤ (if i = j then -Real.log (σ - 1) else 0) + D := by
    intro i j
    by_cases e : i = j
    · subst e
      obtain ⟨C, hC⟩ := hLog W q X d A hS (z i)
      refine ⟨C, fun σ a b => ?_⟩
      have := (abs_le.1 (hC σ a b)).2
      rw [if_pos rfl]
      linarith
    · obtain ⟨C, hC⟩ := hCross W q X d A hS (z i) (z j) (fun h => e (hz h))
      refine ⟨C, fun σ a b => ?_⟩
      rw [if_neg e]
      linarith [hC σ a b]
  choose D hD using bound
  have hMpos : (0 : ℝ) < M := by exact_mod_cast hM
  refine ⟨(∑ i, ∑ j, D i j) / (M : ℝ) ^ 2, fun σ h1 hσ2 => ?_⟩
  let t : W × ℕ → ℝ := fun p => DiagonalEntryNormBounds.cd (A x) p * Real.exp (-(DiagonalEntryNormBounds.ll q p * σ))
  let s : W × ℕ → ℂ := fun p => ∑ i : Fin M, c p.1 ^ (i.val * (p.2 + 1))
  let g : W × ℕ → ℝ := fun p => Complex.normSq (s p) * t p
  have ht0 : ∀ p, 0 ≤ t p := fun p => mul_nonneg (DiagonalEntryNormBounds.cd_nonneg _ p) (Real.exp_pos _).le
  have hg0 : ∀ p, 0 ≤ g p := fun p => mul_nonneg (Complex.normSq_nonneg _) (ht0 p)
  have hT : ∀ p, lterm q (A x) (A x) σ p = (t p : ℂ) := fun p => DiagonalEntryNormBounds.lterm_diag q h2 (A x) σ p
  have hF : ∀ p, ∑ i, ∑ j, lterm q (A (z i)) (A (z j)) σ p = (g p : ℂ) := by
    intro p
    have e : ∀ i j : Fin M, lterm q (A (z i)) (A (z j)) σ p =
        c p.1 ^ (i.val * (p.2 + 1)) * conj (c p.1 ^ (j.val * (p.2 + 1))) * (t p : ℂ) := fun i j => by
      rw [← hT]
      exact lterm_scale q _ _ _ _ p _ _ (hpow i p.1 (p.2 + 1)) (hpow j p.1 (p.2 + 1))
    simp only [e]
    rw [sum_mul_conj]
    simp only [g, s, Complex.ofReal_mul]
  have hsum : ∀ i j, Summable fun p => lterm q (A (z i)) (A (z j)) σ p :=
    fun i j => ((hconv _ _).1 σ h1).of_norm
  have hsF : Summable fun p => ∑ i, ∑ j, lterm q (A (z i)) (A (z j)) σ p :=
    summable_sum fun i _ => summable_sum fun j _ => hsum i j
  have hg : Summable g := by
    rw [← Complex.summable_ofReal]
    exact hsF.congr hF
  have e1 : ∑ i, ∑ j, ∑' p, lterm q (A (z i)) (A (z j)) σ p = ((∑' p, g p : ℝ) : ℂ) := by
    rw [Complex.ofReal_tsum, ← tsum_congr hF, Summable.tsum_finsetSum fun i _ => summable_sum fun j _ => hsum i j]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Summable.tsum_finsetSum fun j _ => hsum i j]
  have e2 : ∑' p, g p ≤ (M : ℝ) * -Real.log (σ - 1) + ∑ i, ∑ j, D i j := by
    have e3 := congrArg Complex.re e1
    rw [Complex.ofReal_re, Complex.re_sum] at e3
    rw [← e3]
    calc ∑ i, (∑ j, ∑' p, lterm q (A (z i)) (A (z j)) σ p).re
        ≤ ∑ i : Fin M, ∑ j : Fin M, ((if i = j then -Real.log (σ - 1) else 0) + D i j) := by
          refine Finset.sum_le_sum fun i _ => ?_
          rw [Complex.re_sum]
          exact Finset.sum_le_sum fun j _ => hD i j σ h1 hσ2
      _ = _ := by
          simp [Finset.sum_add_distrib]
  have e4 : (∑' p : {p : W × ℕ // p.1 ∈ I}, lterm q (A x) (A x) σ p.1).re =
      ∑' p : {p : W × ℕ // p.1 ∈ I}, t p.1 := by
    rw [tsum_congr fun p : {p : W × ℕ // p.1 ∈ I} => hT p.1, ← Complex.ofReal_tsum, Complex.ofReal_re]
  have e5 : ∑' p : {p : W × ℕ // p.1 ∈ I}, g p.1 = (M : ℝ) ^ 2 * ∑' p : {p : W × ℕ // p.1 ∈ I}, t p.1 := by
    rw [← tsum_mul_left]
    refine tsum_congr fun p => ?_
    have : s p.1 = (M : ℂ) := by
      simp [s, hc1 p.1.1 p.2]
    simp only [g, this, Complex.normSq_natCast]
    ring
  have e6 : ∑' p : {p : W × ℕ // p.1 ∈ I}, g p.1 ≤ ∑' p, g p := by
    have e : ∑' p : {p : W × ℕ // p.1 ∈ I}, g p.1 + ∑' p : {p : W × ℕ // ¬ p.1 ∈ I}, g p.1 = ∑' p, g p :=
      Summable.tsum_subtype_add_tsum_subtype_compl hg {p : W × ℕ | p.1 ∈ I}
    have : 0 ≤ ∑' p : {p : W × ℕ // ¬ p.1 ∈ I}, g p.1 := tsum_nonneg fun p => hg0 p.1
    linarith
  rw [e4]
  have e7 : -Real.log (σ - 1) / M + (∑ i, ∑ j, D i j) / (M : ℝ) ^ 2 =
      ((M : ℝ) * -Real.log (σ - 1) + ∑ i, ∑ j, D i j) / (M : ℝ) ^ 2 := by
    field_simp
  rw [e7, le_div_iff₀ (by positivity)]
  linarith
