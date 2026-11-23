import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.SplitRigidity.SplitRigidAlt
import Development.WeilBound.RepresentationTheoryGL.JacquetShalikaBounds.AbsoluteRigidity.LandauIteratedDerivatives.LandauL
import Development.WeilBound.RepresentationTheoryGL.JacquetShalikaBounds.AbsoluteRigidity.EulerLogarithms.EulerProductLogBound
import Development.WeilBound.RepresentationTheoryGL.JacquetShalikaBounds.AbsoluteRigidity.DiagonalTermNorms.ConvergenceOfLandauEuler
open PositivityTheory.RgJS UpperTheory.V.Z.Tf.GOne UpperTheory.V.Z.Tf.SR

private theorem UpperTheory.V.Z.Tf.SR.le_of_sq_le {P T c n : ℝ} (hn : 0 < n) (hc : 0 ≤ c) (hT : 0 ≤ T)
    (h : P ^ 2 ≤ T ^ 2 / (16 * n ^ 2) + c * T) : P ≤ T / (3 * n) + 3 * n * c / 2 := by
  have hS : 0 ≤ T / (3 * n) + 3 * n * c / 2 := by positivity
  have e : (T / (3 * n) + 3 * n * c / 2) ^ 2 = T ^ 2 / (9 * n ^ 2) + c * T + (3 * n * c / 2) ^ 2 := by
    field_simp
    ring
  have h1 : T ^ 2 / (16 * n ^ 2) ≤ T ^ 2 / (9 * n ^ 2) :=
    div_le_div_of_nonneg_left (sq_nonneg T) (by positivity) (by nlinarith [sq_nonneg n, pow_pos hn 2])
  have h2 : P ^ 2 ≤ (T / (3 * n) + 3 * n * c / 2) ^ 2 := by
    rw [e]
    nlinarith [sq_nonneg (3 * n * c / 2)]
  exact (abs_le_of_sq_le_sq' h2 hS).2

private theorem UpperTheory.V.Z.Tf.SR.diag_re_nonneg {W : Type} (q : W → ℕ) (h2 : ∀ w, 2 ≤ q w) {A : Type} [Fintype A]
    (α : W → A → ℂ) (σ : ℝ) : 0 ≤ (∑' p, lterm q α α σ p).re := by
  have e : (fun p => lterm q α α σ p) =
      fun p => ((DiagonalEntryNormBounds.cd α p * Real.exp (-(DiagonalEntryNormBounds.ll q p * σ)) : ℝ) : ℂ) := by
    funext p; exact DiagonalEntryNormBounds.lterm_diag q h2 α σ p
  rw [e, ← Complex.ofReal_tsum, Complex.ofReal_re]
  exact tsum_nonneg fun p => mul_nonneg (DiagonalEntryNormBounds.cd_nonneg α p) (Real.exp_pos _).le

private theorem UpperTheory.V.Z.Tf.SR.sub_part {W : Type} (I : Set W) (f : W × ℕ → ℂ) (hf : Summable f) :
    ∑' p, f p - ∑' p : {p : W × ℕ // p.1 ∈ I}, f p.1 = ∑' p : {p : W × ℕ // ¬ p.1 ∈ I}, f p.1 := by
  have e : ∑' p : {p : W × ℕ // p.1 ∈ I}, f p.1 + ∑' p : {p : W × ℕ // ¬ p.1 ∈ I}, f p.1 = ∑' p, f p :=
    Summable.tsum_subtype_add_tsum_subtype_compl hf {p : W × ℕ | p.1 ∈ I}
  rw [← e]; ring

theorem UpperTheory.V.Z.Tf.SR.absShare :
    LogTwo → CrossUp → PartCS → AbsShare := by
  intro hLog hCross hPart W q X d A hS x I J _ y R C hR hB h
  by_contra hne
  have hne' : ∀ j, x ≠ y j := fun j e => hne ⟨j, e.symm⟩
  have hconv := convergence_of_landau_euler landauL euler_product_log_bound W q X d A hS
  have h2 := hS.primes.two
  have hsum : ∀ (u v : X) (σ : ℝ), 1 < σ → Summable fun p => lterm q (A u) (A v) σ p :=
    fun u v σ hσ => ((hconv u v).1 σ hσ).of_norm
  obtain ⟨C1, hC1⟩ := hLog W q X d A hS x
  have hn : (0 : ℝ) < (Fintype.card J : ℝ) + 1 := by positivity
  have hn1 : (1 : ℝ) ≤ (Fintype.card J : ℝ) + 1 := by
    have : (0 : ℝ) ≤ (Fintype.card J : ℝ) := by positivity
    linarith
  have hR' : 16 * ((Fintype.card J : ℝ) + 1) ^ 2 ≤ (R : ℝ) := by exact_mod_cast hR
  have hR16 : (16 : ℝ) ≤ (R : ℝ) := by nlinarith
  have key : ∀ j, ∃ D : ℝ, ∀ σ : ℝ, 1 < σ → σ ≤ 2 →
      (∑' p, lterm q (A x) (A (y j)) σ p -
        ∑' p : {p : W × ℕ // p.1 ∈ I}, lterm q (A x) (A (y j)) σ p.1).re ≤
        (-Real.log (σ - 1)) / (3 * ((Fintype.card J : ℝ) + 1)) + D := by
    intro j
    obtain ⟨C2, hC2⟩ := hLog W q X d A hS (y j)
    obtain ⟨C3, hC3⟩ := hCross W q X d A hS x (y j) (hne' j)
    refine ⟨C3 + |C2| / (3 * ((Fintype.card J : ℝ) + 1)) + 3 * ((Fintype.card J : ℝ) + 1) * |C| / 2, ?_⟩
    intro σ h1 hσ2
    have hb0 := diag_re_nonneg q h2 (A (y j)) σ
    have hL : 0 ≤ -Real.log (σ - 1) := by
      have := Real.log_nonpos (by linarith : (0 : ℝ) ≤ σ - 1) (by linarith)
      linarith
    have hT : 0 ≤ -Real.log (σ - 1) + |C2| := add_nonneg hL (abs_nonneg _)
    have hb1 : (∑' p, lterm q (A (y j)) (A (y j)) σ p).re ≤ -Real.log (σ - 1) + |C2| := by
      have := abs_le.1 (hC2 σ h1 hσ2)
      have := le_abs_self C2
      linarith
    have hdiv : -Real.log (σ - 1) / (R : ℝ) ≤
        (-Real.log (σ - 1) + |C2|) / (16 * ((Fintype.card J : ℝ) + 1) ^ 2) :=
      div_le_div₀ hT (by linarith [abs_nonneg C2]) (by positivity) hR'
    have ha : (∑' p : {p : W × ℕ // p.1 ∈ I}, lterm q (A x) (A x) σ p.1).re ≤
        (-Real.log (σ - 1) + |C2|) / (16 * ((Fintype.card J : ℝ) + 1) ^ 2) + |C| := by
      have := hB σ h1 hσ2
      have := le_abs_self C
      linarith
    have hP := hPart W q X d A hS x (y j) I σ h1
    have hsq : ‖∑' p : {p : W × ℕ // p.1 ∈ I}, lterm q (A x) (A (y j)) σ p.1‖ ^ 2 ≤
        (-Real.log (σ - 1) + |C2|) ^ 2 / (16 * ((Fintype.card J : ℝ) + 1) ^ 2) +
          |C| * (-Real.log (σ - 1) + |C2|) := by
      refine hP.trans ?_
      have hnn : 0 ≤ (-Real.log (σ - 1) + |C2|) / (16 * ((Fintype.card J : ℝ) + 1) ^ 2) + |C| := by
        positivity
      calc _ ≤ ((-Real.log (σ - 1) + |C2|) / (16 * ((Fintype.card J : ℝ) + 1) ^ 2) + |C|) *
              (∑' p, lterm q (A (y j)) (A (y j)) σ p).re := mul_le_mul_of_nonneg_right ha hb0
        _ ≤ ((-Real.log (σ - 1) + |C2|) / (16 * ((Fintype.card J : ℝ) + 1) ^ 2) + |C|) *
              (-Real.log (σ - 1) + |C2|) := mul_le_mul_of_nonneg_left hb1 hnn
        _ = _ := by ring
    have hlin := le_of_sq_le hn (abs_nonneg C) hT hsq
    have hre := abs_le.1 (Complex.abs_re_le_norm
      (∑' p : {p : W × ℕ // p.1 ∈ I}, lterm q (A x) (A (y j)) σ p.1))
    have hc3 := hC3 σ h1 hσ2
    have e := add_div (-Real.log (σ - 1)) |C2| (3 * ((Fintype.card J : ℝ) + 1))
    rw [Complex.sub_re]
    linarith
  choose D hD using key
  have main : ∀ σ : ℝ, 1 < σ → σ ≤ 2 →
      -Real.log (σ - 1) / 2 ≤ |C1| + |C| + ∑ j, |D j| := by
    intro σ h1 hσ2
    have hL : 0 ≤ -Real.log (σ - 1) := by
      have := Real.log_nonpos (by linarith : (0 : ℝ) ≤ σ - 1) (by linarith)
      linarith
    have hid : ∑' p, lterm q (A x) (A x) σ p - ∑' p : {p : W × ℕ // p.1 ∈ I}, lterm q (A x) (A x) σ p.1 =
        ∑ j, (∑' p, lterm q (A x) (A (y j)) σ p -
          ∑' p : {p : W × ℕ // p.1 ∈ I}, lterm q (A x) (A (y j)) σ p.1) := by
      rw [sub_part I _ (hsum x x σ h1)]
      simp_rw [sub_part I _ (hsum x _ σ h1)]
      have hsj : ∀ j, Summable fun p : {p : W × ℕ // ¬ p.1 ∈ I} => lterm q (A x) (A (y j)) σ p.1 :=
        fun j => (hsum x (y j) σ h1).subtype {p : W × ℕ | ¬ p.1 ∈ I}
      rw [← Summable.tsum_finsetSum (fun j _ => hsj j)]
      refine tsum_congr fun p => ?_
      have hp : (starRingEnd ℂ) (∑ a, A x p.1.1 a ^ (p.1.2 + 1)) =
          ∑ j, (starRingEnd ℂ) (∑ b, A (y j) p.1.1 b ^ (p.1.2 + 1)) := by
        rw [h p.1.1 p.2 (p.1.2 + 1), map_sum]
      simp only [lterm]
      rw [hp, Finset.mul_sum, Finset.sum_mul, Finset.sum_div]
    have hre := congrArg Complex.re hid
    rw [Complex.sub_re, Complex.re_sum] at hre
    have hs : ∑ j, (∑' p, lterm q (A x) (A (y j)) σ p -
        ∑' p : {p : W × ℕ // p.1 ∈ I}, lterm q (A x) (A (y j)) σ p.1).re ≤
        ∑ j : J, ((-Real.log (σ - 1)) / (3 * ((Fintype.card J : ℝ) + 1)) + |D j|) :=
      Finset.sum_le_sum fun j _ => (hD j σ h1 hσ2).trans (by gcongr; exact le_abs_self _)
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hs
    have hcard : (Fintype.card J : ℝ) * (-Real.log (σ - 1) / (3 * ((Fintype.card J : ℝ) + 1))) ≤
        -Real.log (σ - 1) / 3 := by
      rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by norm_num)]
      nlinarith
    have hx := abs_le.1 (hC1 σ h1 hσ2)
    have hc1 := le_abs_self C1
    have hP := hB σ h1 hσ2
    have hb := le_abs_self C
    have hdiv : -Real.log (σ - 1) / (R : ℝ) ≤ -Real.log (σ - 1) / 16 :=
      div_le_div_of_nonneg_left hL (by norm_num) hR16
    linarith
  set K : ℝ := 2 * (|C1| + |C| + ∑ j, |D j|) + 1 with hK
  have hKpos : 0 < K := by
    have : 0 ≤ ∑ j, |D j| := Finset.sum_nonneg fun j _ => abs_nonneg _
    have := abs_nonneg C1
    have := abs_nonneg C
    linarith
  have he : Real.exp (-K) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
  have := main (1 + Real.exp (-K)) (by linarith [Real.exp_pos (-K)]) (by linarith)
  rw [add_sub_cancel_left, Real.log_exp] at this
  linarith
