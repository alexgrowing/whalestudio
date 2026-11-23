import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GL1SpectralBounds.IntegralityGoodReduction
import Development.WeilBound.RepresentationTheoryGL.JacquetShalikaBounds.AbsoluteRigidity.DiagonalTermNorms.ConvergenceOfLandauEuler
import Development.WeilBound.RepresentationTheoryGL.JacquetShalikaBounds.AbsoluteRigidity.LandauIteratedDerivatives.LandauL
import Development.WeilBound.RepresentationTheoryGL.JacquetShalikaBounds.AbsoluteRigidity.EulerLogarithms.EulerProductLogBound

open PositivityTheory.RgJS UpperTheory.V.Z.Tf.GOne

private theorem tsum_cs {ι : Type} (f a b : ι → ℝ) (hf0 : ∀ i, 0 ≤ f i) (ha0 : ∀ i, 0 ≤ a i) (hb0 : ∀ i, 0 ≤ b i)
    (h : ∀ i, f i ^ 2 = a i * b i) (ha : Summable a) (hb : Summable b) :
    (∑' i, f i) ^ 2 ≤ (∑' i, a i) * ∑' i, b i := by
  have hA : 0 ≤ ∑' i, a i := tsum_nonneg ha0
  have hB : 0 ≤ ∑' i, b i := tsum_nonneg hb0
  have key : ∑' i, f i ≤ Real.sqrt ((∑' i, a i) * ∑' i, b i) := by
    apply Real.tsum_le_of_sum_le hf0
    intro s
    apply Real.le_sqrt_of_sq_le
    have h1 : (∑ i ∈ s, f i) ^ 2 ≤ (∑ i ∈ s, a i) * ∑ i ∈ s, b i :=
      Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul s (fun i _ => ha0 i) (fun i _ => hb0 i) (fun i _ => (h i).le)
    refine h1.trans ?_
    exact mul_le_mul (ha.sum_le_tsum s fun i _ => ha0 i) (hb.sum_le_tsum s fun i _ => hb0 i)
      (Finset.sum_nonneg fun i _ => hb0 i) hA
  calc (∑' i, f i) ^ 2 ≤ (Real.sqrt ((∑' i, a i) * ∑' i, b i)) ^ 2 :=
        pow_le_pow_left₀ (tsum_nonneg hf0) key 2
    _ = _ := Real.sq_sqrt (mul_nonneg hA hB)

open DiagonalEntryNormBounds in
private theorem norm_lterm_sq {W A B : Type} [Fintype A] [Fintype B] (q : W → ℕ) (hq : ∀ w, 2 ≤ q w)
    (α : W → A → ℂ) (β : W → B → ℂ) (σ : ℝ) (p : W × ℕ) :
    ‖lterm q α β σ p‖ ^ 2 = ‖lterm q α α σ p‖ * ‖lterm q β β σ p‖ := by
  rw [norm_lterm q hq, norm_lterm q hq, norm_lterm q hq]
  ring

open DiagonalEntryNormBounds in
private theorem lterm_diag_norm {W A : Type} [Fintype A] (q : W → ℕ) (hq : ∀ w, 2 ≤ q w)
    (α : W → A → ℂ) (σ : ℝ) (p : W × ℕ) :
    lterm q α α σ p = ((‖lterm q α α σ p‖ : ℝ) : ℂ) := by
  rw [norm_lterm_diag q hq, lterm_diag q hq]

theorem UpperTheory.V.Z.Tf.GOne.partCS :
    PartCS := by
  intro W q X d A hS x y I σ hσ
  have hq := hS.primes.two
  have hc := convergence_of_landau_euler landauL euler_product_log_bound W q X d A hS
  have hxy := (hc x y).1 σ hσ
  have hxx := (hc x x).1 σ hσ
  have hyy := (hc y y).1 σ hσ
  have sxy : Summable fun p : {p : W × ℕ // p.1 ∈ I} => ‖lterm q (A x) (A y) σ p.1‖ := hxy.subtype _
  have sxx : Summable fun p : {p : W × ℕ // p.1 ∈ I} => ‖lterm q (A x) (A x) σ p.1‖ := hxx.subtype _
  have syy : Summable fun p : {p : W × ℕ // p.1 ∈ I} => ‖lterm q (A y) (A y) σ p.1‖ := hyy.subtype _
  have e1 : (∑' p : {p : W × ℕ // p.1 ∈ I}, lterm q (A x) (A x) σ p.1).re =
      ∑' p : {p : W × ℕ // p.1 ∈ I}, ‖lterm q (A x) (A x) σ p.1‖ := by
    rw [tsum_congr fun p : {p : W × ℕ // p.1 ∈ I} => lterm_diag_norm q hq (A x) σ p.1, ← Complex.ofReal_tsum,
      Complex.ofReal_re]
  have e2 : (∑' p, lterm q (A y) (A y) σ p).re = ∑' p, ‖lterm q (A y) (A y) σ p‖ := by
    rw [tsum_congr fun p => lterm_diag_norm q hq (A y) σ p, ← Complex.ofReal_tsum, Complex.ofReal_re]
  rw [e1, e2]
  have h1 := norm_tsum_le_tsum_norm sxy
  have h2 := tsum_cs _ _ _ (fun _ => norm_nonneg _) (fun _ => norm_nonneg _) (fun _ => norm_nonneg _)
    (fun p : {p : W × ℕ // p.1 ∈ I} => norm_lterm_sq q hq (A x) (A y) σ p.1) sxx syy
  have h3 : ∑' p : {p : W × ℕ // p.1 ∈ I}, ‖lterm q (A y) (A y) σ p.1‖ ≤ ∑' p, ‖lterm q (A y) (A y) σ p‖ :=
    Summable.tsum_le_tsum_of_inj Subtype.val Subtype.val_injective (fun _ _ => norm_nonneg _) (fun _ => le_rfl)
      syy hyy
  refine (pow_le_pow_left₀ (norm_nonneg _) h1 2).trans (h2.trans ?_)
  exact mul_le_mul_of_nonneg_left h3 (tsum_nonneg fun _ => norm_nonneg _)
