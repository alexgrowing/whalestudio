import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.UnfoldedThetaIntegralConvergesSimilitudeOne

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Ff
open scoped Classical

private theorem abs_le_of_continuous_add {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (f : V →+ ℝ) (hf : Continuous f) : ∃ B : ℝ, 0 ≤ B ∧ ∀ z, |f z| ≤ B * ‖z‖ := by
  refine ⟨‖f.toRealLinearMap hf‖, norm_nonneg _, fun z => ?_⟩
  have h := (f.toRealLinearMap hf).le_opNorm z
  simpa using h

private noncomputable def eU {E : Type} [Field E] [NumberField E] (z : InfinitePlace E → ℂ) : (Cinf E)ˣ where
  val := fun w => Complex.exp (z w)
  inv := fun w => Complex.exp (-z w)
  val_inv := by
    funext w
    change Complex.exp (z w) * Complex.exp (-z w) = 1
    rw [← Complex.exp_add, add_neg_cancel, Complex.exp_zero]
  inv_val := by
    funext w
    change Complex.exp (-z w) * Complex.exp (z w) = 1
    rw [← Complex.exp_add, neg_add_cancel, Complex.exp_zero]

private theorem continuous_eU {E : Type} [Field E] [NumberField E] :
    Continuous (eU (E := E)) := by
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · exact continuous_pi fun w => Complex.continuous_exp.comp (continuous_apply w)
  · exact continuous_pi fun w => Complex.continuous_exp.comp (continuous_apply w).neg

private theorem eU_add {E : Type} [Field E] [NumberField E] (z z' : InfinitePlace E → ℂ) :
    eU (z + z') = eU z * eU z' := by
  refine Units.ext ?_
  funext w
  change Complex.exp (z w + z' w) = Complex.exp (z w) * Complex.exp (z' w)
  rw [Complex.exp_add]

private theorem eU_log {E : Type} [Field E] [NumberField E] (s : (Cinf E)ˣ) :
    eU (fun w => Complex.log (s.val w)) = s := by
  refine Units.ext ?_
  funext w
  have h : s.val w * s⁻¹.val w = 1 := congrFun s.mul_inv w
  have h0 : s.val w ≠ 0 := left_ne_zero_of_mul_eq_one h
  change Complex.exp (Complex.log (s.val w)) = s.val w
  exact Complex.exp_log h0

private theorem norm_log_le {E : Type} [Field E] [NumberField E] (s : (Cinf E)ˣ) (w : InfinitePlace E) :
    ‖Complex.log (s.val w)‖ ≤ Real.log (1 + ‖s.val‖ + ‖s⁻¹.val‖) + Real.pi := by
  have h : s.val w * s⁻¹.val w = 1 := congrFun s.mul_inv w
  have h0 : s.val w ≠ 0 := left_ne_zero_of_mul_eq_one h
  have h1 : s⁻¹.val w ≠ 0 := right_ne_zero_of_mul_eq_one h
  have p0 : 0 < ‖s.val w‖ := norm_pos_iff.2 h0
  have p1 : 0 < ‖s⁻¹.val w‖ := norm_pos_iff.2 h1
  have hprod : ‖s.val w‖ * ‖s⁻¹.val w‖ = 1 := by rw [← norm_mul, h, norm_one]
  have b0 : ‖s.val w‖ ≤ ‖s.val‖ := norm_le_pi_norm s.val w
  have b1 : ‖s⁻¹.val w‖ ≤ ‖s⁻¹.val‖ := norm_le_pi_norm s⁻¹.val w
  have n0 : 0 ≤ ‖s.val‖ := norm_nonneg _
  have n1 : 0 ≤ ‖s⁻¹.val‖ := norm_nonneg _
  have l0 : Real.log ‖s.val w‖ ≤ Real.log (1 + ‖s.val‖ + ‖s⁻¹.val‖) :=
    Real.log_le_log p0 (by linarith)
  have l1 : Real.log ‖s⁻¹.val w‖ ≤ Real.log (1 + ‖s.val‖ + ‖s⁻¹.val‖) :=
    Real.log_le_log p1 (by linarith)
  have hs : Real.log ‖s.val w‖ + Real.log ‖s⁻¹.val w‖ = 0 := by
    rw [← Real.log_mul p0.ne' p1.ne', hprod, Real.log_one]
  have hre : |(Complex.log (s.val w)).re| ≤ Real.log (1 + ‖s.val‖ + ‖s⁻¹.val‖) := by
    rw [Complex.log_re, abs_le]
    constructor <;> linarith
  have him : |(Complex.log (s.val w)).im| ≤ Real.pi := by
    rw [Complex.log_im]
    exact Complex.abs_arg_le_pi _
  exact (Complex.norm_le_abs_re_add_abs_im _).trans (add_le_add hre him)

theorem UpperTheory.ConvolutionTheory.R2.Ff.omGrowth :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [IsTotallyComplex E] (_D : Dat F E), OmGrowth F E := by
  intro F E _ _ _ _ _ _ _ _D
  have hN : Continuous (fun s : (Cinf E)ˣ => ideleNorm F E (infId E s)) :=
    continuous_ideleNorm.comp (continuous_infId E)
  refine ⟨hN, fun ω hω => ?_⟩
  let c : (Cinf E)ˣ → ℝ := fun s => ‖((ω (ideleNorm F E (infId E s)) : ℂˣ) : ℂ)‖
  have hc : Continuous c := (Units.continuous_val.comp (hω.comp hN)).norm
  have hpos : ∀ s, 0 < c s := fun s => norm_pos_iff.2 (Units.ne_zero _)
  have hmul : ∀ s s', c (s * s') = c s * c s' := by
    intro s s'
    simp only [c, map_mul, Units.val_mul, norm_mul]
  let f : (InfinitePlace E → ℂ) →+ ℝ :=
    { toFun := fun z => Real.log (c (eU z))
      map_zero' := by
        have h1 : eU (0 : InfinitePlace E → ℂ) = 1 := by
          have := eU_add (0 : InfinitePlace E → ℂ) 0
          rw [add_zero] at this
          exact left_eq_mul.1 this
        have h2 : c 1 = 1 := by simp [c]
        change Real.log (c (eU 0)) = 0
        rw [h1, h2, Real.log_one]
      map_add' := fun z z' => by
        change Real.log (c (eU (z + z'))) = Real.log (c (eU z)) + Real.log (c (eU z'))
        rw [eU_add, hmul, Real.log_mul (hpos _).ne' (hpos _).ne'] }
  have hf : Continuous f :=
    (hc.comp continuous_eU).log fun z => (hpos _).ne'
  obtain ⟨B, hB0, hB⟩ := abs_le_of_continuous_add f hf
  refine ⟨Real.exp (B * Real.pi), ⌈B⌉₊, fun s => ?_⟩
  change c s ≤ _
  set H : ℝ := 1 + ‖s.val‖ + ‖s⁻¹.val‖ with hH
  have hH1 : 1 ≤ H := by
    have n0 : 0 ≤ ‖s.val‖ := norm_nonneg _
    have n1 : 0 ≤ ‖s⁻¹.val‖ := norm_nonneg _
    linarith
  have hH0 : 0 < H := by linarith
  have hL : 0 ≤ Real.log H := Real.log_nonneg hH1
  let z : InfinitePlace E → ℂ := fun w => Complex.log (s.val w)
  have hz : ‖z‖ ≤ Real.log H + Real.pi :=
    (pi_norm_le_iff_of_nonneg (by positivity)).2 fun w => norm_log_le s w
  have hfz : f z = Real.log (c s) := by
    change Real.log (c (eU z)) = _
    rw [eU_log]
  have h1 : Real.log (c s) ≤ B * (Real.log H + Real.pi) := by
    rw [← hfz]
    exact (le_abs_self _).trans ((hB z).trans (mul_le_mul_of_nonneg_left hz hB0))
  have h2 : B * (Real.log H + Real.pi) ≤ B * Real.pi + (⌈B⌉₊ : ℝ) * Real.log H := by
    have : B * Real.log H ≤ (⌈B⌉₊ : ℝ) * Real.log H :=
      mul_le_mul_of_nonneg_right (Nat.le_ceil B) hL
    linarith
  calc c s = Real.exp (Real.log (c s)) := (Real.exp_log (hpos s)).symm
    _ ≤ Real.exp (B * Real.pi + (⌈B⌉₊ : ℝ) * Real.log H) := Real.exp_le_exp.2 (h1.trans h2)
    _ = Real.exp (B * Real.pi) * H ^ ⌈B⌉₊ := by
      rw [Real.exp_add, Real.exp_nat_mul, Real.exp_log hH0]
