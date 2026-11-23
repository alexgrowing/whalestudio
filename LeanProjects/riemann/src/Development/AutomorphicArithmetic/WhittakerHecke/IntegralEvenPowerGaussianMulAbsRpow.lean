import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.CharacterNorms.FacDefs
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.RankTwoDescent
open scoped Classical
open UpperTheory.ConvolutionTheory.R2.G (FS2 Rw nE row)
open UpperTheory.V.Af.Smo (EigAt)
open scoped ComplexOrder

private noncomputable def gg (a : ℂ) (r : ℝ) : ℂ :=
  (r : ℂ) ^ (2 * a - 1) * Complex.exp (-(Real.pi : ℂ) * ((r ^ 2 : ℝ) : ℂ))

private theorem gg_int {a : ℂ} (ha : 0 < a.re) : IntegrableOn (gg a) (Set.Ioi 0) ∧
    ∫ r in Set.Ioi (0 : ℝ), gg a r = (Real.pi : ℂ) ^ (-a) * Complex.Gamma a / 2 := by
  let F : ℝ → ℂ := fun t => (t : ℂ) ^ (a - 1) * Complex.exp (-((Real.pi : ℝ) * t))
  have key : ∀ x ∈ Set.Ioi (0 : ℝ), (|(2 : ℝ)| * x ^ ((2 : ℝ) - 1)) • F (x ^ (2 : ℝ)) = 2 * gg a x := fun x hx => by
    have hx' : (0 : ℝ) < x := hx
    have h0 : (x : ℂ) ≠ 0 := by exact_mod_cast hx'.ne'
    have h1 : ((x ^ (2 : ℝ) : ℝ) : ℂ) ^ (a - 1) = (x : ℂ) ^ (2 * (a - 1)) := by
      rw [Real.rpow_two, sq, Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg hx'.le hx'.le, ← Complex.cpow_add _ _ h0]
      congr 1
      ring
    have h2 : (x : ℂ) ^ (2 * a - 1) = x * (x : ℂ) ^ (2 * (a - 1)) := by
      rw [show 2 * a - 1 = 1 + 2 * (a - 1) by ring, Complex.cpow_add _ _ h0, Complex.cpow_one]
    simp only [F, gg, h1, h2, Complex.real_smul]
    rw [show (2 : ℝ) - 1 = 1 by norm_num, Real.rpow_one, Real.rpow_two, abs_two]
    push_cast
    ring_nf
  have hF : IntegrableOn F (Set.Ioi 0) := by
    have h := (integrableOn_Ioi_comp_mul_left_iff (fun t : ℝ => (Real.exp (-t) : ℂ) * (t : ℂ) ^ (a - 1)) 0 Real.pi_pos).2
      (by simpa using Complex.GammaIntegral_convergent ha)
    refine (h.const_mul ((Real.pi : ℂ) ^ (a - 1))⁻¹).congr ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have hp : (Real.pi : ℂ) ^ (a - 1) ≠ 0 := by simp [Complex.cpow_eq_zero_iff, Real.pi_ne_zero]
    simp only [F]
    rw [Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg Real.pi_pos.le (le_of_lt ht)]
    push_cast
    field_simp
  have h1 := (integrableOn_Ioi_comp_rpow_iff F (p := 2) two_ne_zero).2 hF
  have h2 := integral_comp_rpow_Ioi F (p := 2) two_ne_zero
  refine ⟨?_, ?_⟩
  · refine ((h1.congr_fun key measurableSet_Ioi).const_mul (2 : ℂ)⁻¹).congr (ae_of_all _ fun x => ?_)
    simp
  · rw [setIntegral_congr_fun measurableSet_Ioi key, integral_const_mul,
      Complex.integral_cpow_mul_exp_neg_mul_Ioi ha Real.pi_pos] at h2
    rw [eq_div_iff two_ne_zero, mul_comm, h2, Complex.cpow_neg, one_div,
      Complex.inv_cpow _ _ (by rw [Complex.arg_ofReal_of_nonneg Real.pi_pos.le]; exact Real.pi_ne_zero.symm)]

theorem UpperTheory.integral_even_power_gaussian_mul_abs_rpow :
    ∀ (e : ℕ) (s : ℂ), 0 < s.re → Integrable (fun r : ℝ => (r : ℂ) ^ (2 * e) * Complex.exp (-(Real.pi : ℂ) * ((r ^ 2 : ℝ) : ℂ)) * ((|r| : ℝ) : ℂ) ^ (2 * s - 1)) ∧ ∫ r : ℝ, (r : ℂ) ^ (2 * e) * Complex.exp (-(Real.pi : ℂ) * ((r ^ 2 : ℝ) : ℂ)) * ((|r| : ℝ) : ℂ) ^ (2 * s - 1) = (Real.pi : ℂ) ^ (-(s + e)) * Complex.Gamma (s + e) := by
  intro e s hs
  have ha : 0 < (s + e).re := by simp; positivity
  have hf : ∀ r : ℝ, r ≠ 0 → (r : ℂ) ^ (2 * e) * Complex.exp (-(Real.pi : ℂ) * ((r ^ 2 : ℝ) : ℂ)) * ((|r| : ℝ) : ℂ) ^ (2 * s - 1) =
      gg (s + e) |r| := fun r hr => by
    have h1 : ((|r| : ℝ) : ℂ) ≠ 0 := by simpa using hr
    have h2 : (r : ℂ) ^ (2 * e) = ((|r| : ℝ) : ℂ) ^ ((2 * e : ℕ) : ℂ) := by
      rw [Complex.cpow_natCast, ← Complex.ofReal_pow, ← Complex.ofReal_pow, pow_mul, pow_mul, sq_abs]
    rw [h2, gg, mul_right_comm, ← Complex.cpow_add _ _ h1, sq_abs]
    congr 2
    push_cast
    ring
  have hae : (fun r : ℝ => (r : ℂ) ^ (2 * e) * Complex.exp (-(Real.pi : ℂ) * ((r ^ 2 : ℝ) : ℂ)) * ((|r| : ℝ) : ℂ) ^ (2 * s - 1)) =ᵐ[volume]
      fun r => gg (s + e) |r| := by
    filter_upwards [compl_mem_ae_iff.2 (measure_singleton (0 : ℝ))] with r hr using hf r hr
  obtain ⟨hi, hv⟩ := gg_int ha
  have hp : IntegrableOn (fun r => gg (s + e) |r|) (Set.Ioi 0) :=
    hi.congr_fun (fun r hr => by rw [abs_of_pos hr]) measurableSet_Ioi
  have hn : IntegrableOn (fun r => gg (s + e) |r|) (Set.Iic 0) := by
    rw [← Measure.map_neg_eq_self (volume : Measure ℝ)]
    have m : MeasurableEmbedding fun x : ℝ => -x := (Homeomorph.neg ℝ).measurableEmbedding
    rw [m.integrableOn_map_iff]
    simp_rw [Function.comp_def, abs_neg, Set.neg_preimage, Set.neg_Iic, neg_zero]
    exact Iff.mpr integrableOn_Ici_iff_integrableOn_Ioi hp
  have hall : Integrable fun r => gg (s + e) |r| := by
    rw [← integrableOn_univ, ← Set.Iic_union_Ioi (a := (0 : ℝ))]
    exact hn.union hp
  refine ⟨hall.congr hae.symm, ?_⟩
  have e1 : ∫ r in Set.Ioi (0 : ℝ), gg (s + e) |r| = ∫ r in Set.Ioi (0 : ℝ), gg (s + e) r :=
    setIntegral_congr_fun measurableSet_Ioi fun r hr => by rw [abs_of_pos hr]
  have e2 : ∫ r in Set.Iic (0 : ℝ), gg (s + e) |r| = ∫ r in Set.Ioi (0 : ℝ), gg (s + e) |r| := by
    rw [← neg_zero, ← integral_comp_neg_Iic]
    simp
  rw [integral_congr_ae hae, ← intervalIntegral.integral_Iic_add_Ioi hn hp, e2, e1, hv]
  ring
