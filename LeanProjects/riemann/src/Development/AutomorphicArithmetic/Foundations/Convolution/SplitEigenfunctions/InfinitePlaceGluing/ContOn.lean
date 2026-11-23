import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.CharacterNorms.NzCont
import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.CharacterNorms.TrTranslate
import Development.AutomorphicArithmetic.WhittakerHecke.EqZeroOfOrthogonalEvenHomogeneousTrig
import Development.AutomorphicArithmetic.WhittakerHecke.EqZeroAtOneOfFourierIntegralEqZero
import Development.AutomorphicArithmetic.WhittakerHecke.IntegrableAndContinuousMellinIntegralOfRapidDeca

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2
open scoped Classical
open UpperTheory.ConvolutionTheory.R2.G (FS2 Rw nE row)
open UpperTheory.ConvolutionTheory.RankTwoDescent UpperTheory.ConvolutionTheory.RankTwoDescent.Nz

private theorem X_two_pi (t : ℝ) : X (t + 2 * Real.pi) = X t := by
  refine Units.ext ?_
  ext i j w
  fin_cases i <;> fin_cases j <;> simp [X, Real.cos_add_two_pi, Real.sin_add_two_pi]

private theorem rot_per : Function.Periodic rot (2 * Real.pi) := fun t => by
  rw [rot_eq, rot_eq, X_two_pi]

section

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E]

private theorem dec_of {D : Dat ℚ E} {ω : HChar ℚ} {φ : GL (Fin 2) (A E) → ℂ} (h : admitted D ω φ) (r : ℕ) :
    ∃ B : ℝ, ∀ y t, y ≠ 0 → ‖Wo D φ (em E (aE (iy y) * rot t))‖ ≤ B * ((1 + |y|) ^ r)⁻¹ := by
  have hC : IsCompact (Set.range fun t => em E (rot t)) :=
    Function.Periodic.compact_of_continuous (c := 2 * Real.pi)
      (fun t => by simp only [rot_per t]) (by positivity) (cont_em.comp cont_rot)
  obtain ⟨K, -, hK⟩ := h.wdec _ hC
  obtain ⟨B, hB⟩ := hK r
  refine ⟨B, fun y t hy => ?_⟩
  have h1 := (hB (iy y) (em E (rot t)) ⟨t, rfl⟩).1
  rwa [re_iy hy, ← map_mul] at h1

private theorem pack {D : Dat ℚ E} {ω χ : HChar ℚ} {φ : GL (Fin 2) (A E) → ℂ} (h : admitted D ω φ)
    (hχ : ∀ a, ‖((χ.1 a : ℂˣ) : ℂ)‖ = 1) (k : ℕ) {s : ℂ} (hs : 1 - (k : ℝ) < s.re) :
    (∀ t, Integrable fun y : ℝ => Wo D φ (em E (aE (iy y) * rot t)) * ((χ.1 (iy y) : ℂˣ) : ℂ) * (y : ℂ) ^ k * ((|y| : ℝ) : ℂ) ^ (s - 2)) ∧
    Continuous fun t => ∫ y : ℝ, Wo D φ (em E (aE (iy y) * rot t)) * ((χ.1 (iy y) : ℂˣ) : ℂ) * (y : ℂ) ^ k * ((|y| : ℝ) : ℂ) ^ (s - 2) :=
  UpperTheory.integrable_and_continuous_mellinIntegral_of_rapidDecay (fun y t => Wo D φ (em E (aE (iy y) * rot t))) (fun y => ((χ.1 (iy y) : ℂˣ) : ℂ)) k s
    (contOn_Wo D h.cont h.bdd) ((Units.continuous_val.comp χ.2.1).comp_continuousOn contOn_iy) (fun y => hχ _)
    (dec_of h) hs

private theorem zero_of {D : Dat ℚ E} {ω χ : HChar ℚ} {φ : GL (Fin 2) (A E) → ℂ} (h : admitted D ω φ)
    (hχ : ∀ a, ‖((χ.1 a : ℂˣ) : ℂ)‖ = 1) (k : ℕ) {s : ℂ} (hs : 1 - (k : ℝ) < s.re)
    (hM : ∀ (e : ℕ) (p : MvPolynomial (Fin 2) ℂ), p.IsHomogeneous (2 * e) → Mk D χ k φ p s = 0) :
    ∫ y : ℝ, Wo D φ (em E (aE (iy y))) * ((χ.1 (iy y) : ℂˣ) : ℂ) * (y : ℂ) ^ k * ((|y| : ℝ) : ℂ) ^ (s - 2) = 0 := by
  have h0 := UpperTheory.eq_zero_of_orthogonal_even_homogeneous_trig _ (pack h hχ k hs).2
    (fun t => by simp only [Wo_rot_pi D ω h.cen]) hM 0
  simpa only [rot_zero, mul_one] using h0

private theorem unit_of {ω χ : HChar ℚ} (hω : Unit1 ω) (hχ : ∀ a, (χ.1 a * ω.1 a) ^ 2 = 1) (a : IdeleGroup ℚ) :
    ‖((χ.1 a : ℂˣ) : ℂ)‖ = 1 := by
  have h1 := congrArg (fun z : ℂˣ => ‖(z : ℂ)‖) (hχ a)
  simp only [Units.val_pow_eq_pow_val, Units.val_mul, norm_pow, norm_mul, hω a, mul_one, Units.val_one, norm_one] at h1
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).1 h1

private theorem contOn_chi (χ : HChar ℚ) : ContinuousOn (fun y : ℝ => ((χ.1 (iy y) : ℂˣ) : ℂ)) ({0}ᶜ : Set ℝ) :=
  (Units.continuous_val.comp χ.2.1).comp_continuousOn contOn_iy

private theorem continuousOn_wo_compl_zero_of_adm {D : Dat ℚ E} {ω : HChar ℚ} {φ : GL (Fin 2) (A E) → ℂ} (hA : admitted D ω φ) :
    ContinuousOn (fun y : ℝ => Wo D φ (em E (aE (iy y)))) ({0}ᶜ : Set ℝ) := by
  rw [continuousOn_iff_continuous_restrict]
  refine cont_Wo D hA.cont hA.bdd (c := fun y : ({0}ᶜ : Set ℝ) => em E (aE (iy y))) ?_
  exact continuousOn_iff_continuous_restrict.1 (cont_em.comp_continuousOn (continuous_aE.comp_continuousOn contOn_iy))

private noncomputable def GG (D : Dat ℚ E) (χ : HChar ℚ) (k : ℕ) (s : ℂ) (φ : GL (Fin 2) (A E) → ℂ) (y : ℝ) : ℂ :=
  Wo D φ (em E (aE (iy y))) * ((χ.1 (iy y) : ℂˣ) : ℂ) * (y : ℂ) ^ k * ((|y| : ℝ) : ℂ) ^ (s - 2)

private theorem GG_int {D : Dat ℚ E} {ω χ : HChar ℚ} {φ : GL (Fin 2) (A E) → ℂ} (hA : admitted D ω φ)
    (hχ : ∀ a, ‖((χ.1 a : ℂˣ) : ℂ)‖ = 1) (k : ℕ) {s : ℂ} (hs : 1 - (k : ℝ) < s.re) : Integrable (GG D χ k s φ) := by
  have h := (pack hA hχ k hs).1 0
  simp only [rot_zero, mul_one] at h
  exact h

private theorem GG_cont {D : Dat ℚ E} {ω : HChar ℚ} (χ : HChar ℚ) {φ : GL (Fin 2) (A E) → ℂ} (hA : admitted D ω φ) (k : ℕ) (s : ℂ) :
    ContinuousAt (GG D χ k s φ) 1 := by
  have hne : ({0}ᶜ : Set ℝ) ∈ 𝓝 (1 : ℝ) := isOpen_compl_singleton.mem_nhds (by simp)
  have h1 := (continuousOn_wo_compl_zero_of_adm hA).continuousAt hne
  have h4 := (contOn_chi χ).continuousAt hne
  have h5 : ContinuousAt (fun y : ℝ => ((|y| : ℝ) : ℂ) ^ (s - 2)) 1 := by
    refine ContinuousAt.cpow (by fun_prop) continuousAt_const ?_
    simp
  have h6 : ContinuousAt (fun y : ℝ => (y : ℂ) ^ k) 1 := by fun_prop
  exact ((h1.mul h4).mul h6).mul h5

private theorem GG_four {D : Dat ℚ E} {φ : GL (Fin 2) (A E) → ℂ} (χ : HChar ℚ) (hL : ∀ γ g, φ (ratGL E 2 γ * g) = φ g) (k : ℕ) (s : ℂ) (u : ℝ) :
    ∫ y : ℝ, GG D χ k s φ y * Complex.exp (2 * Real.pi * Complex.I * ((y * u : ℝ) : ℂ)) =
      ∫ y : ℝ, GG D χ k s (fun g => φ (g * hU D u)) y := by
  refine integral_congr_ae ?_
  have hae : ∀ᵐ y : ℝ, y ≠ 0 := compl_mem_ae_iff.2 (measure_singleton 0)
  filter_upwards [hae] with y hy
  simp only [GG]
  rw [Wo_hU D hL hy u]
  ring

private theorem GG_one (D : Dat ℚ E) (χ : HChar ℚ) (k : ℕ) (s : ℂ) (φ : GL (Fin 2) (A E) → ℂ) : GG D χ k s φ 1 = Wo D φ 1 := by
  simp [GG, iy_one]

end

theorem UpperTheory.ConvolutionTheory.RankTwoDescent.nonZ_of :
    NonZ := by
  intro E _ _ _ D P ω χ hcen hω hχ hAll L N φ hG hW k s hs
  by_contra hcon
  push_neg at hcon
  have hχ1 := unit_of hω hχ
  have hA : admitted D ω φ := hAll φ hG.mem
  have hzero : ∀ u : ℝ, ∫ y : ℝ, GG D χ k s φ y * Complex.exp (2 * Real.pi * Complex.I * ((y * u : ℝ) : ℂ)) = 0 := by
    intro u
    have hGu := Gd_translate hG u
    rw [GG_four χ hA.left]
    exact zero_of (hAll _ hGu.mem) hχ1 k hs fun e p hp => hcon _ e p hGu hp
  have h1 := UpperTheory.eq_zero_at_one_of_fourierIntegral_eq_zero _ (GG_int hA hχ1 k hs) (GG_cont χ hA k s) hzero
  exact hW ((GG_one D χ k s φ).symm.trans h1)
