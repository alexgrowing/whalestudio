import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.Entire
import Development.AutomorphicArithmetic.WhittakerHecke.WhittakerPeriodAddSmulAndNormLe
import Development.AutomorphicArithmetic.WhittakerHecke.HasDerivAtWhittakerPeriodOneParameter
import Development.AutomorphicArithmetic.WhittakerHecke.ArchimedeanConjugateCurveOneParameterSubgroup
import Development.AutomorphicArithmetic.WhittakerHecke.WhittakerCoeffLieDerivUnipotentEqMul
import Development.AutomorphicArithmetic.WhittakerHecke.ExistsSmoothLieActionMemCuspidalTranslates
import Development.AutomorphicArithmetic.WhittakerHecke.LieActionPreservesFixedAtPlace
import Development.AutomorphicArithmetic.WhittakerHecke.LieActionPreservesSatakeEigenAtPlace
import Development.AutomorphicArithmetic.WhittakerHecke.LieActionPreservesRightInvarianceFiniteAdelic
import Development.AutomorphicArithmetic.WhittakerHecke.ConjLieElementEmbedRotationEqTrigMatrix

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.RankTwoDescent UpperTheory.ConvolutionTheory.RankTwoDescent.TA
open UpperTheory.ConvolutionTheory.R2.G (FS2 nE)
open scoped Classical

noncomputable section

namespace UpperTheory.ConvolutionTheory.RankTwoDescent.SH

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E]

private theorem re_iy (y : ℝ) (hy : y ≠ 0) : re ((iy y : (A ℚ)ˣ) : A ℚ) = y := by
  have h : iy y = TR.infId ℚ ⟨fun _ => y, fun _ => y⁻¹, funext fun _ => mul_inv_cancel₀ hy, funext fun _ => inv_mul_cancel₀ hy⟩ := dif_neg hy
  have h2 : ∀ x, TR.pInf ℚ (TR.sInf ℚ x) = x := fun x => (TR.infEq ℚ).symm_apply_apply x
  rw [h, re]
  change TR.pInf ℚ (1 - TR.sInf ℚ 1 + TR.sInf ℚ (fun _ => y)) _ = y
  simp [h2]

private def Q (D : Dat ℚ E) (L N : ℕ) (f : Sm E 2) (X : Lie E 2) : Prop :=
  (∀ (y : (A ℚ)ˣ) x, Wo D (lie E 2 X f).1 (em E (aE y) * infGL E 2 x) ≠ 0 → ∀ v, Bad N v → Dv L v ((y : A ℚ) - 1)) ∧
  ∀ t ∈ UU, (∀ v, Dv L v ((t : A ℚ) - 1)) → ∀ (y : (A ℚ)ˣ) x,
    Wo D (lie E 2 X f).1 (em E (aE (y * t)) * infGL E 2 x) = Wo D (lie E 2 X f).1 (em E (aE y) * infGL E 2 x)

private theorem eig_smul {w : H.P E} {B : Multiset ℂˣ} {f : GL (Fin 2) (A E) → ℂ} (c : ℂ)
    (h : UpperTheory.V.Af.Smo.EigAt w B f) : UpperTheory.V.Af.Smo.EigAt w B (c • f) := fun g => by
  have h0 := h g
  refine ⟨h0.card, fun g' k hk => ?_, fun ϖ hϖ j hj g' => ?_⟩
  · simpa using congrArg (c * ·) (h0.inv g' k hk)
  · have h1 := h0.eig ϖ hϖ j hj g'
    simp only [Pi.smul_apply, smul_eq_mul] at h1 ⊢
    rw [mul_left_comm, ← h1, ← smul_eq_mul, smul_finsum]
    exact finsum_congr fun x => by rw [smul_eq_mul, mul_left_comm]

private theorem gd_smul {D : Dat ℚ E} {P : CuspSub E 2} {L N : ℕ} {f : Sm E 2} {X : Lie E 2} {c : ℂ}
    (hG : Gd D P L N f.1) (hm : (lie E 2 X f).1 ∈ Tr P) (hQ : Q D L N f X) :
    Gd D P L N (c • (lie E 2 X f).1) := by
  have hs : ∀ h, Wo D (c • (lie E 2 X f).1) h = c * Wo D (lie E 2 X f).1 h := fun h => (UpperTheory.whittakerPeriod_add_smul_and_norm_le E D).2.1 c _ h
  refine ⟨hG.pos, hG.dvd, hG.same, (Tr P).smul_mem c hm, hG.pl, fun w hw => ?_, fun k hk g => ?_, fun y x hne => ?_, fun t ht hL y x => ?_⟩
  · obtain ⟨h1, B, h2, h3⟩ := hG.fix w hw
    refine ⟨fun g k hk => ?_, B, h2, eig_smul c (UpperTheory.lie_action_preserves_satake_eigen_at_place E w B f X h3)⟩
    simpa using congrArg (c * ·) (UpperTheory.lie_action_preserves_fixed_at_place E w f X h1 g k hk)
  · have := UpperTheory.lie_action_preserves_right_invariance_finite_adelic E k hk.1 f X (hG.lev k hk) g
    simpa using congrArg (c * ·) this
  · rw [hs] at hne
    exact hQ.1 y x (right_ne_zero_of_mul hne)
  · rw [hs, hs, hQ.2 t ht hL y x]

private theorem q_cv {D : Dat ℚ E} {P : CuspSub E 2} {L N : ℕ} {f : Sm E 2} (k : GL (Fin 2) (A E))
    (hG : Gd D P L N f.1) (hc : Continuous f.1) (hX : Continuous (lie E 2 (toL (XB D k)) f).1)
    (hB : ∃ B : ℝ, ∀ g, ‖(lie E 2 (toL (XB D k)) f).1 g‖ ≤ B) : Q D L N f (toL (XB D k)) := by
  obtain ⟨h0, hadd, hd, -⟩ := UpperTheory.archimedeanConjugateCurve_oneParameterSubgroup E D k
  have key : ∀ g, HasDerivAt (fun t : ℝ => Wo D f.1 (g * infGL E 2 (cv D k t)))
      (Wo D (lie E 2 (toL (XB D k)) f).1 g) 0 := fun g =>
    UpperTheory.hasDerivAt_whittakerPeriod_oneParameter E D f (cv D k) _ g h0 hadd hd hc hX hB
  refine ⟨fun y x hne v hv => ?_, fun t ht hL y x => ?_⟩
  · by_contra hcon
    have hz : (fun s : ℝ => Wo D f.1 (em E (aE y) * infGL E 2 x * infGL E 2 (cv D k s))) = fun _ => 0 := funext fun s => by
      by_contra h1
      rw [mul_assoc, ← map_mul] at h1
      exact hcon (hG.supp y _ h1 v hv)
    have h2 := key (em E (aE y) * infGL E 2 x)
    rw [hz] at h2
    exact hne (h2.unique (hasDerivAt_const _ _))
  · have h1 := key (em E (aE (y * t)) * infGL E 2 x)
    have h2 := key (em E (aE y) * infGL E 2 x)
    have e : (fun s : ℝ => Wo D f.1 (em E (aE (y * t)) * infGL E 2 x * infGL E 2 (cv D k s))) =
        fun s : ℝ => Wo D f.1 (em E (aE y) * infGL E 2 x * infGL E 2 (cv D k s)) := funext fun s => by
      rw [mul_assoc, mul_assoc, ← map_mul, hG.tor t ht hL y]
    rw [e] at h1
    exact h1.unique h2

private theorem lieDerivative_linear (f : Sm E 2) (a b c : ℝ) (X Y Z : Lie E 2) :
    (lie E 2 (a • X + b • Y + c • Z) f).1 = (a : ℂ) • (lie E 2 X f).1 + (b : ℂ) • (lie E 2 Y f).1 + (c : ℂ) • (lie E 2 Z f).1 := by
  rw [map_add, map_add, map_smul, map_smul, map_smul]
  funext g
  simp

private theorem whittaker_lieDerivative_linear {D : Dat ℚ E} {f : Sm E 2} (hc : ∀ X, Continuous (lie E 2 X f).1) (a b c : ℝ) (X Y Z : Lie E 2)
    (h : GL (Fin 2) (A E)) :
    Wo D (lie E 2 (a • X + b • Y + c • Z) f).1 h = a * Wo D (lie E 2 X f).1 h + b * Wo D (lie E 2 Y f).1 h + c * Wo D (lie E 2 Z f).1 h := by
  obtain ⟨h1, h2, -⟩ := UpperTheory.whittakerPeriod_add_smul_and_norm_le E D
  rw [lieDerivative_linear, h1 _ _ (((hc X).const_smul _).add ((hc Y).const_smul _)) ((hc Z).const_smul _),
    h1 _ _ ((hc X).const_smul _) ((hc Y).const_smul _), h2, h2, h2]

private theorem quadraticCondition_linear {D : Dat ℚ E} {L N : ℕ} {f : Sm E 2} (hc : ∀ X, Continuous (lie E 2 X f).1) (a b c : ℝ) {X Y Z : Lie E 2}
    (hX : Q D L N f X) (hY : Q D L N f Y) (hZ : Q D L N f Z) : Q D L N f (a • X + b • Y + c • Z) := by
  refine ⟨fun y x hne v hv => ?_, fun t ht hL y x => ?_⟩
  · rw [whittaker_lieDerivative_linear hc] at hne
    by_contra hcon
    have h1 : Wo D (lie E 2 X f).1 (em E (aE y) * infGL E 2 x) = 0 := by
      by_contra h; exact hcon (hX.1 y x h v hv)
    have h2 : Wo D (lie E 2 Y f).1 (em E (aE y) * infGL E 2 x) = 0 := by
      by_contra h; exact hcon (hY.1 y x h v hv)
    have h3 : Wo D (lie E 2 Z f).1 (em E (aE y) * infGL E 2 x) = 0 := by
      by_contra h; exact hcon (hZ.1 y x h v hv)
    exact hne (by rw [h1, h2, h3]; ring)
  · rw [whittaker_lieDerivative_linear hc, whittaker_lieDerivative_linear hc, hX.2 t ht hL y x, hY.2 t ht hL y x, hZ.2 t ht hL y x]

private theorem xb_dec (D : Dat ℚ E) (t : ℝ) :
    toL (XB D (em E (rot t))) = (Real.cos t ^ 2) • toL (XB D (em E (rot 0))) + (Real.sin t ^ 2) • toL (XB D (em E (rot (Real.pi / 2)))) +
      (Real.cos t * Real.sin t) • ((2 : ℝ) • toL (XB D (em E (rot (Real.pi / 4)))) + (-1 : ℝ) • toL (XB D (em E (rot 0))) +
        (-1 : ℝ) • toL (XB D (em E (rot (Real.pi / 2))))) := by
  have c4 : Real.cos (Real.pi / 4) ^ 2 = 1 / 2 := by
    rw [Real.cos_pi_div_four, div_pow, Real.sq_sqrt (by norm_num)]; norm_num
  have s4 : Real.sin (Real.pi / 4) ^ 2 = 1 / 2 := by
    rw [Real.sin_pi_div_four, div_pow, Real.sq_sqrt (by norm_num)]; norm_num
  have m4 : Real.cos (Real.pi / 4) * Real.sin (Real.pi / 4) = 1 / 2 := by
    rw [Real.sin_pi_div_four, Real.cos_pi_div_four, ← pow_two, div_pow, Real.sq_sqrt (by norm_num)]; norm_num
  rw [UpperTheory.conj_lie_element_embed_rotation_eq_trig_matrix E D t, UpperTheory.conj_lie_element_embed_rotation_eq_trig_matrix E D 0, UpperTheory.conj_lie_element_embed_rotation_eq_trig_matrix E D (Real.pi / 2), UpperTheory.conj_lie_element_embed_rotation_eq_trig_matrix E D (Real.pi / 4), c4, s4, m4]
  simp only [Real.cos_zero, Real.sin_zero, Real.cos_pi_div_two, Real.sin_pi_div_two]
  funext i j w
  fin_cases i <;> fin_cases j <;> simp <;> ring

end UpperTheory.ConvolutionTheory.RankTwoDescent.SH

open UpperTheory.ConvolutionTheory.RankTwoDescent.SH in
theorem UpperTheory.ConvolutionTheory.RankTwoDescent.shift_of :
    TrAdm → Shift := by
  intro hT E _ _ _ D P ω χ hC hU hχ L N φ hG
  have adm := hT E D P ω χ hC hU hχ
  obtain ⟨f, rfl, -⟩ := UpperTheory.exists_smooth_lie_action_mem_cuspidal_translates E P 0 φ hG.mem
  have hmem : ∀ X, (lie E 2 X f).1 ∈ Tr P := fun X => by
    obtain ⟨f', hf', hm⟩ := UpperTheory.exists_smooth_lie_action_mem_cuspidal_translates E P X f.1 hG.mem
    rwa [show f' = f from Subtype.ext hf'] at hm
  have hc : ∀ X, Continuous (lie E 2 X f).1 := fun X => (adm _ (hmem X)).cont
  have hb : ∀ X, ∃ B : ℝ, ∀ g, ‖(lie E 2 X f).1 g‖ ≤ B := fun X => (adm _ (hmem X)).bdd
  have hf0 := adm _ hG.mem
  have hq : ∀ k, Q D L N f (toL (XB D k)) := fun k => q_cv k hG hf0.cont (hc _) (hb _)
  set b0 : Lie E 2 := toL (XB D (em E (rot 0))) with hb0
  set b1 : Lie E 2 := toL (XB D (em E (rot (Real.pi / 2)))) with hb1
  set b2 : Lie E 2 := toL (XB D (em E (rot (Real.pi / 4)))) with hb2
  set b3 : Lie E 2 := (2 : ℝ) • b2 + (-1 : ℝ) • b0 + (-1 : ℝ) • b1 with hb3
  have hq3 : Q D L N f b3 := quadraticCondition_linear hc _ _ _ (hq _) (hq _) (hq _)
  set κ : ℂ := (2 * Real.pi * Complex.I)⁻¹ with hκ
  have hκ0 : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by
    simp [Real.pi_ne_zero, Complex.I_ne_zero]
  refine ⟨κ • (lie E 2 b1 f).1, κ • (lie E 2 b3 f).1, κ • (lie E 2 b0 f).1, gd_smul hG (hmem _) (hq _), gd_smul hG (hmem _) hq3,
    gd_smul hG (hmem _) (hq _), fun y t hy => ?_⟩
  obtain ⟨-, h2, -⟩ := UpperTheory.whittakerPeriod_add_smul_and_norm_le E D
  have e := UpperTheory.whittakerCoeff_lieDeriv_unipotent_eq_mul E D f ⟨hf0.cont, hf0.left⟩ (fun X => ⟨hc X, hb X⟩) (iy y) (em E (rot t))
  rw [xb_dec D t, whittaker_lieDerivative_linear hc, re_iy y hy, ← map_mul] at e
  rw [h2, h2, h2]
  have e' : (y : ℂ) * Wo D f.1 (em E (aE (iy y) * rot t)) = κ * ((2 * Real.pi * Complex.I * (y : ℂ)) * Wo D f.1 (em E (aE (iy y) * rot t))) := by
    rw [hκ]; field_simp
  rw [e', ← e, hκ]
  push_cast
  ring

end
