import Development.AutomorphicArithmetic.Foundations.Convolution.GeneralizedMeasures.HeckeFinAlt
import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.TensApply
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.AdelicNormDetLeHeightPow
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.LocalHeightDeterminant

open MeasureTheory NumberField IsDedekindDomain MvPolynomial Filter
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum UpperTheory.ConvolutionTheory.C PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Geo
open GroundTheory.Global GroundTheory.Global.SemiLocal GroundTheory.Automorphic.Spherical
open UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.GM

private theorem norm_det_le_pow {R : Type*} [NormedField R] [IsUltrametricDist R] {n : ℕ} (g : GL (Fin n) R) :
    ‖(g : Matrix (Fin n) (Fin n) R).det‖ ≤ locHeight g ^ n :=
  _root_.UpperTheory.Reformulated.B.LocalHeightDeterminant.norm_det_le_pow g

private theorem norm_det_inv {R : Type*} [NormedField R] {n : ℕ} (h : GL (Fin n) R)
    (H : ‖(h : Matrix (Fin n) (Fin n) R).det‖ = 1) :
    ‖((h⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R).det‖ = 1 := by
  have := congrArg norm (show (h : Matrix (Fin n) (Fin n) R).det *
      ((h⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R).det = 1 by
    rw [← Matrix.det_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.det_one])
  rwa [norm_mul, H, one_mul, norm_one] at this

section SlopeTestRemainingChoices

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}

private theorem norm_eq_one_of_v {w : Pl E} {y : w.adicCompletion E} (h : Valued.v y = 1) : ‖y‖ = 1 := by
  have hy : y ≠ 0 := by
    rintro rfl
    simp at h
  refine le_antisymm (Valued.toNormedField.norm_le_one_iff.2 h.le) ?_
  have h2 : ‖y⁻¹‖ ≤ 1 := Valued.toNormedField.norm_le_one_iff.2 (by rw [map_inv₀, h, inv_one])
  rw [norm_inv] at h2
  exact (inv_le_one₀ (norm_pos_iff.2 hy)).1 h2

private theorem infAt_finEmb' (w : InfinitePlace E) (x : AdelicGLn.FiniteAdelicGL E n) :
    infAt w (finEmb E n x) = 1 := by
  show (AdelicGLn.infiniteEquiv E n (AdelicGLn.prodEquiv E n (finEmb E n x)).1) w = 1
  rw [AutomorphicForm.prodEquiv_finEmb, map_one]
  rfl

private theorem liesOver_of_below {w : Pl E} {q : Pl F} (h : AdeleBaseChange.below F w = q) :
    w.asIdeal.LiesOver q.asIdeal := by
  subst h
  constructor
  rfl

private theorem heightOff_inv (q : Pl F) (g : AdelicGLn.AdelicGL E n) : heightOff q g⁻¹ = heightOff q g := by
  simp only [heightOff, infAt_inv, finAt_inv, locHeight_inv]

private theorem heightOff_nonneg (q : Pl F) (g : AdelicGLn.AdelicGL E n) : 0 ≤ heightOff q g :=
  mul_nonneg (Finset.prod_nonneg fun w _ => pow_nonneg (locHeight_pos _).le _)
    (finprod_nonneg fun w => finprod_nonneg fun _ => (locHeight_pos _).le)

private theorem module_le (q : Pl F) (x : AdelicGLn.FiniteAdelicGL E n)
    (hq : ∀ w : PlacesOver E q, ‖((finAt w.1 (finEmb E n x) : GL (Fin n) (w.1.adicCompletion E)) :
      Matrix (Fin n) (Fin n) (w.1.adicCompletion E)).det‖ = 1) :
    (detModule E n (finEmb E n x) : ℝ) ≤ heightOff q (finEmb E n x) ^ n := by
  classical
  set X := finEmb E n x with hX
  have hi : ∀ w : InfinitePlace E, ((AdelicGLn.det E n X : AdeleRing (𝓞 E) E)).1 w = 1 := fun w => by
    have h : ((AdelicGLn.det E n X : AdeleRing (𝓞 E) E)).1 w =
        (infAt w X : Matrix (Fin n) (Fin n) w.Completion).det := by
      rw [AdelicGLn.coe_det, ← infEval_apply, RingHom.map_det]; rfl
    rw [h, hX, infAt_finEmb']
    simp
  have hf : ∀ v : Pl E, ((AdelicGLn.det E n X : AdeleRing (𝓞 E) E)).2 v =
      (finAt v X : Matrix (Fin n) (Fin n) (v.adicCompletion E)).det := fun v => by
    rw [AdelicGLn.coe_det, ← finEval_apply, RingHom.map_det]; rfl
  have hg : ∀ w : Pl E, (∏ᶠ (_ : AdeleBaseChange.below F w ≠ q), locHeight (finAt w X)) =
      if AdeleBaseChange.below F w ≠ q then locHeight (finAt w X) else 1 := fun w => finprod_eq_if
  have hP : (∏ w : InfinitePlace E, locHeight (infAt w X) ^ w.mult) = 1 :=
    Finset.prod_eq_one fun w _ => by rw [hX, infAt_finEmb', locHeight_one, one_pow]
  have h1 := IdeleGroup.finite_mulSupport_norm (AdelicGLn.det E n X)
  have h2 := finite_mulSupport_locHeight_finAt X
  have e1 := finprod_eq_prod_of_mulSupport_subset (fun v : Pl E => ‖((AdelicGLn.det E n X : AdeleRing (𝓞 E) E)).2 v‖)
    (s := (h1.union h2).toFinset) (fun v hv => by simp only [Set.Finite.coe_toFinset]; exact Or.inl hv)
  have e2 := finprod_eq_prod_of_mulSupport_subset
    (fun w : Pl E => if AdeleBaseChange.below F w ≠ q then locHeight (finAt w X) else 1)
    (s := (h1.union h2).toFinset) (fun v hv => by
      simp only [Set.Finite.coe_toFinset]
      refine Or.inr fun h3 => hv ?_
      dsimp only
      split_ifs
      · exact h3
      · rfl)
  rw [show (detModule E n X : ℝ) = (IdeleGroup.ideleModule E (AdelicGLn.det E n X) : ℝ) from rfl,
    IdeleGroup.ideleModule_eq, heightOff, hP, one_mul]
  simp only [hg, hi, norm_one, one_pow, Finset.prod_const_one, one_mul]
  rw [e1, e2, ← Finset.prod_pow]
  refine Finset.prod_le_prod (fun _ _ => norm_nonneg _) fun v _ => ?_
  rw [hf]
  by_cases hb : AdeleBaseChange.below F v = q
  · have := hq ⟨v, liesOver_of_below hb⟩
    simp only [ne_eq, hb, not_true_eq_false, if_false, one_pow]
    exact this.le
  · rw [if_pos hb]
    exact norm_det_le_pow _

end SlopeTestRemainingChoices

theorem UpperTheory.ConvolutionTheory.GM.tensHt : TensHt := by
  classical
  intro F E _ _ _ _ _ n hn q
  obtain ⟨D, N, -, hD⟩ := UpperTheory.adelicNorm_det_le_height_pow E n
  set m := 2 * Fintype.card (InfinitePlace E) with hm
  refine ⟨N * m + 1, fun Yf hYf => ?_⟩
  set M : ℝ := max 1 D with hMdef
  have hM : 1 ≤ M := le_max_left _ _
  have hM0 : 0 ≤ M := zero_le_one.trans hM
  have hYf0 : 0 ≤ Yf := zero_le_one.trans hYf
  refine ⟨heightConst E n * M ^ m * Yf ^ (n * m) * Yf,
    one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le
      (one_le_mul_of_one_le_of_one_le one_le_heightConst (one_le_pow₀ hM)) (one_le_pow₀ hYf)) hYf,
    fun β e Y hY hβ he g hg => ?_⟩
  have hY0 : 0 ≤ Y := zero_le_one.trans hY
  have hg' : kbar β (infPart E n (g : AdelicGLn.AdelicGL E n)) *
      e (finPart E n (g : AdelicGLn.AdelicGL E n)) ≠ 0 := by
    have := (UpperTheory.ConvolutionTheory.Tf.tensApply E n hn β e).1 g
    rw [this] at hg
    exact hg
  have he0 : e (finPart E n (g : AdelicGLn.AdelicGL E n)) ≠ 0 := right_ne_zero_of_mul hg'
  refine ⟨?_, he0⟩
  have hk := left_ne_zero_of_mul hg'
  obtain ⟨s, hs⟩ : ∃ s, β (infPart E n (g : AdelicGLn.AdelicGL E n) * zInf E n s) ≠ 0 := by
    by_contra hc
    push_neg at hc
    exact hk (by simp [kbar, hc])
  set x := finPart E n (g : AdelicGLn.AdelicGL E n) with hx
  set G := infEmb E n (infPart E n (g : AdelicGLn.AdelicGL E n)) with hG
  set X := finEmb E n x with hX
  have hGX : G * X = (g : AdelicGLn.AdelicGL E n) := infEmb_infPart_mul_finEmb_finPart _
  set A := infEmb E n (infPart E n (g : AdelicGLn.AdelicGL E n) * zInf E n s) with hAdef
  have hA : A = G * centralSection E n s := by rw [hAdef, map_mul, infEmb_zInf]
  have hAY : AutomorphicForm.height A ≤ Y := hβ _ hs
  obtain ⟨hXY, hdet⟩ := he x he0
  have hq : ∀ w : PlacesOver E q, ‖((finAt w.1 (finEmb E n x) : GL (Fin n) (w.1.adicCompletion E)) :
      Matrix (Fin n) (Fin n) (w.1.adicCompletion E)).det‖ = 1 := fun w => norm_eq_one_of_v (hdet w)
  have hq' : ∀ w : PlacesOver E q, ‖((finAt w.1 (finEmb E n x⁻¹) : GL (Fin n) (w.1.adicCompletion E)) :
      Matrix (Fin n) (Fin n) (w.1.adicCompletion E)).det‖ = 1 := fun w => by
    rw [map_inv, finAt_inv]
    exact norm_det_inv _ (hq w)
  have hg1 : detModule E n (g : AdelicGLn.AdelicGL E n) = 1 := mem_normOneGL_iff_detModule.1 g.2
  have hGX1 : detModule E n G * detModule E n X = 1 := by rw [← map_mul, hGX, hg1]
  have hs_eq : detModule E n A * detModule E n X = s := by
    rw [hA, map_mul, detModule_centralSection hn, mul_right_comm, hGX1, one_mul]
  have hsR : (detModule E n A : ℝ) * (detModule E n X : ℝ) = s := congrArg Subtype.val hs_eq
  have hsR' : (detModule E n A⁻¹ : ℝ) * (detModule E n X⁻¹ : ℝ) = (s : ℝ)⁻¹ := by
    rw [map_inv, map_inv, Positive.coe_inv, Positive.coe_inv, ← mul_inv, hsR]
  have hb : ∀ B : AdelicGLn.AdelicGL E n, AutomorphicForm.height B ≤ Y →
      (detModule E n B : ℝ) ≤ M * Y ^ N := fun B hB =>
    (hD B).trans (mul_le_mul (le_max_right _ _) (pow_le_pow_left₀ (height_pos B).le hB N)
      (pow_nonneg (height_pos B).le N) hM0)
  have hxb : (detModule E n X : ℝ) ≤ Yf ^ n :=
    (module_le q x hq).trans (pow_le_pow_left₀ (heightOff_nonneg q _) hXY n)
  have hxb' : (detModule E n X⁻¹ : ℝ) ≤ Yf ^ n := by
    have h := module_le q x⁻¹ hq'
    rw [map_inv, heightOff_inv] at h
    exact h.trans (pow_le_pow_left₀ (heightOff_nonneg q _) hXY n)
  set L : ℝ := M * Y ^ N * Yf ^ n with hL
  have hL1 : 1 ≤ L := one_le_mul_of_one_le_of_one_le
    (one_le_mul_of_one_le_of_one_le hM (one_le_pow₀ hY)) (one_le_pow₀ hYf)
  have hMY : 0 ≤ M * Y ^ N := mul_nonneg hM0 (pow_nonneg hY0 N)
  have hsL : (s : ℝ) ≤ L := by
    rw [← hsR]
    exact mul_le_mul (hb A hAY) hxb (detModule E n X).2.le hMY
  have hsL' : (s : ℝ)⁻¹ ≤ L := by
    rw [← hsR']
    exact mul_le_mul (hb A⁻¹ (by rwa [height_inv])) hxb' (detModule E n X⁻¹).2.le hMY
  have hZ : AutomorphicForm.height (centralSection E n s) ≤ L ^ m := by
    set ee : ℝ := ((n * Module.finrank ℚ E : ℝ))⁻¹ with hee
    have he0' : 0 ≤ ee := by positivity
    have he1 : ee ≤ 1 := by
      rw [hee, ← Nat.cast_mul]
      exact Nat.cast_inv_le_one _
    have key : ∀ y : ℝ, 0 ≤ y → y ≤ L → y ^ ee ≤ L := fun y hy hyL =>
      calc y ^ ee ≤ L ^ ee := Real.rpow_le_rpow hy hyL he0'
        _ ≤ L ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hL1 he1
        _ = L := Real.rpow_one L
    refine height_diagUnits_posIdele_le (K := E) (n := n) (ρ := fun _ => (s : ℝ) ^ ee)
      (fun _ => Real.rpow_pos_of_pos s.2 ee) hL1 fun _ => ⟨key _ s.2.le hsL, ?_⟩
    rw [← Real.inv_rpow s.2.le]
    exact key _ (inv_pos.2 s.2).le hsL'
  have hGh : AutomorphicForm.height G ≤ heightConst E n * Y * L ^ m := by
    have h1 : G = A * (centralSection E n s)⁻¹ := by rw [hA, mul_inv_cancel_right]
    rw [h1]
    refine (height_mul_le _ _).trans ?_
    rw [height_inv]
    have hc0 : 0 ≤ heightConst E n := zero_le_one.trans one_le_heightConst
    exact mul_le_mul (mul_le_mul_of_nonneg_left hAY hc0) hZ (height_pos _).le (mul_nonneg hc0 hY0)
  have e1 : ∀ w, infAt w (g : AdelicGLn.AdelicGL E n) = infAt w G := fun w => by
    rw [← hGX, infAt_mul, hX, infAt_finEmb', mul_one]
  have e2 : ∀ w, finAt w (g : AdelicGLn.AdelicGL E n) = finAt w X := fun w => by
    rw [← hGX, finAt_mul, hG, finAt_infEmb, one_mul]
  have hsplit : heightOff q (g : AdelicGLn.AdelicGL E n) =
      (∏ w : InfinitePlace E, locHeight (infAt w G) ^ w.mult) * heightOff q X := by
    unfold heightOff
    simp only [e1, e2, hX, infAt_finEmb', locHeight_one, one_pow, Finset.prod_const_one, one_mul]
  have hPG : (∏ w : InfinitePlace E, locHeight (infAt w G) ^ w.mult) ≤ AutomorphicForm.height G :=
    le_mul_of_one_le_right (zero_le_one.trans (one_le_prod_locHeight G)) (one_le_finprod_locHeight G)
  rw [hsplit]
  calc (∏ w : InfinitePlace E, locHeight (infAt w G) ^ w.mult) * heightOff q X
      ≤ (heightConst E n * Y * L ^ m) * Yf :=
        mul_le_mul (hPG.trans hGh) hXY (heightOff_nonneg q _)
          (mul_nonneg (mul_nonneg (zero_le_one.trans one_le_heightConst) hY0) (pow_nonneg (zero_le_one.trans hL1) m))
    _ = heightConst E n * M ^ m * Yf ^ (n * m) * Yf * Y ^ (N * m + 1) := by
        rw [hL, mul_pow, mul_pow, ← pow_mul, ← pow_mul]
        ring
