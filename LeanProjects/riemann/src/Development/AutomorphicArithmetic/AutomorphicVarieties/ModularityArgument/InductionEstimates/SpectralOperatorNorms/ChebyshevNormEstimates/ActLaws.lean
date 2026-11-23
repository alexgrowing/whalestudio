import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.SpectralOperatorNorms.KillExempt
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ScatteringLimits.ConvolutionSpectra.ConvSpec
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ScatteringLimits.ConvolutionSpectra.ConvLaws

open MeasureTheory NumberField IsDedekindDomain MvPolynomial Filter Topology
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.Ci PositivityTheory.Rg.Fx
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Adel PositivityTheory.Rg.Tf.IntegralApplyAeEq UpperTheory.V.Z.IntegralApplyAeEq UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial

noncomputable section SlopeTestRemainingChoices

variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] [CompleteSpace V]

private def cL : (V →L[ℂ] V) →L[ℂ] (L V →L[ℂ] L V) := LinearMap.mkContinuous
    { toFun := fun A => A.compLpL 2 volume
      map_add' := fun A B => ContinuousLinearMap.add_compLpL A B
      map_smul' := fun a A => ContinuousLinearMap.smul_compLpL a A } 1 fun A => by
      rw [one_mul]; exact ContinuousLinearMap.norm_compLpL_le A

private theorem cL_ae (c : V →L[ℂ] V) (x : L V) : ∀ᵐ t : ℝ, cL c x t = c (x t) := c.coeFn_compLpL x

private theorem cL_norm (c : V →L[ℂ] V) (t : ℝ) (x : L V) : ‖cL c (sh V t x)‖ ≤ ‖c‖ * ‖x‖ := by
  refine (ContinuousLinearMap.le_opNorm _ _).trans ?_
  rw [show ‖sh V t x‖ = ‖x‖ from (shF V).norm t x]
  gcongr
  exact ContinuousLinearMap.norm_compLpL_le _

private theorem cL_comp (c c' : V →L[ℂ] V) (x : L V) : cL c (cL c' x) = cL (c ∘L c') x := by
  refine Lp.ext ?_
  filter_upwards [cL_ae c (cL c' x), cL_ae c' x, cL_ae (c ∘L c') x] with t h1 h2 h3
  rw [h1, h2, h3]; rfl

private theorem cL_one (x : L V) : cL (1 : V →L[ℂ] V) x = x := Lp.ext (cL_ae 1 x)

private theorem sh_cL (c : V →L[ℂ] V) (a : ℝ) (x : L V) : sh V a (cL c x) = cL c (sh V a x) := by
  refine Lp.ext ?_
  filter_upwards [sh_ae V a (cL c x), (measurePreserving_add_right volume a).quasiMeasurePreserving.ae (cL_ae c x),
    cL_ae c (sh V a x), sh_ae V a x] with t h1 h2 h3 h4
  rw [h1, h2, h3, h4]

private theorem TT (c c' : V →L[ℂ] V) (a b : ℝ) (x : L V) :
    cL c (sh V a (cL c' (sh V b x))) = cL (c ∘L c') (sh V (a + b) x) := by
  rw [sh_cL, cL_comp, show sh V (a + b) x = sh V a (sh V b x) from (shF V).add a b x]

private theorem conv_eq {κ : ℝ → V →L[ℂ] V} (hk : Ker κ) (x : L V) : conv κ x = ∫ t, cL (κ t) (sh V t x) :=
  (convSpec κ hk x).2.2

private theorem conv_int {κ : ℝ → V →L[ℂ] V} (hk : Ker κ) (x : L V) : Integrable fun t => cL (κ t) (sh V t x) :=
  (convSpec κ hk x).2.1

private theorem symb_int {κ : ℝ → V →L[ℂ] V} (hk : Ker κ) (z : ℂ) : Integrable fun t : ℝ => Complex.exp (z * t) • κ t := by
  refine Continuous.integrable_of_hasCompactSupport (Continuous.smul (f := fun t : ℝ => Complex.exp (z * t)) (by fun_prop) hk.1) ?_
  exact hk.2.mono fun t ht h0 => ht (by simp [h0])

private def KK (A : L V →L[ℂ] L V) (s : ℂ → V →L[ℂ] V) : Prop := ∃ κ, Ker κ ∧ A = conv κ ∧ s = symb κ

private theorem ker_zero : Ker (fun _ : ℝ => (0 : V →L[ℂ] V)) := ⟨continuous_const, HasCompactSupport.zero⟩

private theorem KK_zero : KK (0 : L V →L[ℂ] L V) fun _ => 0 := by
  refine ⟨fun _ => 0, ker_zero, ?_, ?_⟩
  · ext1 x; rw [conv_eq ker_zero]; simp
  · ext1 z; simp [symb]

private theorem KK_add {A A' : L V →L[ℂ] L V} {s s'} (h : KK A s) (h' : KK A' s') : KK (A + A') fun z => s z + s' z := by
  obtain ⟨κ, hk, rfl, rfl⟩ := h
  obtain ⟨κ', hk', rfl, rfl⟩ := h'
  have h : Ker fun t => κ t + κ' t := ⟨hk.1.add hk'.1, hk.2.add hk'.2⟩
  refine ⟨_, h, ?_, ?_⟩
  · ext1 x
    rw [ContinuousLinearMap.add_apply, conv_eq h, conv_eq hk, conv_eq hk', ← integral_add (conv_int hk x) (conv_int hk' x)]
    simp only [map_add, ContinuousLinearMap.add_apply]
  · ext1 z
    simp only [symb, smul_add]
    rw [integral_add (symb_int hk z) (symb_int hk' z)]

private theorem ker_sh {κ : ℝ → V →L[ℂ] V} (hk : Ker κ) (F : (V →L[ℂ] V) →L[ℂ] (V →L[ℂ] V)) (a : ℝ) :
    Ker fun t => F (κ (t - a)) :=
  ⟨F.continuous.comp (hk.1.comp (by fun_prop)),
    (hk.2.comp_homeomorph (Homeomorph.subRight a)).comp_left (g := F) (map_zero F)⟩

private theorem symb_sh {κ : ℝ → V →L[ℂ] V} (hk : Ker κ) (F : (V →L[ℂ] V) →L[ℂ] (V →L[ℂ] V)) (a : ℝ) (z : ℂ) :
    symb (fun t => F (κ (t - a))) z = Complex.exp (z * a) • F (symb κ z) := by
  rw [symb, symb, ← F.integral_comp_comm (symb_int hk z), ← integral_smul, ← integral_add_right_eq_self _ a]
  refine integral_congr_ae (Eventually.of_forall fun t => ?_)
  simp only [add_sub_cancel_right, map_smul, smul_smul, ← Complex.exp_add]
  congr 2
  push_cast; ring

private theorem KK_left {A : L V →L[ℂ] L V} {s} (h : KK A s) (c : V →L[ℂ] V) (a : ℝ) :
    KK ((cL c ∘L sh V a) ∘L A) fun z => (Complex.exp (z * a) • c) ∘L s z := by
  obtain ⟨κ, hk, rfl, rfl⟩ := h
  have h := ker_sh hk (ContinuousLinearMap.compL ℂ V V V c) a
  refine ⟨_, h, ?_, ?_⟩
  · ext1 x
    rw [ContinuousLinearMap.comp_apply, conv_eq h, conv_eq hk, ← ContinuousLinearMap.integral_comp_comm _ (conv_int hk x),
      ← integral_add_right_eq_self (fun t => cL (ContinuousLinearMap.compL ℂ V V V c (κ (t - a))) (sh V t x)) a]
    refine integral_congr_ae (Eventually.of_forall fun t => ?_)
    simp only [ContinuousLinearMap.comp_apply, TT, add_sub_cancel_right, ContinuousLinearMap.compL_apply, add_comm a t]
  · ext1 z
    rw [symb_sh hk, ContinuousLinearMap.compL_apply, ContinuousLinearMap.smul_comp]

private theorem KK_right {A : L V →L[ℂ] L V} {s} (h : KK A s) (c : V →L[ℂ] V) (a : ℝ) :
    KK (A ∘L (cL c ∘L sh V a)) fun z => s z ∘L (Complex.exp (z * a) • c) := by
  obtain ⟨κ, hk, rfl, rfl⟩ := h
  have h := ker_sh hk ((ContinuousLinearMap.compL ℂ V V V).flip c) a
  refine ⟨_, h, ?_, ?_⟩
  · ext1 x
    rw [ContinuousLinearMap.comp_apply, conv_eq h, conv_eq hk,
      ← integral_add_right_eq_self (fun t => cL ((ContinuousLinearMap.compL ℂ V V V).flip c (κ (t - a))) (sh V t x)) a]
    refine integral_congr_ae (Eventually.of_forall fun t => ?_)
    simp only [ContinuousLinearMap.comp_apply, TT, add_sub_cancel_right, ContinuousLinearMap.compL_apply,
      ContinuousLinearMap.flip_apply]
  · ext1 z
    rw [symb_sh hk, ContinuousLinearMap.flip_apply, ContinuousLinearMap.compL_apply, ContinuousLinearMap.comp_smul]

private theorem KK_mul {A A' : L V →L[ℂ] L V} {s s'} (h : KK A s) (h' : KK A' s') : KK (A ∘L A') fun z => s z ∘L s' z := by
  obtain ⟨κ, hk, rfl, rfl⟩ := h
  obtain ⟨κ', hk', rfl, rfl⟩ := h'
  have i1 : Integrable κ := hk.1.integrable_of_hasCompactSupport hk.2
  have i2 : Integrable κ' := hk'.1.integrable_of_hasCompactSupport hk'.2
  have h : Ker (convolution κ κ' (ContinuousLinearMap.compL ℂ V V V) volume) :=
    ⟨hk'.2.continuous_convolution_right _ hk.1.locallyIntegrable hk'.1, hk.2.convolution _ hk'.2⟩
  have e : ∀ t, Integrable fun r => κ r ∘L κ' (t - r) := fun t =>
    hk'.2.convolutionExists_right (ContinuousLinearMap.compL ℂ V V V) hk.1.locallyIntegrable hk'.1 t
  refine ⟨_, h, ?_, ?_⟩
  · ext1 x
    have hI : Integrable (fun p : ℝ × ℝ => cL (κ p.2 ∘L κ' (p.1 - p.2)) (sh V p.1 x)) (volume.prod volume) := by
      refine ((i1.convolution_integrand (ContinuousLinearMap.compL ℂ V V V) i2).norm.mul_const ‖x‖).mono'
        (Continuous.aestronglyMeasurable ?_) (Eventually.of_forall fun p => cL_norm _ _ _)
      refine Continuous.clm_apply (cL.continuous.comp ?_) (((shF V).cont x).comp continuous_fst)
      exact (hk.1.comp continuous_snd).clm_comp (hk'.1.comp (by fun_prop))
    rw [ContinuousLinearMap.comp_apply, conv_eq h, conv_eq hk, conv_eq hk']
    have h1 : ∀ t, cL (convolution κ κ' (ContinuousLinearMap.compL ℂ V V V) volume t) (sh V t x) =
        ∫ r, cL (κ r ∘L κ' (t - r)) (sh V t x) := fun t =>
      ((cL.flip (sh V t x)).integral_comp_comm (e t)).symm
    simp only [h1]
    rw [integral_integral_swap (f := fun t r => cL (κ r ∘L κ' (t - r)) (sh V t x)) hI]
    refine integral_congr_ae (Eventually.of_forall fun r => ?_)
    have h2 := ((cL (κ r) ∘L sh V r).integral_comp_comm (conv_int hk' x)).symm
    refine h2.trans ?_
    beta_reduce
    rw [← integral_add_right_eq_self (fun t => cL (κ r ∘L κ' (t - r)) (sh V t x)) r]
    refine integral_congr_ae (Eventually.of_forall fun t => ?_)
    simp only [ContinuousLinearMap.comp_apply, TT, add_sub_cancel_right, add_comm r t]
  · ext1 z
    have h1 := integral_convolution (ContinuousLinearMap.compL ℂ V V V) (symb_int hk z) (symb_int hk' z) (μ := volume) (ν := volume)
    refine h1.symm.trans ?_
    refine integral_congr_ae (Eventually.of_forall fun t => ?_)
    simp only [convolution_def, ← integral_smul]
    refine integral_congr_ae (Eventually.of_forall fun r => ?_)
    simp only [map_smul, ContinuousLinearMap.smul_apply, smul_smul, ← Complex.exp_add]
    congr 2
    push_cast; ring

private def opD (u : ℝ →₀ (V →L[ℂ] V)) : L V →L[ℂ] L V := u.sum fun t c => cL c ∘L sh V t

private def syD (u : ℝ →₀ (V →L[ℂ] V)) (z : ℂ) : V →L[ℂ] V := u.sum fun t c => Complex.exp (z * t) • c

private theorem opD_apply (u : ℝ →₀ (V →L[ℂ] V)) (x : L V) :
    opD u x = u.sum fun t c => c.compLpL 2 volume (sh V t x) := by
  simp only [opD, Finsupp.sum, ContinuousLinearMap.sum_apply]; rfl

private theorem opD_add (u u' : ℝ →₀ (V →L[ℂ] V)) : opD (u + u') = opD u + opD u' :=
  Finsupp.sum_add_index' (fun _ => by simp) fun _ _ _ => by rw [map_add, ContinuousLinearMap.add_comp]

private theorem syD_add (u u' : ℝ →₀ (V →L[ℂ] V)) (z : ℂ) : syD (u + u') z = syD u z + syD u' z :=
  Finsupp.sum_add_index' (fun _ => by simp) fun _ _ _ => smul_add _ _ _

private theorem opD_single (t : ℝ) (c : V →L[ℂ] V) : opD (Finsupp.single t c) = cL c ∘L sh V t :=
  Finsupp.sum_single_index (by simp)

private theorem syD_single (t : ℝ) (c : V →L[ℂ] V) (z : ℂ) : syD (Finsupp.single t c) z = Complex.exp (z * t) • c :=
  Finsupp.sum_single_index (by simp)

private theorem D_ind {P : (L V →L[ℂ] L V) → (ℂ → V →L[ℂ] V) → Prop} (h0 : P 0 fun _ => 0)
    (ha : ∀ A A' s s', P A s → P A' s' → P (A + A') fun z => s z + s' z)
    (h1 : ∀ (c : V →L[ℂ] V) (a : ℝ), P (cL c ∘L sh V a) fun z => Complex.exp (z * a) • c) (u : ℝ →₀ (V →L[ℂ] V)) :
    P (opD u) (syD u) := by
  induction u using Finsupp.induction_linear with
  | zero => exact h0
  | add f g hf hg =>
    rw [opD_add, show syD (f + g) = fun z => syD f z + syD g z from funext (syD_add f g)]
    exact ha _ _ _ _ hf hg
  | single a c =>
    rw [opD_single, show syD (Finsupp.single a c) = _ from funext (syD_single a c)]
    exact h1 c a

private def RR (A : L V →L[ℂ] L V) (s : ℂ → V →L[ℂ] V) : Prop :=
  ∃ u B r, KK B r ∧ A = opD u + B ∧ s = fun z => syD u z + r z

private theorem RR_of_KK {A : L V →L[ℂ] L V} {s} (h : KK A s) : RR A s :=
  ⟨0, A, s, h, (zero_add A).symm, funext fun z => (zero_add (s z)).symm⟩

private theorem RR_add {A A' : L V →L[ℂ] L V} {s s'} (h : RR A s) (h' : RR A' s') : RR (A + A') fun z => s z + s' z := by
  obtain ⟨u, B, r, hk, rfl, rfl⟩ := h
  obtain ⟨u', B', r', hk', rfl, rfl⟩ := h'
  exact ⟨u + u', _, _, KK_add hk hk', by rw [opD_add]; abel, funext fun z => by rw [syD_add, add_add_add_comm]⟩

private theorem RR_single (c : V →L[ℂ] V) (a : ℝ) : RR (cL c ∘L sh V a) fun z => Complex.exp (z * a) • c :=
  ⟨Finsupp.single a c, _, _, KK_zero, by rw [opD_single, add_zero], funext fun z => by rw [syD_single, add_zero]⟩

private theorem RR_ind {P : (L V →L[ℂ] L V) → (ℂ → V →L[ℂ] V) → Prop}
    (ha : ∀ A A' s s', P A s → P A' s' → P (A + A') fun z => s z + s' z)
    (h1 : ∀ (c : V →L[ℂ] V) (a : ℝ), P (cL c ∘L sh V a) fun z => Complex.exp (z * a) • c)
    (hK : ∀ A s, KK A s → P A s) {A s} (h : RR A s) : P A s := by
  obtain ⟨u, B, r, hk, rfl, rfl⟩ := h
  exact ha _ _ _ _ (D_ind (hK _ _ KK_zero) ha h1 u) (hK _ _ hk)

private theorem KK_RR {A A' : L V →L[ℂ] L V} {s s'} (h : KK A s) (h' : RR A' s') : KK (A ∘L A') fun z => s z ∘L s' z := by
  refine RR_ind (P := fun A' s' => KK (A ∘L A') fun z => s z ∘L s' z) (fun B B' r r' h1 h2 => ?_) (fun c a => KK_right h c a)
    (fun B r hk => KK_mul h hk) h'
  simpa only [ContinuousLinearMap.comp_add] using KK_add h1 h2

private theorem RR_mul {A A' : L V →L[ℂ] L V} {s s'} (h : RR A s) (h' : RR A' s') : RR (A ∘L A') fun z => s z ∘L s' z := by
  refine RR_ind (P := fun A s => RR (A ∘L A') fun z => s z ∘L s' z) (fun B B' r r' h1 h2 => ?_) (fun c a => ?_)
    (fun B r hk => RR_of_KK (KK_RR hk h')) h
  · simpa only [ContinuousLinearMap.add_comp] using RR_add h1 h2
  refine RR_ind (P := fun A' s' => RR ((cL c ∘L sh V a) ∘L A') fun z => (Complex.exp (z * a) • c) ∘L s' z)
    (fun B B' r r' h1 h2 => ?_) (fun c' b => ?_) (fun B r hk => RR_of_KK (KK_left hk c a)) h'
  · simpa only [ContinuousLinearMap.comp_add] using RR_add h1 h2
  have e1 : (cL c ∘L sh V a) ∘L (cL c' ∘L sh V b) = cL (c ∘L c') ∘L sh V (a + b) := ContinuousLinearMap.ext (TT c c' a b)
  have e2 : (fun z : ℂ => (Complex.exp (z * a) • c) ∘L (Complex.exp (z * b) • c')) =
      fun z : ℂ => Complex.exp (z * (a + b : ℝ)) • (c ∘L c') := funext fun z => by
    rw [ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_smul, smul_smul, ← Complex.exp_add]
    congr 2
    push_cast; ring
  rw [e1, e2]
  exact RR_single _ _

private theorem RR_const (c : ℂ) : RR (c • (1 : L V →L[ℂ] L V)) fun _ => c • 1 := by
  have h := RR_single (c • (1 : V →L[ℂ] V)) 0
  have e : cL (c • (1 : V →L[ℂ] V)) ∘L sh V 0 = c • 1 := ContinuousLinearMap.ext fun x => by
    rw [ContinuousLinearMap.comp_apply, map_smul, ContinuousLinearMap.smul_apply, cL_one, show sh V 0 x = x from (shF V).zero x]
    rfl
  rw [e] at h
  simpa using h

private theorem exp_bd (z : ℂ) (hz : |z.re| ≤ 1) (t : ℝ) : ‖Complex.exp (z * t)‖ ≤ Real.exp |t| := by
  rw [Complex.norm_exp, Complex.re_mul_ofReal]
  refine Real.exp_le_exp.2 ((le_abs_self _).trans ?_)
  rw [abs_mul]
  exact mul_le_of_le_one_left (abs_nonneg _) hz

private theorem RR_bd {A : L V →L[ℂ] L V} {s} (h : RR A s) : ∃ K, SB s K := by
  refine RR_ind (P := fun _ s => ∃ K, SB s K) ?_ (fun c a => ⟨Real.exp |a| * ‖c‖, fun z hz => ?_⟩) ?_ h
  · rintro - - s s' ⟨K, hK⟩ ⟨K', hK'⟩
    exact ⟨K + K', fun z hz => (norm_add_le _ _).trans (add_le_add (hK z hz) (hK' z hz))⟩
  · rw [norm_smul]
    exact mul_le_mul_of_nonneg_right (exp_bd z hz a) (norm_nonneg _)
  · rintro _ _ ⟨κ, hk, rfl, rfl⟩
    refine ⟨∫ t, Real.exp |t| * ‖κ t‖, fun z hz => norm_integral_le_of_norm_le ?_ (Eventually.of_forall fun t => ?_)⟩
    · refine Continuous.integrable_of_hasCompactSupport
        (Continuous.mul (f := fun t : ℝ => Real.exp |t|) (by fun_prop) hk.1.norm) ?_
      exact hk.2.mono fun t ht h0 => ht (by simp [h0])
    · rw [norm_smul]
      exact mul_le_mul_of_nonneg_right (exp_bd z hz t) (norm_nonneg _)

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

private theorem act_iff (J : L V →ₗᵢ[ℂ] H) (Y : H →L[ℂ] H) (s : ℂ → V →L[ℂ] V) :
    Act J Y s ↔ ∃ A, RR A s ∧ ∀ x, Y (J x) = J (A x) := by
  constructor
  · rintro ⟨u, κ, hk, h1, h2⟩
    exact ⟨_, ⟨u, _, _, ⟨κ, hk, rfl, rfl⟩, rfl, funext h2⟩, fun x => by
      rw [h1, ContinuousLinearMap.add_apply, opD_apply]⟩
  · rintro ⟨_, ⟨u, _, _, ⟨κ, hk, rfl, rfl⟩, rfl, rfl⟩, h⟩
    exact ⟨u, κ, hk, fun x => by rw [h, ContinuousLinearMap.add_apply, opD_apply], fun z => rfl⟩

private theorem conv_iff (J : L V →ₗᵢ[ℂ] H) (Y : H →L[ℂ] H) {β : ℝ → V →L[ℂ] V} (hk : Ker β) :
    Conv J J Y β ↔ ∀ x, Y (J x) = J (conv β x) := by
  refine ⟨fun h x => h x _ (convSpec β hk x).1, fun h x v hv => ?_⟩
  rw [h]
  congr 1
  refine Lp.ext ?_
  filter_upwards [hv, (convSpec β hk x).1] with t h1 h2
  rw [h1, h2]

end SlopeTestRemainingChoices

theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.actLaws :
    ∀ {H V : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] [CompleteSpace V] (J : L V →ₗᵢ[ℂ] H), Act J 1 (fun _ => 1) ∧ (∀ Y β, Ker β → Conv J J Y β → Act J Y (symb β)) ∧
      (∀ Y s, Act J Y s → (∃ K, SB s K) ∧ ∀ c : ℂ, Act J (c • Y) fun z => c • s z) ∧
      (∀ Y Y' s s', Act J Y s → Act J Y' s' → Act J (Y + Y') (fun z => s z + s' z) ∧ Act J (Y ∘L Y') fun z => s z ∘L s' z) ∧
      ∀ Y Y' β s', Ker β → Conv J J Y β → Act J Y' s' → ∃ κ, Ker κ ∧ Conv J J (Y ∘L Y') κ ∧ ∀ z, symb κ z = symb β z ∘L s' z := by
  intro H V _ _ _ _ _ _ _ J
  simp only [act_iff]
  refine ⟨⟨_, by simpa only [one_smul] using RR_const (V := V) 1, fun x => rfl⟩,
    fun Y β hk h => ⟨_, RR_of_KK ⟨β, hk, rfl, rfl⟩, (conv_iff J Y hk).1 h⟩, ?_, ?_, ?_⟩
  · rintro Y s ⟨A, hA, h⟩
    refine ⟨RR_bd hA, fun c => ⟨c • A, ?_, fun x => by simp [h]⟩⟩
    simpa only [ContinuousLinearMap.smul_comp, ContinuousLinearMap.one_def, ContinuousLinearMap.id_comp] using
      RR_mul (RR_const c) hA
  · rintro Y Y' s s' ⟨A, hA, h⟩ ⟨A', hA', h'⟩
    exact ⟨⟨_, RR_add hA hA', fun x => by simp [h, h']⟩, ⟨_, RR_mul hA hA', fun x => by simp [h, h']⟩⟩
  · rintro Y Y' β s' hk h ⟨A', hA', h'⟩
    obtain ⟨κ, hκ, e1, e2⟩ := KK_RR ⟨β, hk, rfl, rfl⟩ hA'
    refine ⟨κ, hκ, (conv_iff J _ hκ).2 fun x => ?_, fun z => (congrFun e2 z).symm⟩
    rw [← e1, ContinuousLinearMap.comp_apply, h', (conv_iff J Y hk).1 h, ContinuousLinearMap.comp_apply]
