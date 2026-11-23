import PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.TorusKernels.IsHolVOf
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.PerDeriv
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.ScalarStabilizers.Trzero
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.EisensteinSmoothContinuous
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.PeriodicIntegralFundamentalDomainInvariant
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.EisensteinPeriodDerivative
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.EisensteinConstantTermUpperBlock
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.EisensteinConstantTermOfPeriodMeanOfUpperBlock
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.ConstantTermAutomorphy
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.EisensteinLieAlgebraAction

noncomputable section

open NumberField MeasureTheory Topology Matrix Neutral.B1 Formalism.L2.Host GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Sd UpperTheory.V.Sd.Eis

namespace UpperTheory.Esk.ArchimedeanConjugationLemmas

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F]

theorem map_aff1 {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) (x : R) :
    GeneralLinearGroup.map f (aff 1 x) = aff 1 (f x) := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [aff]

theorem aff_one_zero {R : Type} [CommRing R] : aff (1 : Rˣ) (0 : R) = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [aff]

theorem aff_mul {R : Type} [CommRing R] (y y' : Rˣ) (x x' : R) : aff y x * aff y' x' = aff (y * y') (y * x' + x) := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [aff, Matrix.mul_apply, Fin.sum_univ_succ]

theorem infGL_aff (x : TR.Rinf F) : TR.infGL F 2 (aff 1 x) = aff 1 (TR.sInf F x) := by
  refine TR.ga_ext ?_ ?_
  · rw [TR.pInf_infGL, map_aff1]
    exact congrArg _ ((TR.infEq F).symm_apply_apply x).symm
  · rw [TR.pFin_infGL, map_aff1]
    exact aff_one_zero.symm

theorem infGL_left (a : GL (Fin 2) (TR.Rinf F)) (g : GA F 2) :
    TR.infGL F 2 a * g = g * TR.infGL F 2 ((GeneralLinearGroup.map (TR.pInf F) g)⁻¹ * a * GeneralLinearGroup.map (TR.pInf F) g) :=
  TR.ga_ext (by simp only [map_mul, map_inv, TR.pInf_infGL]; group) (by simp only [map_mul, map_inv, TR.pFin_infGL]; group)

omit [IsTotallyReal F] in
theorem conj_deriv (h : GL (Fin 2) (TR.Rinf F)) (a : ℝ → GL (Fin 2) (TR.Rinf F)) (X : Matrix (Fin 2) (Fin 2) (TR.Rinf F))
    (ha : HasDerivAt (fun t => TR.toL (a t).val) (TR.toL X) 0) :
    HasDerivAt (fun t => TR.toL (h⁻¹ * a t * h).val) (TR.toL ((h⁻¹).val * X * h.val)) 0 :=
  ((TR.rmul (TR.toL h.val)).comp (TR.lmul (TR.toL (h⁻¹).val))).hasFDerivAt.comp_hasDerivAt (0 : ℝ) ha

open Classical in
omit [IsTotallyReal F] in
theorem conj_dec (h : GL (Fin 2) (TR.Rinf F)) (i j : Fin 2) (u : TR.Rinf F) :
    TR.toL ((h⁻¹).val * Matrix.single i j u * h.val) = ∑ v, u v • ∑ a, ∑ b,
      ((((GeneralLinearGroup.map (Pi.evalRingHom (fun _ => ℝ) v) h)⁻¹).val * Matrix.single i j (1 : ℝ) *
        (GeneralLinearGroup.map (Pi.evalRingHom (fun _ => ℝ) v) h).val) a b : ℝ) •
          TR.toL (Matrix.single a b (Pi.single v 1 : TR.Rinf F)) := by
  funext a b w
  simp only [← map_inv]
  generalize h⁻¹ = h'
  fin_cases a <;> fin_cases b <;> fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Matrix.single_apply, Fin.sum_univ_two, Pi.single_apply, Finset.sum_apply] <;> ring

omit [IsTotallyReal F] in
theorem nil_curve (u : TR.Rinf F) :
    Continuous (fun t : ℝ => aff (1 : (TR.Rinf F)ˣ) (t • u)) ∧
    (∀ s t : ℝ, aff (1 : (TR.Rinf F)ˣ) ((s + t) • u) = aff 1 (s • u) * aff 1 (t • u)) ∧
    HasDerivAt (fun t : ℝ => TR.toL (aff (1 : (TR.Rinf F)ˣ) (t • u)).val) (TR.toL (Matrix.single 0 1 u)) 0 := by
  refine ⟨Units.continuous_iff.2 ⟨?_, ?_⟩, fun s t => ?_, ?_⟩
  · refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp [aff] <;> fun_prop
  · refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp [aff, -Matrix.coe_units_inv] <;> fun_prop
  · ext i j : 2
    fin_cases i <;> fin_cases j <;> simp [aff, add_smul, add_comm]
  · refine hasDerivAt_pi.2 fun i => hasDerivAt_pi.2 fun j => ?_
    fin_cases i <;> fin_cases j <;> simp [aff, hasDerivAt_const]
    simpa using (hasDerivAt_id (0 : ℝ)).smul_const u

omit [IsTotallyReal F] in
theorem tor_curve (u : TR.Rinf F) (y : ℝ → (TR.Rinf F)ˣ) (hy : ∀ t v, (y t).val v = Real.exp (t * u v)) :
    Continuous (fun t : ℝ => aff (y t) 0) ∧
    (∀ s t : ℝ, aff (y (s + t)) 0 = aff (y s) 0 * aff (y t) 0) ∧
    HasDerivAt (fun t : ℝ => TR.toL (aff (y t) 0).val) (TR.toL (Matrix.single 0 0 u)) 0 := by
  have e : ∀ t, (y t).val = fun v => Real.exp (t * u v) := fun t => funext (hy t)
  have e' : ∀ t, ((y t)⁻¹).val = fun v => Real.exp (-(t * u v)) := fun t =>
    Units.inv_eq_of_mul_eq_one_right (by funext v; simp [hy, ← Real.exp_add])
  refine ⟨Units.continuous_iff.2 ⟨?_, ?_⟩, fun s t => ?_, ?_⟩
  · refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp [aff, e] <;> fun_prop
  · refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp [aff, -Matrix.coe_units_inv, e'] <;> fun_prop
  · ext i j v
    fin_cases i <;> fin_cases j <;> simp [aff, hy, add_mul, Real.exp_add]
  · refine hasDerivAt_pi.2 fun i => hasDerivAt_pi.2 fun j => ?_
    fin_cases i <;> fin_cases j <;> simp [aff, hasDerivAt_const]
    refine hasDerivAt_pi.2 fun v => ?_
    simpa [hy] using ((hasDerivAt_id (0 : ℝ)).mul_const (u v)).exp

theorem ctLeftV [MeasurableSpace (NA F)] [BorelSpace (NA F)] (μ : Measure (NA F)) [μ.IsAddHaarMeasure] (D : Set (NA F))
    (hD : IsAddFundamentalDomain (ratN F 2 1) D μ) (k : InfinitePlace F → ℕ) (c : Pl F → ℕ) (ω : HChar F)
    (hω : IsOfFinOrder ω) (φ : TR.Sm F 2) (hφ : UpperTheory.Esk.IsHolV k c ω φ) (u : TR.Rinf F) (y : ℝ → (TR.Rinf F)ˣ)
    (hy : ∀ t v, (y t).val v = Real.exp (t * u v)) (g : GA F 2) :
    HasDerivAt (fun t => cterm μ D φ.1 (TR.infGL F 2 (aff (y t) 0) * g))
      ((∑ v, (k v : ℂ) / 2 * ((u v : ℝ) : ℂ)) * cterm μ D φ.1 g) 0 := by
  classical
  have hS := UpperTheory.eisenstein_smooth_continuous
  have hB := UpperTheory.eisenstein_constantTerm_of_periodMean_of_upperBlock UpperTheory.periodic_integral_fundamentalDomain_invariant UpperTheory.eisenstein_constantTerm_upperBlock
  have hL := UpperTheory.constant_term_automorphy UpperTheory.eisenstein_smooth_continuous UpperTheory.periodic_integral_fundamentalDomain_invariant UpperTheory.eisenstein_period_derivative UpperTheory.eisenstein_constantTerm_upperBlock
  have hA := UpperTheory.eisenstein_lie_algebra_action
  have hl := hL F μ D hD φ hφ.aut.left hφ.aut.level
  have hb := hB F μ D hD φ.1 (hS F 2 φ hφ.aut.level) hφ.aut.left
  have hi : ∀ X, IntegrableOn (fun x : NA F => (TR.lie F 2 X φ).1 (unip x * g)) D μ := fun X =>
    (hB F μ D hD _ (hl X).1.2 (hl X).1.1).1 g
  let L : TR.Lie F 2 →ₗ[ℝ] ℂ :=
    { toFun := fun X => cterm μ D (TR.lie F 2 X φ).1 g
      map_add' := fun X Y => by
        rw [map_add]
        exact integral_add (hi X) (hi Y)
      map_smul' := fun r X => by
        rw [map_smul]
        exact integral_smul r (fun x : NA F => (TR.lie F 2 X φ).1 (unip x * g)) }
  have hsm : ∀ (X) (z : ℂ) (ψ : TR.Sm F 2), TR.lie F 2 X φ = z • ψ → L X = z * cterm μ D ψ.1 g := fun X z ψ e => by
    change cterm μ D (TR.lie F 2 X φ).1 g = _
    rw [e]
    exact integral_const_mul z (fun x : NA F => ψ.1 (unip x * g))
  set h := GeneralLinearGroup.map (TR.pInf F) g with hh
  have key : ∀ (a : ℝ → GL (Fin 2) (TR.Rinf F)) (X : Matrix (Fin 2) (Fin 2) (TR.Rinf F)), Continuous a →
      (∀ s t, a (s + t) = a s * a t) → HasDerivAt (fun t => TR.toL (a t).val) (TR.toL X) 0 →
      HasDerivAt (fun t => cterm μ D φ.1 (TR.infGL F 2 (a t) * g)) (L (TR.toL ((h⁻¹).val * X * h.val))) 0 := by
    intro a X h1 h2 h3
    simp only [infGL_left _ g]
    exact (hl _).2 (fun t => h⁻¹ * a t * h) (by fun_prop) (fun s t => by rw [h2]; group) (conj_deriv h a X h3) g
  have hnil : ∀ x : TR.Rinf F, L (TR.toL ((h⁻¹).val * Matrix.single 0 1 x * h.val)) = 0 := fun x => by
    obtain ⟨h1, h2, h3⟩ := nil_curve x
    have := key _ _ h1 h2 h3
    simp only [infGL_aff, hb.2.1] at this
    exact this.unique (hasDerivAt_const _ _)
  let E : InfinitePlace F → Fin 2 → Fin 2 → TR.Lie F 2 := fun v a b => TR.toL (Matrix.single a b (Pi.single v 1 : TR.Rinf F))
  have hE : ∀ v a b, TR.lie F 2 (E v a b) = TR.Eop v a b := fun _ _ _ => by
    simp only [E, TR.Eop]
  have hdec : ∀ (i j : Fin 2) (x : TR.Rinf F), L (TR.toL ((h⁻¹).val * Matrix.single i j x * h.val)) =
      ∑ v, (x v : ℂ) * ∑ a, ∑ b,
      ((((GeneralLinearGroup.map (Pi.evalRingHom (fun _ => ℝ) v) h)⁻¹).val * Matrix.single i j (1 : ℝ) *
        (GeneralLinearGroup.map (Pi.evalRingHom (fun _ => ℝ) v) h).val) a b : ℝ) * L (E v a b) := fun i j x => by
    rw [conj_dec]
    simp only [map_sum, map_smul, Complex.real_smul, E]
  have hv := fun v : InfinitePlace F => hA (GeneralLinearGroup.map (Pi.evalRingHom (fun _ => ℝ) v) h) (fun a b => L (E v a b))
    ((k v : ℂ) * cterm μ D φ.1 g)
    (by
      rw [← map_add, hsm _ 0 φ, zero_mul]
      rw [map_add, hE, hE, zero_smul]
      exact UpperTheory.V.Sd.Hm.trzero F ω hω φ hφ.cent v)
    (by
      rw [← map_sub, hsm _ (Complex.I * (k v : ℂ)) φ, mul_assoc]
      rw [map_sub, hE, hE]
      exact hφ.wt v)
    (by
      rw [← map_sub, ← map_add, hsm _ Complex.I (TR.lie F 2 (E v 0 1 + E v 1 0) φ)]
      · rfl
      rw [map_sub, map_add, hE, hE, hE, hE]
      exact hφ.low v)
    (by
      have := hnil (Pi.single v 1)
      rw [hdec, Finset.sum_eq_single v (fun w _ hw => by simp [Pi.single_eq_of_ne hw]) (by simp)] at this
      simpa only [Pi.single_eq_same, Complex.ofReal_one, one_mul] using this)
  obtain ⟨h1, h2, h3⟩ := tor_curve u y hy
  have := key _ _ h1 h2 h3
  rw [hdec] at this
  simp only [hv] at this
  convert this using 1
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun v _ => ?_
  ring

theorem ode {f : ℝ → ℂ} {κ : ℂ} (h : ∀ t, HasDerivAt f (κ * f t) t) : f 1 = Complex.exp κ * f 0 := by
  have h1 : ∀ t : ℝ, HasDerivAt (fun t : ℝ => Complex.exp (-κ * t) * f t) 0 t := fun t => by
    have := (((Complex.ofRealCLM.hasDerivAt (x := t)).const_mul (-κ)).cexp).mul (h t)
    refine this.congr_deriv ?_
    simp only [Complex.ofRealCLM_apply, Complex.ofReal_one]; ring
  have h2 := is_const_of_deriv_eq_zero (fun t => (h1 t).differentiableAt) (fun t => (h1 t).deriv) 1 0
  simp only [Complex.ofReal_one, mul_one, Complex.ofReal_zero, mul_zero, Complex.exp_zero, one_mul] at h2
  rw [← h2, ← mul_assoc, ← Complex.exp_add]; simp

theorem ct_grow [MeasurableSpace (NA F)] [BorelSpace (NA F)] (μ : Measure (NA F)) [μ.IsAddHaarMeasure] (D : Set (NA F))
    (hD : IsAddFundamentalDomain (ratN F 2 1) D μ) (k : InfinitePlace F → ℕ) (c : Pl F → ℕ) (ω : HChar F)
    (hω : IsOfFinOrder ω) (φ : TR.Sm F 2) (hφ : UpperTheory.Esk.IsHolV k c ω φ) (T : ℝ) (g : GA F 2) :
    ∃ g' : GA F 2, cterm μ D φ.1 g' = Complex.exp (∑ v, (k v : ℂ) / 2 * ((T : ℝ) : ℂ)) * cterm μ D φ.1 g := by
  let z : ℝ → (TR.Rinf F)ˣ := fun t => ⟨fun _ => Real.exp (t * T), fun _ => Real.exp (-(t * T)),
    by funext v; simp [← Real.exp_add], by funext v; simp [← Real.exp_add]⟩
  have hz : ∀ s t, z (s + t) = z s * z t := fun s t => Units.ext (funext fun v => by simp [z, add_mul, Real.exp_add])
  have h0 : z 0 = 1 := Units.ext (funext fun v => by simp [z])
  have := ode (f := fun t => cterm μ D φ.1 (TR.infGL F 2 (aff (z t) 0) * g))
    (κ := ∑ v, (k v : ℂ) / 2 * ((T : ℝ) : ℂ)) fun t => by
    have h2 := ctLeftV μ D hD k c ω hω φ hφ (fun _ => T) z (fun _ _ => rfl) (TR.infGL F 2 (aff (z t) 0) * g)
    have h3 := HasDerivAt.comp_sub_const t t (by rw [sub_self]; exact h2)
    refine h3.congr_of_eventuallyEq (Filter.Eventually.of_forall fun s => ?_)
    beta_reduce
    rw [← mul_assoc, ← map_mul, aff_mul, ← hz]; simp
  refine ⟨_, this.trans ?_⟩
  rw [h0, aff_one_zero, map_one, one_mul]

theorem ct_zero [MeasurableSpace (NA F)] [BorelSpace (NA F)] (μ : Measure (NA F)) [μ.IsAddHaarMeasure] (D : Set (NA F))
    (hD : IsAddFundamentalDomain (ratN F 2 1) D μ) (k : InfinitePlace F → ℕ) (c : Pl F → ℕ) (ω : HChar F)
    (hω : IsOfFinOrder ω) (φ : TR.Sm F 2) (hφ : UpperTheory.Esk.IsHolV k c ω φ) (hk : ∀ v, 1 ≤ k v) (C : ℝ)
    (hC : ∀ g, ‖φ.1 g‖ ≤ C) (g : GA F 2) : cterm μ D φ.1 g = 0 := by
  obtain ⟨i1, i2, i3, i4, hco, -, -⟩ := UpperTheory.eisenstein_constantTerm_upperBlock F
  have hfin : μ D ≠ ⊤ := (UpperTheory.periodic_integral_fundamentalDomain_invariant (NA F) (ratN F 2 1) hco μ D hD).1
  set M := C * μ.real D
  have hb : ∀ h, ‖cterm μ D φ.1 h‖ ≤ M := fun h =>
    norm_setIntegral_le_of_norm_le_const (lt_top_iff_ne_top.2 hfin) (fun x _ => hC _)
  set s : ℝ := ∑ v, (k v : ℝ) / 2
  obtain ⟨v₀⟩ : Nonempty (InfinitePlace F) := inferInstance
  have hs : 0 < s := by
    have : (k v₀ : ℝ) / 2 ≤ s := Finset.single_le_sum (f := fun v => (k v : ℝ) / 2) (fun v _ => by positivity) (Finset.mem_univ v₀)
    have h1 : (1 : ℝ) ≤ k v₀ := by exact_mod_cast hk v₀
    linarith
  by_contra hne
  have ha : 0 < ‖cterm μ D φ.1 g‖ := norm_pos_iff.2 hne
  set a := ‖cterm μ D φ.1 g‖
  set T : ℝ := (|M| + 1) / (a * s)
  obtain ⟨g', hg'⟩ := ct_grow μ D hD k c ω hω φ hφ T g
  have e : (∑ v, (k v : ℂ) / 2 * ((T : ℝ) : ℂ)) = ((s * T : ℝ) : ℂ) := by
    simp only [s, Finset.sum_mul]; push_cast; rfl
  have h1 := hb g'
  rw [hg', e, norm_mul, Complex.norm_exp_ofReal] at h1
  have h2 : s * T + 1 ≤ Real.exp (s * T) := Real.add_one_le_exp _
  have h3 : s * T * a = |M| + 1 := by
    simp only [T]; field_simp
  have h4 : M ≤ |M| := le_abs_self M
  nlinarith

end UpperTheory.Esk.ArchimedeanConjugationLemmas

theorem UpperTheory.Esk.pf_H2e : UpperTheory.Esk.H2e := by
  intro F _ _ _ k c ω φ hω hk hφ hC
  obtain ⟨C, hC⟩ := hC
  refine ⟨hφ.aut, ?_⟩
  intro r h0 h1 _ _ μ D hμ hD g
  obtain rfl : r = 1 := by omega
  exact UpperTheory.Esk.ArchimedeanConjugationLemmas.ct_zero μ D hD k c ω hω φ hφ hk C hC g
