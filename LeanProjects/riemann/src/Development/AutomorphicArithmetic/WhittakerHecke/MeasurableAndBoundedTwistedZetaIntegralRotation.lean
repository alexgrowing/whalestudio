import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.CharacterNorms.FacDefs
import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.CharacterNorms.NzCont
import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.CharacterNorms.XgDefs
import Development.AutomorphicArithmetic.WhittakerHecke.RatIdeleAbsRealIdeleNatIdeleUnitIdeles
import Development.AutomorphicArithmetic.WhittakerHecke.WhittakerFunctionContinuousBoundedEquivariant
import Development.AutomorphicArithmetic.WhittakerHecke.HasSumCoprimeIntegralEqIdeleIntegral
import Development.AutomorphicArithmetic.WhittakerHecke.WhittakerUnipotentTranslateOfInfiniteComponentZe
import Development.AutomorphicArithmetic.WhittakerHecke.RightInvariantBaseChangeUnipotentOfPlacesAboveFi
import Development.AutomorphicArithmetic.WhittakerHecke.ExistsFactorizationOfIdeleCongruenceDivisorLevel
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.RankTwoDescent
open scoped Classical
open UpperTheory.ConvolutionTheory.R2.G (FS2 Rw nE row)
open UpperTheory.V.Af.Smo (EigAt)
open scoped ComplexOrder

private theorem norm_chi {ω χ : HChar ℚ} (hω : Unit1 ω) (h : ∀ a, (χ.1 a * ω.1 a) ^ 2 = 1) (a : (A ℚ)ˣ) :
    ‖((χ.1 a : ℂˣ) : ℂ)‖ = 1 := by
  have h1 := congrArg (fun u : ℂˣ => ‖(u : ℂ)‖) (h a)
  simp only [Units.val_pow_eq_pow_val, Units.val_mul, norm_pow, norm_mul, Units.val_one, norm_one, hω a, mul_one] at h1
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).1 h1

private theorem ab_mul (a b : (A ℚ)ˣ) : ab (a * b) = ab a * ab b := by
  show ((IdeleGroup.ideleModule ℚ (a * b) : {r : ℝ // 0 < r}) : ℝ) = _
  rw [map_mul]
  rfl

private theorem rot_eq {a b : ℝ} (h1 : Real.sin a = Real.sin b) (h2 : Real.cos a = Real.cos b) : rot a = rot b := by
  unfold rot
  congr 2
  apply Subtype.ext
  simp only [h1, h2]

private theorem rot_per (t : ℝ) : ∃ t' ∈ Set.Icc (0 : ℝ) (2 * Real.pi), rot t = rot t' := by
  have hp : Function.Periodic (fun x : ℝ => rot x) (2 * Real.pi) := fun x =>
    rot_eq (Real.sin_add_two_pi x) (Real.cos_add_two_pi x)
  obtain ⟨y, hy, e⟩ := hp.exists_mem_Ico₀ (by positivity) t
  exact ⟨y, ⟨hy.1, hy.2.le⟩, e⟩

private theorem exists_Xr {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] (t : ℝ) : ∃ X, em E (rot t) = infGL E 2 X := by
  refine ⟨GeneralLinearGroup.map (GlobalTheory.CuspRep.pInf E) (em E (rot t)), ?_⟩
  have h1 : GeneralLinearGroup.map (pFin E) (em E (rot t)) = 1 := by
    have h0 : GeneralLinearGroup.map (pFin ℚ) (rot t) = 1 := TR.pFin_infGL _
    refine Units.ext (Matrix.ext fun i j => ?_)
    have hij : pFin ℚ ((rot t).val i j) = ((1 : GL (Fin 2) (Af ℚ)) : Matrix (Fin 2) (Fin 2) (Af ℚ)) i j :=
      congrArg (fun g : GL (Fin 2) (Af ℚ) => g.val i j) h0
    show pFin E (AdeleBaseChange.adeleMap ℚ E ((rot t).val i j)) = _
    rw [AdeleBaseChange.adeleMap_apply]
    show (AdeleBaseChange.finiteAdeleMap ℚ E) (pFin ℚ ((rot t).val i j)) = _
    rw [hij]
    fin_cases i <;> fin_cases j <;> simp
  have := GlobalTheory.CuspRep.infGL_mul_finGL (em E (rot t))
  rw [h1, map_one, mul_one] at this
  exact this.symm

private theorem mul_sg (v : H.P ℚ) (y : A ℚ) (x : H.Kv v) : y * H.sg v x = H.sg v (H.cp v y * x) := by
  refine Prod.ext ?_ (FiniteAdeleRing.ext (K := ℚ) fun w => ?_)
  · show y.1 * 0 = 0
    exact mul_zero _
  · by_cases h : w = v
    · subst h
      show y.2 w * (H.sg w x).2 w = (H.sg w (H.cp w y * x)).2 w
      have a1 : ∀ z : H.Kv w, (H.sg w z).2 w = z := fun z => GroundTheory.Global.finiteAdeleSingleAdd_apply_self w z
      rw [a1, a1]
      rfl
    · show y.2 w * (H.sg v x).2 w = (H.sg v (H.cp v y * x)).2 w
      have a1 : ∀ z : H.Kv v, (H.sg v z).2 w = 0 := fun z => GroundTheory.Global.finiteAdeleSingleAdd_apply_of_ne h z
      rw [a1, a1, mul_zero]

private theorem wo_int {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {D : Dat ℚ E} {P : CuspSub E 2} {ω : HChar ℚ} {L N : ℕ} {φ : GL (Fin 2) (A E) → ℂ} (hA : admitted D ω φ) (hG : Gd D P L N φ)
    (y : (A ℚ)ˣ) (X) (hne : Wo D φ (em E (aE y) * infGL E 2 X) ≠ 0) (v : H.P ℚ) (hv : ¬ Bad N v) :
    Valued.v (H.cp v (y : A ℚ)) ≤ 1 := by
  have hgd := hG.pl v hv
  refine hgd.psi.2.2 _ fun c hc => ?_
  have hfix := UpperTheory.right_invariant_baseChangeUnipotent_of_places_above_fixed E D φ v hgd (fun w hw => (hG.fix w (by rwa [hw])).1) c hc
  have e := UpperTheory.whittaker_unipotent_translate_of_infinite_component_zero E D φ hA.cont hA.left (H.sg v c) rfl y X
  have e' : (fun g => φ (g * Xg.nu D (H.sg v c))) = φ := funext hfix
  rw [e'] at e
  have h1 : ψ (-((y : A ℚ) * H.sg v c)) = 1 := by
    have : (1 : ℂ) * Wo D φ (em E (aE y) * infGL E 2 X) = ψ (-((y : A ℚ) * H.sg v c)) * Wo D φ (em E (aE y) * infGL E 2 X) := by
      rw [one_mul]
      exact e
    exact (mul_right_cancel₀ hne this).symm
  have h2 := Nz.psi_neg_mul ((y : A ℚ) * H.sg v c)
  rw [h1, one_mul, mul_sg, mul_comm] at h2
  exact h2

private theorem key_bd {x B : ℝ} {m : ℕ} {σ : ℝ} {n : ℕ} (hσ : 4 < σ) (hm : σ ≤ m) (hx : 0 < x) (hn : 0 < n) (hB : 0 ≤ B) {w : ℝ}
    (hw : w ≤ B * ((1 + x) ^ (m + 2))⁻¹) :
    w * (x * (n : ℝ)⁻¹) ^ (σ - 1) / x ≤ B * (1 + x) ^ (-(2 : ℝ)) * (n : ℝ) ^ (1 - σ) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have h1x : 0 < 1 + x := by linarith
  have e1 : (x * (n : ℝ)⁻¹) ^ (σ - 1) / x = x ^ (σ - 2) * (n : ℝ) ^ (1 - σ) := by
    rw [Real.mul_rpow hx.le (inv_nonneg.2 hn'.le), Real.inv_rpow hn'.le, ← Real.rpow_neg hn'.le, neg_sub]
    have : x ^ (σ - 1) = x ^ (σ - 2) * x := by
      rw [← Real.rpow_add_one hx.ne']; ring_nf
    rw [this]
    field_simp
  have e2 : x ^ (σ - 2) ≤ (1 + x) ^ m := by
    calc x ^ (σ - 2) ≤ (1 + x) ^ (σ - 2) := Real.rpow_le_rpow hx.le (by linarith) (by linarith)
      _ ≤ (1 + x) ^ (m : ℝ) := Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
      _ = (1 + x) ^ m := Real.rpow_natCast _ _
  have e3 : (1 + x) ^ (-(2 : ℝ)) = ((1 + x) ^ 2)⁻¹ := by
    rw [Real.rpow_neg h1x.le, Real.rpow_two]
  have hnn : 0 ≤ (n : ℝ) ^ (1 - σ) := Real.rpow_nonneg hn'.le _
  rw [mul_div_assoc, e1, ← mul_assoc]
  refine mul_le_mul_of_nonneg_right ?_ hnn
  rw [e3]
  calc w * x ^ (σ - 2) ≤ (B * ((1 + x) ^ (m + 2))⁻¹) * x ^ (σ - 2) :=
        mul_le_mul_of_nonneg_right hw (Real.rpow_nonneg hx.le _)
    _ ≤ (B * ((1 + x) ^ (m + 2))⁻¹) * (1 + x) ^ m := mul_le_mul_of_nonneg_left e2 (by positivity)
    _ = B * ((1 + x) ^ 2)⁻¹ := by
        rw [pow_add]; field_simp

section
variable {E : Type} [Field E] [NumberField E]

private noncomputable def fY (D : Dat ℚ E) (χ : HChar ℚ) (φ : GL (Fin 2) (A E) → ℂ) (s : ℂ) (t : ℝ) (y : IdeleGroup ℚ) : ℂ :=
  Wo D φ (em E (aE y * rot t)) * ((χ.1 y : ℂˣ) : ℂ) * ((ab y : ℝ) : ℂ) ^ (s - 1)

private noncomputable def gY (D : Dat ℚ E) (χ : HChar ℚ) (φ : GL (Fin 2) (A E) → ℂ) (s : ℂ) (n : ℕ) (t r : ℝ) : ℂ :=
  fY D χ φ s t (iy r * pin n) / ((|r| : ℝ) : ℂ)

private theorem gY_zero (D : Dat ℚ E) (χ : HChar ℚ) (φ : GL (Fin 2) (A E) → ℂ) (s : ℂ) (n : ℕ) (t : ℝ) : gY D χ φ s n t 0 = 0 := by
  simp [gY]

private theorem gY_bd (D : Dat ℚ E) {ω χ : HChar ℚ} (hU : Unit1 ω) (hχω : ∀ a, (χ.1 a * ω.1 a) ^ 2 = 1) (φ : GL (Fin 2) (A E) → ℂ)
    {s : ℂ} (hs : 4 < s.re) {m : ℕ} (hm : s.re ≤ m) {B : ℝ} (hB0 : 0 ≤ B)
    (hBt : ∀ (t : ℝ) (y : (A ℚ)ˣ), ‖Wo D φ (em E (aE y * rot t))‖ ≤ B * ((1 + |re y|) ^ (m + 2))⁻¹)
    (n : ℕ) (hn : 0 < n) (t r : ℝ) : ‖gY D χ φ s n t r‖ ≤ (B * (1 + ‖r‖) ^ (-(2 : ℝ))) * (n : ℝ) ^ (1 - s.re) := by
  by_cases hr : r = 0
  · subst hr
    rw [gY_zero, norm_zero]
    exact mul_nonneg (mul_nonneg hB0 (Real.rpow_nonneg (by positivity) _)) (Real.rpow_nonneg (by positivity) _)
  have habs : 0 < |r| := abs_pos.2 hr
  have hab : ab (iy r * pin n) = |r| * (n : ℝ)⁻¹ := by
    rw [ab_mul, UpperTheory.ratIdeleAbs_realIdele_natIdele_unitIdeles.1 r hr, UpperTheory.ratIdeleAbs_realIdele_natIdele_unitIdeles.2.1 n hn]
  have hre := UpperTheory.ratIdeleAbs_realIdele_natIdele_unitIdeles.2.2.2 r n hr hn
  have h1 := hBt t (iy r * pin n)
  rw [hre] at h1
  have h2 := key_bd (σ := s.re) (x := |r|) (n := n) hs hm habs hn hB0 h1
  have hpos : 0 < |r| * (n : ℝ)⁻¹ := by
    have : (0 : ℝ) < n := by exact_mod_cast hn
    positivity
  unfold gY fY
  rw [hab, norm_div, norm_mul, norm_mul, norm_chi hU hχω, mul_one, Complex.norm_real, Real.norm_of_nonneg (abs_nonneg r),
    Complex.norm_cpow_eq_rpow_re_of_pos hpos]
  simp only [Complex.sub_re, Complex.one_re]
  simpa [Real.norm_eq_abs] using h2

private theorem gY_meas (D : Dat ℚ E) (χ : HChar ℚ) {φ : GL (Fin 2) (A E) → ℂ} (hWc : Continuous (Wo D φ)) (s : ℂ) (n : ℕ) :
    Measurable (Function.uncurry (gY D χ φ s n)) := by
  have hS : MeasurableSet ((Set.univ ×ˢ {0}ᶜ : Set (ℝ × ℝ))) :=
    MeasurableSet.univ.prod (measurableSet_singleton 0).compl
  have hc : ContinuousOn (Function.uncurry (gY D χ φ s n)) (Set.univ ×ˢ {0}ᶜ) := by
    rw [continuousOn_iff_continuous_restrict]
    have hi : Continuous fun x : ↥((Set.univ ×ˢ {0}ᶜ : Set (ℝ × ℝ))) => iy x.1.2 * pin n :=
      (Nz.contOn_iy.comp_continuous (continuous_snd.comp continuous_subtype_val) fun x => x.2.2).mul continuous_const
    have hr : Continuous fun x : ↥((Set.univ ×ˢ {0}ᶜ : Set (ℝ × ℝ))) => rot x.1.1 :=
      Nz.cont_rot.comp (continuous_fst.comp continuous_subtype_val)
    have hh : Continuous fun x : ↥((Set.univ ×ˢ {0}ᶜ : Set (ℝ × ℝ))) => em E (aE (iy x.1.2 * pin n) * rot x.1.1) :=
      Nz.cont_em.comp ((continuous_aE.comp hi).mul hr)
    have habc : Continuous fun x : ↥((Set.univ ×ˢ {0}ᶜ : Set (ℝ × ℝ))) => ((ab (iy x.1.2 * pin n) : ℝ) : ℂ) :=
      Complex.continuous_ofReal.comp (continuous_ab.comp hi)
    have hp : Continuous fun x : ↥((Set.univ ×ˢ {0}ᶜ : Set (ℝ × ℝ))) => ((ab (iy x.1.2 * pin n) : ℝ) : ℂ) ^ (s - 1) :=
      habc.cpow continuous_const fun x => Complex.ofReal_mem_slitPlane.2 (ab_pos _)
    have hd : Continuous fun x : ↥((Set.univ ×ˢ {0}ᶜ : Set (ℝ × ℝ))) => ((|x.1.2| : ℝ) : ℂ) :=
      Complex.continuous_ofReal.comp (continuous_abs.comp (continuous_snd.comp continuous_subtype_val))
    refine Continuous.div (((hWc.comp hh).mul (Units.continuous_val.comp (χ.2.1.comp hi))).mul hp) hd fun x => ?_
    have : x.1.2 ≠ 0 := x.2.2
    simpa using this
  have e : Function.uncurry (gY D χ φ s n) = (Set.univ ×ˢ {0}ᶜ : Set (ℝ × ℝ)).piecewise (Function.uncurry (gY D χ φ s n)) 0 := by
    funext p
    by_cases hp : p ∈ (Set.univ ×ˢ {0}ᶜ : Set (ℝ × ℝ))
    · rw [Set.piecewise_eq_of_mem _ _ _ hp]
    · rw [Set.piecewise_eq_of_notMem _ _ _ hp]
      have : p.2 = 0 := by
        by_contra h
        exact hp ⟨Set.mem_univ _, h⟩
      show gY D χ φ s n p.1 p.2 = 0
      rw [this, gY_zero]
  rw [e]
  exact hc.measurable_piecewise continuous_zero.continuousOn hS

private theorem series_core {N : ℕ} {σ : ℝ} (hσ : 4 < σ) {Y : ℝ → ℂ} {c : ℂ} {g : ℕ → ℝ → ℝ → ℂ} {G : ℝ → ℝ}
    (hGi : Integrable G) (hG0 : ∀ r, 0 ≤ G r) (hm : ∀ n, Measurable (Function.uncurry (g n)))
    (hbd : ∀ n : ℕ, 0 < n → ∀ t r, ‖g n t r‖ ≤ G r * (n : ℝ) ^ (1 - σ))
    (hsum : (∀ n : ℕ, 0 < n → ∀ t, Integrable (g n t)) → (∀ t, Summable fun n : {n : ℕ // 0 < n ∧ n.Coprime N} => ∫ r : ℝ, ‖g n t r‖) →
      ∀ t, HasSum (fun n : {n : ℕ // 0 < n ∧ n.Coprime N} => c * ∫ r : ℝ, g n t r) (Y t)) :
    Measurable Y ∧ ∃ C : ℝ, ∀ t : ℝ, ‖Y t‖ ≤ C := by
  have hgm : ∀ n t, Measurable (g n t) := fun n t => (hm n).comp measurable_prodMk_left
  have hgi : ∀ (n : ℕ), 0 < n → ∀ t, Integrable (g n t) := fun n hn t =>
    (hGi.mul_const _).mono' (hgm n t).aestronglyMeasurable (Eventually.of_forall (hbd n hn t))
  have hJ : ∀ (n : ℕ), 0 < n → ∀ t, ∫ r, ‖g n t r‖ ≤ (∫ r, G r) * (n : ℝ) ^ (1 - σ) := by
    intro n hn t
    rw [← integral_mul_const]
    exact integral_mono (hgi n hn t).norm (hGi.mul_const _) (hbd n hn t)
  have hsn : Summable fun n : {n : ℕ // 0 < n ∧ n.Coprime N} => (n : ℝ) ^ (1 - σ) :=
    (Real.summable_nat_rpow.2 (by linarith)).subtype _
  have hs := hsum hgi fun t => Summable.of_nonneg_of_le (fun n => integral_nonneg fun _ => norm_nonneg _)
    (fun n => hJ n n.2.1 t) (hsn.mul_left _)
  refine ⟨?_, ‖c‖ * ((∫ r, G r) * ∑' n : {n : ℕ // 0 < n ∧ n.Coprime N}, (n : ℝ) ^ (1 - σ)), fun t => ?_⟩
  · have ham : ∀ n, Measurable fun t => c * ∫ r : ℝ, g n t r := fun n =>
      ((hm n).stronglyMeasurable.integral_prod_right (ν := volume)).measurable.const_mul _
    refine measurable_of_tendsto_metrizable' (atTop : Filter (Finset {n : ℕ // 0 < n ∧ n.Coprime N}))
      (f := fun (S : Finset {n : ℕ // 0 < n ∧ n.Coprime N}) t => ∑ n ∈ S, c * ∫ r : ℝ, g n t r) (fun S => Finset.measurable_sum S fun n _ => ham n) ?_
    exact tendsto_pi_nhds.2 fun t => hs t
  · refine (hs t).norm_le_of_bounded ((hsn.hasSum.mul_left _).mul_left _) fun n => ?_
    rw [norm_mul]
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
    exact (norm_integral_le_integral_norm _).trans (hJ n n.2.1 t)

end

theorem UpperTheory.measurable_and_bounded_twisted_zeta_integral_rotation :
    ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (D : Dat ℚ E) (P : CuspSub E 2) (ω χ : HChar ℚ),
        CenN P ω → Unit1 ω → (∀ a, (χ.1 a * ω.1 a) ^ 2 = 1) → ∀ (L N : ℕ), ChOk χ L → ∀ φ, admitted D ω φ → Gd D P L N φ → ∀ s : ℂ, 4 < s.re → Measurable (fun t : ℝ => Yt D χ φ s (rot t)) ∧ ∃ C : ℝ, ∀ t : ℝ, ‖Yt D χ φ s (rot t)‖ ≤ C := by
  intro E _ _ _ D P ω χ hCen hU hχω L N hχ φ hA hG s hs
  have hL : 0 < L := Nat.pos_of_dvd_of_pos hG.dvd hG.pos
  obtain ⟨hWc, -, -, -⟩ := UpperTheory.whittakerFunction_continuous_bounded_equivariant E D ω φ hA
  have hC : IsCompact ((fun t => em E (rot t)) '' Set.Icc 0 (2 * Real.pi)) :=
    isCompact_Icc.image (Nz.cont_em.comp Nz.cont_rot)
  obtain ⟨K, -, hK⟩ := hA.wdec _ hC
  obtain ⟨m, hm⟩ := exists_nat_ge s.re
  obtain ⟨B, hB⟩ := hK (m + 2)
  have hBt : ∀ (t : ℝ) (y : (A ℚ)ˣ), ‖Wo D φ (em E (aE y * rot t))‖ ≤ B * ((1 + |re y|) ^ (m + 2))⁻¹ := by
    intro t y
    obtain ⟨t', ht', e⟩ := rot_per t
    have := (hB y (em E (rot t')) ⟨t', ht', rfl⟩).1
    rw [e, map_mul]
    exact this
  have hB0 : 0 ≤ B := by
    have h1 := (norm_nonneg _).trans (hBt 0 1)
    have h2 : 0 < ((1 + |re ((1 : (A ℚ)ˣ) : A ℚ)|) ^ (m + 2))⁻¹ := by positivity
    exact nonneg_of_mul_nonneg_left h1 h2
  refine series_core (N := N) (c := (cT L : ℂ)) (g := gY D χ φ s) (G := fun r => B * (1 + ‖r‖) ^ (-(2 : ℝ))) hs
    ((integrable_one_add_norm (by simp)).const_mul B) (fun r => mul_nonneg hB0 (Real.rpow_nonneg (by positivity) _))
    (gY_meas D χ hWc s) (gY_bd D hU hχω φ hs hm hB0 hBt) ?_
  intro hgi hJ t
  obtain ⟨X, hX⟩ := exists_Xr (E := E) t
  refine UpperTheory.hasSum_coprime_integral_eq_idele_integral L N hL (fY D χ φ s t) ?_ ?_ (fun n => hgi n n.2.1 t) (hJ t)
  · intro τ hτ y
    have hm1 : ab (y * τ) = ab y := by rw [ab_mul, UpperTheory.ratIdeleAbs_realIdele_natIdele_unitIdeles.2.2.1 τ hτ.1, mul_one]
    have hm2 : χ.1 (y * τ) = χ.1 y := by rw [map_mul, hχ τ hτ.1 hτ.2, mul_one]
    have hm3 := hG.tor τ hτ.1 hτ.2 y X
    have e1 : em E (aE (y * τ) * rot t) = em E (aE (y * τ)) * infGL E 2 X := by rw [map_mul, hX]
    have e2 : em E (aE y * rot t) = em E (aE y) * infGL E 2 X := by rw [map_mul, hX]
    unfold fY
    rw [e1, e2, hm1, hm2, hm3]
  · intro y hy
    have h1 : Wo D φ (em E (aE y) * infGL E 2 X) ≠ 0 := by
      intro h0
      apply hy
      unfold fY
      rw [map_mul, hX, h0, zero_mul, zero_mul]
    exact UpperTheory.exists_factorization_of_ideleCongruence_divisor_level L N hG.pos hG.dvd hG.same y (hG.supp y X h1) (fun v hv => wo_int hA hG y X h1 v hv)
