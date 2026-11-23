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

private theorem ae_ne' : ∀ᵐ y : ℝ, y ≠ 0 := compl_mem_ae_iff.2 (measure_singleton (0 : ℝ))

private theorem norm_chi' {ω χ : HChar ℚ} (hω : Unit1 ω) (h : ∀ a, (χ.1 a * ω.1 a) ^ 2 = 1) (a : (A ℚ)ˣ) :
    ‖((χ.1 a : ℂˣ) : ℂ)‖ = 1 := by
  have h1 := congrArg (fun u : ℂˣ => ‖(u : ℂ)‖) (h a)
  simp only [Units.val_pow_eq_pow_val, Units.val_mul, norm_pow, norm_mul, Units.val_one, norm_one, hω a, mul_one] at h1
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).1 h1

private theorem ab_mul' (a b : (A ℚ)ˣ) : ab (a * b) = ab a * ab b := by
  simp [ab, map_mul]

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

private theorem cpid (s : ℂ) {r a : ℝ} (hr : r ≠ 0) (ha : 0 < a) :
    (((|r| * a : ℝ) : ℂ)) ^ (s - 1) / ((|r| : ℝ) : ℂ) = ((|r| : ℝ) : ℂ) ^ (s - 2) * (a : ℂ) ^ (s - 1) := by
  have h0 : 0 < |r| := abs_pos.2 hr
  have h0c : ((|r| : ℝ) : ℂ) ≠ 0 := by exact_mod_cast h0.ne'
  have e : s - 2 = (s - 1) - 1 := by ring
  have e4 : ((|r| : ℝ) : ℂ) ^ (s - 2) = ((|r| : ℝ) : ℂ) ^ (s - 1) / ((|r| : ℝ) : ℂ) := by
    rw [e, Complex.cpow_sub _ _ h0c, Complex.cpow_one]
  rw [Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg h0.le ha.le, e4, mul_div_right_comm]

private theorem core {s : ℂ} (hs : 4 < s.re) {W c : ℂ} {r a B : ℝ} (hr : r ≠ 0) (ha : 0 < a) (hc : ‖c‖ = 1)
    (hW : ‖W‖ ≤ B * ((1 + |r|) ^ (⌈s.re⌉₊ + 2))⁻¹) :
    ‖W * c * (((|r| * a : ℝ) : ℂ)) ^ (s - 1) / ((|r| : ℝ) : ℂ)‖ ≤ a ^ (s.re - 1) * (B * (1 + r ^ 2)⁻¹) := by
  have hy0 : 0 < |r| := abs_pos.2 hr
  set m := ⌈s.re⌉₊ with hm
  set b := 1 + |r| with hb
  have hb1 : 1 ≤ b := by rw [hb]; linarith
  have hb0 : 0 < b := by linarith
  have hyb : |r| ≤ b := by rw [hb]; linarith
  have hσ : 0 ≤ s.re - 2 := by linarith
  have hm' : s.re - 2 ≤ (m : ℝ) := by
    have := Nat.le_ceil s.re
    rw [← hm] at this
    linarith
  have e1 : |r| ^ (s.re - 2) ≤ b ^ m := by
    calc |r| ^ (s.re - 2) ≤ b ^ (s.re - 2) := Real.rpow_le_rpow hy0.le hyb hσ
      _ ≤ b ^ (m : ℝ) := Real.rpow_le_rpow_of_exponent_le hb1 hm'
      _ = b ^ m := Real.rpow_natCast b m
  have e3 : 1 + r ^ 2 ≤ b ^ 2 := by
    rw [hb]
    nlinarith [abs_nonneg r, sq_abs r]
  have hB : 0 ≤ B := by
    have h1 : 0 ≤ B * (b ^ (m + 2))⁻¹ := (norm_nonneg _).trans hW
    have h2 : 0 < (b ^ (m + 2))⁻¹ := by positivity
    exact nonneg_of_mul_nonneg_left h1 h2
  have e2 : ‖W * c * (((|r| * a : ℝ) : ℂ)) ^ (s - 1) / ((|r| : ℝ) : ℂ)‖ = ‖W‖ * (|r| ^ (s.re - 2) * a ^ (s.re - 1)) := by
    rw [mul_div_assoc, cpid s hr ha, norm_mul, norm_mul, hc, mul_one, norm_mul,
      Complex.norm_cpow_eq_rpow_re_of_pos hy0, Complex.norm_cpow_eq_rpow_re_of_pos ha]
    simp
  rw [e2]
  have ha' : 0 ≤ a ^ (s.re - 1) := Real.rpow_nonneg ha.le _
  calc ‖W‖ * (|r| ^ (s.re - 2) * a ^ (s.re - 1))
      ≤ (B * (b ^ (m + 2))⁻¹) * (b ^ m * a ^ (s.re - 1)) := by gcongr
    _ = a ^ (s.re - 1) * (B * (b ^ 2)⁻¹) := by
        field_simp
        ring
    _ ≤ a ^ (s.re - 1) * (B * (1 + r ^ 2)⁻¹) := by gcongr

section
variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E]

private theorem ex_X (t : ℝ) : ∃ X, infGL E 2 X = em E (rot t) := by
  have h := infGL_mul_finGL (E := E) (a := 2) (em E (rot t))
  have e2 : ∀ i j, ((rot t).val i j).2 = ((1 : Matrix (Fin 2) (Fin 2) (A ℚ)) i j).2 := by
    intro i j
    have e : (rot t).val i j = (1 : Matrix (Fin 2) (Fin 2) (A ℚ)) i j - TR.sInf ℚ ((1 : Matrix (Fin 2) (Fin 2) (TR.Rinf ℚ)) i j) +
        TR.sInf ℚ ((Nz.X t).val i j) := by
      rw [Nz.rot_eq]
      rfl
    rw [e]
    show ((1 : Matrix (Fin 2) (Fin 2) (A ℚ)) i j).2 - 0 + 0 = _
    simp
  have h1 : Matrix.GeneralLinearGroup.map (pFin E) (em E (rot t)) = 1 := by
    refine Units.ext (Matrix.ext fun i j => ?_)
    have e3 : (AdeleBaseChange.adeleMap ℚ E ((rot t).val i j)).2 = (AdeleBaseChange.adeleMap ℚ E ((1 : Matrix (Fin 2) (Fin 2) (A ℚ)) i j)).2 := by
      rw [AdeleBaseChange.adeleMap_apply, AdeleBaseChange.adeleMap_apply, e2]
    change (AdeleBaseChange.adeleMap ℚ E ((rot t).val i j)).2 = _
    rw [e3]
    fin_cases i <;> fin_cases j <;> simp [Matrix.one_apply] <;> rfl
  rw [h1, map_one, mul_one] at h
  exact ⟨_, h⟩

private theorem wo_int {D : Dat ℚ E} {P : CuspSub E 2} {ω : HChar ℚ} {L N : ℕ} {φ : GL (Fin 2) (A E) → ℂ} (hA : admitted D ω φ) (hG : Gd D P L N φ)
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
end

theorem UpperTheory.has_sum_twisted_zeta_integral_dirichlet_series :
    ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (D : Dat ℚ E) (P : CuspSub E 2) (ω χ : HChar ℚ),
        CenN P ω → Unit1 ω → (∀ a, (χ.1 a * ω.1 a) ^ 2 = 1) → ∀ (L N : ℕ), ChOk χ L → ∀ φ, admitted D ω φ → Gd D P L N φ → ∀ μ : ℕ → ℂ, (∀ n, 0 < n → n.Coprime N → ∀ r t : ℝ, r ≠ 0 →
          Wo D φ (em E (aE (iy r * pin n) * rot t)) = μ n * Wo D φ (em E (aE (iy r) * rot t))) →
        ∀ s : ℂ, 4 < s.re → ∀ t : ℝ,
        HasSum (fun n : {n : ℕ // 0 < n ∧ n.Coprime N} => (cT L : ℂ) * (μ n * ((χ.1 (pin n) : ℂˣ) : ℂ) * (n : ℂ) ^ (1 - s)) * It D χ φ s t)
          (Yt D χ φ s (rot t)) := by
  intro E _ _ _ D P ω χ hCen hU hχω L N hχ φ hA hG μ hμ s hs t
  have hLpos : 0 < L := Nat.pos_of_dvd_of_pos hG.dvd hG.pos
  have nχ := norm_chi' hU hχω
  obtain ⟨X, hX⟩ := ex_X (E := E) t
  obtain ⟨hab1, hab2, hab3, hab4⟩ := UpperTheory.ratIdeleAbs_realIdele_natIdele_unitIdeles
  obtain ⟨f, hf⟩ : ∃ f : IdeleGroup ℚ → ℂ, f = fun y => Wo D φ (em E (aE y * rot t)) * ((χ.1 y : ℂˣ) : ℂ) * ((ab y : ℝ) : ℂ) ^ (s - 1) := ⟨_, rfl⟩
  have hW : ∀ y : (A ℚ)ˣ, Wo D φ (em E (aE y * rot t)) = Wo D φ (em E (aE y) * infGL E 2 X) := fun y => by rw [map_mul, hX]
  have hinv : ∀ τ ∈ TT L, ∀ y : IdeleGroup ℚ, f (y * τ) = f y := by
    intro τ hτ y
    have h1 : χ.1 τ = 1 := hχ τ hτ.1 hτ.2
    have h2 : ab τ = 1 := hab3 τ hτ.1
    simp only [hf]
    rw [hW, hW y, hG.tor τ hτ.1 hτ.2 y X, map_mul, h1, mul_one, ab_mul', h2, mul_one]
  have hsupp : ∀ y : IdeleGroup ℚ, f y ≠ 0 → ∃ (n : ℕ) (r : ℝ) (τ : (A ℚ)ˣ), 0 < n ∧ n.Coprime N ∧ r ≠ 0 ∧ τ ∈ TT L ∧ y = iy r * pin n * τ := by
    intro y hy
    have hne : Wo D φ (em E (aE y) * infGL E 2 X) ≠ 0 := by
      intro h0
      apply hy
      simp only [hf]
      rw [hW, h0]
      simp
    exact UpperTheory.exists_factorization_of_ideleCongruence_divisor_level L N hG.pos hG.dvd hG.same y (hG.supp y X hne) (fun v hv => wo_int hA hG y X hne v hv)
  obtain ⟨K, -, hK⟩ := hA.wdec {em E (rot t)} isCompact_singleton
  obtain ⟨B0, hB0⟩ := hK (⌈s.re⌉₊ + 2)
  have hb : ∀ y : (A ℚ)ˣ, ‖Wo D φ (em E (aE y * rot t))‖ ≤ |B0| * ((1 + |re y|) ^ (⌈s.re⌉₊ + 2))⁻¹ := by
    intro y
    have h1 := (hB0 y (em E (rot t)) rfl).1
    rw [← map_mul] at h1
    exact h1.trans (mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity))
  obtain ⟨G, hGd⟩ : ∃ G : ℝ → ℂ, G = fun y => Wo D φ (em E (aE (iy y) * rot t)) * ((χ.1 (iy y) : ℂˣ) : ℂ) * (y : ℂ) ^ 0 * ((|y| : ℝ) : ℂ) ^ (s - 2) := ⟨_, rfl⟩
  have hGmeas : AEStronglyMeasurable G volume := by
    have hcont : ContinuousOn G ({0}ᶜ : Set ℝ) := by
      refine continuousOn_iff_continuous_restrict.2 ?_
      have ci : Continuous fun y : ({0}ᶜ : Set ℝ) => iy y.1 := continuousOn_iff_continuous_restrict.1 Nz.contOn_iy
      have h1 : Continuous fun y : ({0}ᶜ : Set ℝ) => Wo D φ (em E (aE (iy y.1) * rot t)) :=
        Nz.cont_Wo D hA.cont hA.bdd (Nz.cont_em.comp ((continuous_aE.comp ci).mul continuous_const))
      have h2 : Continuous fun y : ({0}ᶜ : Set ℝ) => ((χ.1 (iy y.1) : ℂˣ) : ℂ) :=
        Units.continuous_val.comp (χ.2.1.comp ci)
      have h3 : Continuous fun y : ({0}ᶜ : Set ℝ) => ((y.1 : ℝ) : ℂ) ^ 0 :=
        (Complex.continuous_ofReal.comp continuous_subtype_val).pow 0
      have h4 : Continuous fun y : ({0}ᶜ : Set ℝ) => (((|y.1| : ℝ)) : ℂ) ^ (s - 2) :=
        Continuous.cpow (Complex.continuous_ofReal.comp (continuous_abs.comp continuous_subtype_val))
          continuous_const fun y => Complex.ofReal_mem_slitPlane.2 (abs_pos.2 y.2)
      rw [hGd]
      exact ((h1.mul h2).mul h3).mul h4
    have h := hcont.aestronglyMeasurable (μ := volume) (measurableSet_singleton (0 : ℝ)).compl
    rwa [Measure.restrict_eq_self_of_ae_mem (s := ({0}ᶜ : Set ℝ)) ae_ne'] at h
  have hGb : ∀ r : ℝ, r ≠ 0 → ‖G r‖ ≤ |B0| * (1 + r ^ 2)⁻¹ := by
    intro r hr
    have h1 := core hs (W := Wo D φ (em E (aE (iy r) * rot t))) (c := ((χ.1 (iy r) : ℂˣ) : ℂ)) (a := 1) hr one_pos (nχ _)
      (by simpa only [Nz.re_iy hr] using hb (iy r))
    rw [mul_div_assoc, cpid s hr one_pos] at h1
    simpa [hGd] using h1
  have hGint : Integrable G := by
    refine Integrable.mono' (integrable_inv_one_add_sq.const_mul |B0|) hGmeas ?_
    filter_upwards [ae_ne'] with y hy using hGb y hy
  have hev : ∀ n : {n : ℕ // 0 < n ∧ n.Coprime N}, ∀ r : ℝ, r ≠ 0 → f (iy r * pin n) / ((|r| : ℝ) : ℂ) =
      (μ n * ((χ.1 (pin n) : ℂˣ) : ℂ) * (n : ℂ) ^ (1 - s)) * G r := by
    intro n r hr
    have hn0 : (0 : ℝ) < (n : ℕ) := by exact_mod_cast n.2.1
    have hn1 : 0 < ((n : ℕ) : ℝ)⁻¹ := inv_pos.2 hn0
    have hab : ab (iy r * pin n) = |r| * ((n : ℕ) : ℝ)⁻¹ := by
      rw [ab_mul', hab1 r hr, hab2 n n.2.1]
    have hc : (((((n : ℕ) : ℝ)⁻¹ : ℝ)) : ℂ) ^ (s - 1) = (((n : ℕ)) : ℂ) ^ (1 - s) := by
      rw [Complex.ofReal_inv, Complex.ofReal_natCast, Complex.inv_cpow _ _ (by simp [Complex.natCast_arg, Real.pi_ne_zero.symm]), ← Complex.cpow_neg]
      congr 1
      ring
    simp only [hf, hGd]
    have hχm : χ.1 (iy r * pin n) = χ.1 (iy r) * χ.1 (pin n) := map_mul _ _ _
    rw [hμ n n.2.1 n.2.2 r t hr, hab, mul_div_assoc, cpid s hr hn1, hc, hχm]
    simp only [Units.val_mul, pow_zero, mul_one]
    ring
  have hFint : ∀ n : {n : ℕ // 0 < n ∧ n.Coprime N}, Integrable (fun r : ℝ => f (iy r * pin n) / ((|r| : ℝ) : ℂ)) := by
    intro n
    refine (hGint.const_mul (μ n * ((χ.1 (pin n) : ℂˣ) : ℂ) * (n : ℂ) ^ (1 - s))).congr ?_
    filter_upwards [ae_ne'] with r hr using (hev n r hr).symm
  have hI : ∀ n : {n : ℕ // 0 < n ∧ n.Coprime N}, ∫ r : ℝ, f (iy r * pin n) / ((|r| : ℝ) : ℂ) =
      (μ n * ((χ.1 (pin n) : ℂˣ) : ℂ) * (n : ℂ) ^ (1 - s)) * It D χ φ s t := by
    intro n
    have e : It D χ φ s t = ∫ r, G r := by rw [hGd]; rfl
    rw [e, ← integral_const_mul]
    refine integral_congr_ae ?_
    filter_upwards [ae_ne'] with r hr using hev n r hr
  have hbd : ∀ n : {n : ℕ // 0 < n ∧ n.Coprime N}, ∀ r : ℝ, r ≠ 0 → ‖f (iy r * pin n) / ((|r| : ℝ) : ℂ)‖ ≤
      ((((n : ℕ) : ℝ)⁻¹) ^ (s.re - 1)) * (|B0| * (1 + r ^ 2)⁻¹) := by
    intro n r hr
    have hn0 : (0 : ℝ) < (n : ℕ) := by exact_mod_cast n.2.1
    have hn1 : 0 < ((n : ℕ) : ℝ)⁻¹ := inv_pos.2 hn0
    have hab : ab (iy r * pin n) = |r| * ((n : ℕ) : ℝ)⁻¹ := by
      rw [ab_mul', hab1 r hr, hab2 n n.2.1]
    have h1 := core hs (W := Wo D φ (em E (aE (iy r * pin n) * rot t))) (c := ((χ.1 (iy r * pin n) : ℂˣ) : ℂ)) hr hn1 (nχ _)
      (by simpa only [hab4 r n hr n.2.1] using hb (iy r * pin n))
    simp only [hf]
    rw [hab]
    exact h1
  have hSum : Summable (fun n : {n : ℕ // 0 < n ∧ n.Coprime N} => ∫ r : ℝ, ‖f (iy r * pin n) / ((|r| : ℝ) : ℂ)‖) := by
    have hbi : Integrable fun r : ℝ => |B0| * (1 + r ^ 2)⁻¹ := integrable_inv_one_add_sq.const_mul |B0|
    have hs1 : Summable fun n : ℕ => ((n : ℝ)⁻¹ ^ (s.re - 1)) * ∫ r : ℝ, |B0| * (1 + r ^ 2)⁻¹ := by
      refine Summable.mul_right _ ?_
      have h2 : Summable fun n : ℕ => (n : ℝ) ^ (-(s.re - 1)) := Real.summable_nat_rpow.2 (by linarith)
      refine h2.congr fun n => ?_
      rw [Real.inv_rpow (Nat.cast_nonneg n), Real.rpow_neg (Nat.cast_nonneg n)]
    have hs2 := hs1.subtype {n : ℕ | 0 < n ∧ n.Coprime N}
    refine Summable.of_nonneg_of_le (fun n => integral_nonneg fun r => norm_nonneg _) (fun n => ?_) hs2
    show _ ≤ ((((n : ℕ) : ℝ)⁻¹) ^ (s.re - 1)) * ∫ r : ℝ, |B0| * (1 + r ^ 2)⁻¹
    rw [← integral_const_mul]
    refine integral_mono_ae (hFint n).norm (hbi.const_mul _) ?_
    filter_upwards [ae_ne'] with r hr using hbd n r hr
  have key := UpperTheory.hasSum_coprime_integral_eq_idele_integral L N hLpos f hinv hsupp hFint hSum
  have eY : Yt D χ φ s (rot t) = ∫ y, f y ∂(ideleMeasure ℚ) := by rw [hf]; rfl
  rw [eY]
  have e5 : (fun n : {n : ℕ // 0 < n ∧ n.Coprime N} => (cT L : ℂ) * (μ n * ((χ.1 (pin n) : ℂˣ) : ℂ) * (n : ℂ) ^ (1 - s)) * It D χ φ s t) =
      fun n : {n : ℕ // 0 < n ∧ n.Coprime N} => (cT L : ℂ) * ∫ r : ℝ, f (iy r * pin n) / ((|r| : ℝ) : ℂ) := by
    funext n
    rw [hI n, mul_assoc]
  rw [e5]
  exact key
