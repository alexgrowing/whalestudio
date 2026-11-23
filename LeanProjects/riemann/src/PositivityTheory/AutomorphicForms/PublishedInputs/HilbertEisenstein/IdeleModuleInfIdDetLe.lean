import PositivityTheory.AutomorphicForms.PublishedInputs.HilbertEisenstein.SSmooth
import GroundTheory.GlobalFields.TateThesis.TateThetaDecay
import GroundTheory.GlobalFields.TateThesis.AdelePoissonUniform
import GroundTheory.IdeleRoots.ClassicalIdeles.FinOrdValGenProof
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsOpenIdeleSubgroupContainsCongruenceUnits

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V.Af UpperTheory.V.Base
open scoped Matrix
open MeasureTheory GroundTheory.Global GroundTheory.Global.IdeleGroup UpperTheory.V.Sd UpperTheory.V.Published

namespace UpperTheory.HilbertEisensteinWeightOne.eisensteinGrowth

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F]

def boxP (e : HeightOneSpectrum (𝓞 F) → ℤ) (v : Fin 2 → Ad F) : Prop :=
  ∀ w, ∀ i, Valued.v (pLoc F w (pFin F (v i))) ≤ WithZero.exp (e w)

theorem norm_omega_eq_one {ω : HChar F} (h : IsOfFinOrder ω) (x : Ideles F) :
    ‖((ω.1 x : ℂˣ) : ℂ)‖ = 1 := by
  obtain ⟨n, hn, hpow⟩ := h.exists_pow_eq_one
  have h1 : (ω.1 x) ^ n = 1 := by
    have := congrArg (fun χ : HChar F => (χ.1 x)) hpow
    simpa using this
  have h2 : ((ω.1 x : ℂˣ) : ℂ) ^ n = 1 := by
    rw [← Units.val_pow_eq_pow_val, h1, Units.val_one]
  have h3 : ‖((ω.1 x : ℂˣ) : ℂ)‖ ^ n = 1 := by rw [← norm_pow, h2, norm_one]
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hn.ne').1 h3

theorem absD_scalar_mul (t : {r : ℝ // 0 < r}) (u : normOneSubgroup F) (h : GA F 2) :
    absD (Matrix.GeneralLinearGroup.scalar (Fin 2) (moduleSection (w0 F) t * (u : Ideles F)) * h) =
      (t : ℝ) ^ 2 * absD h := by
  set z : Ideles F := moduleSection (w0 F) t * (u : Ideles F)
  have hdet : Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.scalar (Fin 2) z) = z ^ 2 := by
    ext
    simp [Matrix.GeneralLinearGroup.scalar, Matrix.det_diagonal, Fin.prod_univ_two, sq]
  have hu : IdeleGroup.ideleModule F (u : Ideles F) = 1 := u.2
  have hz : IdeleGroup.ideleModule F z = t := by
    simp only [z, map_mul, ideleModule_moduleSection, hu, mul_one]
  unfold absD
  rw [map_mul, hdet, map_mul, map_pow, hz]
  rfl

omit [IsTotallyReal F] in
theorem absD_pos (h : GA F 2) : 0 < absD h := (IdeleGroup.ideleModule F _).2

theorem norm_infEq_apply (d : UpperTheory.V.TR.Rinf F) (w : InfinitePlace F) :
    ‖(UpperTheory.V.TR.infEq F d) w‖ = |d w| := by
  have hv := IsTotallyReal.isReal w
  set x := (UpperTheory.V.TR.infEq F d) w
  have h1 : (NumberField.InfinitePlace.Completion.isometryEquivRealOfIsReal hv) x = d w := by
    show NumberField.InfinitePlace.Completion.ringEquivRealOfIsReal hv
      ((NumberField.InfinitePlace.Completion.ringEquivRealOfIsReal (IsTotallyReal.isReal w)).symm (d w)) = d w
    exact RingEquiv.apply_symm_apply _ _
  have h0 : (NumberField.InfinitePlace.Completion.isometryEquivRealOfIsReal hv) 0 = 0 :=
    map_zero (NumberField.InfinitePlace.Completion.ringEquivRealOfIsReal hv)
  have := (NumberField.InfinitePlace.Completion.isometryEquivRealOfIsReal hv).dist_eq x 0
  rw [h0, h1, Real.dist_0_eq_abs] at this
  rw [← dist_zero_right, ← this]

theorem infId_fst (d : (UpperTheory.V.TR.Rinf F)ˣ) :
    ((UpperTheory.V.TR.infId F d : Ideles F) : Ad F).1 = UpperTheory.V.TR.infEq F d.val := by
  change (1 : InfiniteAdeleRing F) - UpperTheory.V.TR.infEq F 1 + UpperTheory.V.TR.infEq F d.val = _
  rw [map_one, sub_self, zero_add]

theorem infId_snd (d : (UpperTheory.V.TR.Rinf F)ˣ) :
    ((UpperTheory.V.TR.infId F d : Ideles F) : Ad F).2 = 1 := by
  change (1 : Af F) - 0 + 0 = 1
  rw [sub_zero, add_zero]

theorem ideleModule_infId (d : (UpperTheory.V.TR.Rinf F)ˣ) :
    (IdeleGroup.ideleModule F (UpperTheory.V.TR.infId F d) : ℝ) = ∏ w, |d.val w| := by
  rw [ideleModule_eq]
  have hfin : ∏ᶠ v : HeightOneSpectrum (𝓞 F), ‖((UpperTheory.V.TR.infId F d : Ideles F) : Ad F).2 v‖ = 1 := by
    rw [infId_snd]
    simp
  rw [hfin, mul_one]
  refine Finset.prod_congr rfl fun w _ => ?_
  have hm : w.mult = 1 := by
    unfold InfinitePlace.mult
    rw [if_pos (IsTotallyReal.isReal w)]
  have e : ((UpperTheory.V.TR.infId F d : Ideles F) : Ad F).1 w = (UpperTheory.V.TR.infEq F d.val) w := by
    rw [infId_fst]
  rw [hm, pow_one, e, norm_infEq_apply]

theorem abs_apply_le_height (y : GL (Fin 2) (UpperTheory.V.TR.Rinf F)) (i j : Fin 2) (w : InfinitePlace F) :
    |(y : Matrix (Fin 2) (Fin 2) (UpperTheory.V.TR.Rinf F)) i j w| ≤ UpperTheory.V.TR.height y := by
  have h1 : |(y : Matrix (Fin 2) (Fin 2) (UpperTheory.V.TR.Rinf F)) i j w| ≤
      ‖UpperTheory.V.TR.toL (y : Matrix (Fin 2) (Fin 2) (UpperTheory.V.TR.Rinf F))‖ := by
    rw [← Real.norm_eq_abs]
    exact (norm_le_pi_norm _ w).trans ((norm_le_pi_norm _ j).trans (norm_le_pi_norm _ i))
  have h2 := norm_nonneg (UpperTheory.V.TR.toL ((y⁻¹ : GL (Fin 2) (UpperTheory.V.TR.Rinf F)) : Matrix (Fin 2) (Fin 2) (UpperTheory.V.TR.Rinf F)))
  unfold UpperTheory.V.TR.height
  linarith

theorem one_le_height (y : GL (Fin 2) (UpperTheory.V.TR.Rinf F)) : 1 ≤ UpperTheory.V.TR.height y := by
  unfold UpperTheory.V.TR.height
  have := norm_nonneg (UpperTheory.V.TR.toL (y : Matrix (Fin 2) (Fin 2) (UpperTheory.V.TR.Rinf F)))
  have := norm_nonneg (UpperTheory.V.TR.toL ((y⁻¹ : GL (Fin 2) (UpperTheory.V.TR.Rinf F)) : Matrix (Fin 2) (Fin 2) (UpperTheory.V.TR.Rinf F)))
  linarith

theorem abs_det_apply_le (y : GL (Fin 2) (UpperTheory.V.TR.Rinf F)) (w : InfinitePlace F) :
    |((Matrix.GeneralLinearGroup.det y : (UpperTheory.V.TR.Rinf F)ˣ) : UpperTheory.V.TR.Rinf F) w| ≤
      2 * UpperTheory.V.TR.height y ^ 2 := by
  rw [Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_fin_two]
  simp only [Pi.sub_apply, Pi.mul_apply]
  have h00 := abs_apply_le_height y 0 0 w
  have h01 := abs_apply_le_height y 0 1 w
  have h10 := abs_apply_le_height y 1 0 w
  have h11 := abs_apply_le_height y 1 1 w
  calc _ ≤ |(y : Matrix (Fin 2) (Fin 2) (UpperTheory.V.TR.Rinf F)) 0 0 w * (y : Matrix (Fin 2) (Fin 2) (UpperTheory.V.TR.Rinf F)) 1 1 w| +
        |(y : Matrix (Fin 2) (Fin 2) (UpperTheory.V.TR.Rinf F)) 0 1 w * (y : Matrix (Fin 2) (Fin 2) (UpperTheory.V.TR.Rinf F)) 1 0 w| := abs_sub _ _
    _ ≤ UpperTheory.V.TR.height y * UpperTheory.V.TR.height y + UpperTheory.V.TR.height y * UpperTheory.V.TR.height y := by
        rw [abs_mul, abs_mul]
        gcongr <;> first | exact abs_nonneg _ | assumption | linarith [one_le_height y]
    _ = 2 * UpperTheory.V.TR.height y ^ 2 := by ring

theorem ideleModule_infId_det_le (y : GL (Fin 2) (UpperTheory.V.TR.Rinf F)) :
    (IdeleGroup.ideleModule F (UpperTheory.V.TR.infId F (Matrix.GeneralLinearGroup.det y)) : ℝ) ≤
      2 ^ Fintype.card (InfinitePlace F) * UpperTheory.V.TR.height y ^ (2 * Fintype.card (InfinitePlace F)) := by
  rw [ideleModule_infId]
  calc ∏ w, |((Matrix.GeneralLinearGroup.det y : (UpperTheory.V.TR.Rinf F)ˣ) : UpperTheory.V.TR.Rinf F) w|
      ≤ ∏ _w : InfinitePlace F, 2 * UpperTheory.V.TR.height y ^ 2 :=
        Finset.prod_le_prod (fun _ _ => abs_nonneg _) fun w _ => abs_det_apply_le y w
    _ = _ := by rw [Finset.prod_const, Finset.card_univ, mul_pow, ← pow_mul, mul_comm 2 (Fintype.card _)]

theorem absD_mul_infGL_le (g : GA F 2) : ∃ (C : ℝ) (N : ℕ), ∀ y : GL (Fin 2) (UpperTheory.V.TR.Rinf F),
    absD (g * UpperTheory.V.TR.infGL F 2 y) ≤ C * UpperTheory.V.TR.height y ^ N ∧
      (absD (g * UpperTheory.V.TR.infGL F 2 y))⁻¹ ≤ C * UpperTheory.V.TR.height y ^ N := by
  set n := Fintype.card (InfinitePlace F)
  have hsplit : ∀ y : GL (Fin 2) (UpperTheory.V.TR.Rinf F), absD (g * UpperTheory.V.TR.infGL F 2 y) =
      absD g * (IdeleGroup.ideleModule F (UpperTheory.V.TR.infId F (Matrix.GeneralLinearGroup.det y)) : ℝ) := by
    intro y
    unfold absD
    rw [map_mul, UpperTheory.V.TR.det_infGL, map_mul, Positive.val_mul]
  have hinv : ∀ y : GL (Fin 2) (UpperTheory.V.TR.Rinf F),
      (IdeleGroup.ideleModule F (UpperTheory.V.TR.infId F (Matrix.GeneralLinearGroup.det y)) : ℝ)⁻¹ =
      (IdeleGroup.ideleModule F (UpperTheory.V.TR.infId F (Matrix.GeneralLinearGroup.det y⁻¹)) : ℝ) := by
    intro y
    rw [map_inv, map_inv, map_inv, Positive.coe_inv]
  have hh : ∀ y : GL (Fin 2) (UpperTheory.V.TR.Rinf F), UpperTheory.V.TR.height y⁻¹ = UpperTheory.V.TR.height y := by
    intro y
    unfold UpperTheory.V.TR.height
    rw [inv_inv]
    ring
  refine ⟨max (absD g) (absD g)⁻¹ * 2 ^ n, 2 * n, fun y => ⟨?_, ?_⟩⟩
  · rw [hsplit, mul_assoc]
    exact mul_le_mul (le_max_left _ _) (ideleModule_infId_det_le y) (IdeleGroup.ideleModule F _).2.le
      ((absD_pos g).le.trans (le_max_left _ _))
  · rw [hsplit, mul_inv, hinv, mul_assoc]
    have := ideleModule_infId_det_le y⁻¹
    rw [hh] at this
    exact mul_le_mul (le_max_right _ _) this (IdeleGroup.ideleModule F _).2.le
      ((absD_pos g).le.trans (le_max_left _ _))

theorem exists_D {ω : HChar F} {c : HeightOneSpectrum (𝓞 F) → ℕ} (hyp : Hyp ω c) :
    ∃ D : 𝓞 F, D ≠ 0 ∧ ∀ w : HeightOneSpectrum (𝓞 F), ∀ x : w.adicCompletion F,
      Valued.v x ≤ WithZero.exp ((c w : ℤ) + dd w) →
        Valued.v (algebraMap F (w.adicCompletion F) (D : F) * x) ≤ 1 := by
  classical
  obtain ⟨n, hn, hpow⟩ := hyp.fin.exists_pow_eq_one
  have hpow' : ω.1 ^ n = 1 := by
    have := congrArg Subtype.val hpow
    simpa using this
  have hker : IsOpen (ω.1.ker : Set (Ideles F)) :=
    GroundTheory.BlockD.isOpen_ker_of_pow_eq_one ω.1 ω.2.1 hn hpow'
  obtain ⟨S, M, hS, key⟩ := GlobalTheory.OpenIdeleCongr.localIdele_mem_of_isOpen ω.1.ker hker
  have hc0 : ∀ w ∉ S, c w = 0 := by
    intro w hw
    have hmem : (0 : ℕ) ∈ {n : ℕ | ∀ x : (w.adicCompletion F)ˣ, IsUnitAt w x →
        Valued.v ((x : w.adicCompletion F) - 1) ≤ WithZero.exp (-(n : ℤ)) → ω.loc w x = 1} := by
      intro x hx _
      exact MonoidHom.mem_ker.1 (key w x hx fun h => absurd h hw)
    exact Nat.le_zero.1 ((hyp.cond w).2 hmem)
  set T := hS.toFinset
  set 𝔠 : Ideal (𝓞 F) := ∏ w ∈ T, w.asIdeal ^ c w
  have h𝔠 : 𝔠 ≠ ⊥ := by
    rw [← Ideal.zero_eq_bot]
    exact Finset.prod_ne_zero_iff.2 fun w _ => pow_ne_zero _ (by rw [Ideal.zero_eq_bot]; exact w.ne_bot)
  obtain ⟨b, hb, hb0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h𝔠
  have hdiff : differentIdeal ℤ (𝓞 F) ≠ ⊥ := differentIdeal_ne_bot
  obtain ⟨a, ha, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hdiff
  refine ⟨a * b, mul_ne_zero ha0 hb0, fun w x hx => ?_⟩
  have hva : w.intValuation a ≤ WithZero.exp (-(dd w)) := by
    have := GroundTheory.Global.intValuation_le_of_mem_ideal w hdiff ha
    rwa [FractionalIdeal.count_coe F w hdiff] at this
  have hvb : w.intValuation b ≤ WithZero.exp (-(c w : ℤ)) := by
    by_cases hw : w ∈ S
    · have hle : 𝔠 ≤ w.asIdeal ^ c w := by
        rw [show 𝔠 = _ from (Finset.mul_prod_erase T (fun w => w.asIdeal ^ c w) (hS.mem_toFinset.2 hw)).symm]
        exact Ideal.mul_le_left (I := w.asIdeal ^ c w) (J := ∏ x ∈ T.erase w, x.asIdeal ^ c x)
      exact (w.intValuation_le_pow_iff_mem b (c w)).2 (hle hb)
    · rw [hc0 w hw, Nat.cast_zero, neg_zero, WithZero.exp_zero]
      exact w.intValuation_le_one b
  have hD : Valued.v (algebraMap F (w.adicCompletion F) ((a * b : 𝓞 F) : F)) ≤
      WithZero.exp (-((c w : ℤ) + dd w)) := by
    have e1 : Valued.v (algebraMap F (w.adicCompletion F) ((a * b : 𝓞 F) : F)) = w.intValuation (a * b) := by
      rw [← HeightOneSpectrum.valuation_of_algebraMap (K := F)]
      exact HeightOneSpectrum.valuedAdicCompletion_eq_valuation' w _
    rw [e1, map_mul, show -((c w : ℤ) + dd w) = -(dd w) + -(c w : ℤ) by ring, WithZero.exp_add]
    exact mul_le_mul' hva hvb
  rw [map_mul]
  calc Valued.v (algebraMap F (w.adicCompletion F) ((a * b : 𝓞 F) : F)) * Valued.v x
      ≤ WithZero.exp (-((c w : ℤ) + dd w)) * WithZero.exp ((c w : ℤ) + dd w) := mul_le_mul' hD hx
    _ = 1 := by rw [← WithZero.exp_add, neg_add_cancel, WithZero.exp_zero]

theorem lintegral_min_lt_top :
    ∫⁻ t, ENNReal.ofReal (min (t : ℝ) (t : ℝ)⁻¹) ∂posRealMeasure < ⊤ := by
  have hmeas : Measurable fun t : {r : ℝ // 0 < r} => ENNReal.ofReal (min (t : ℝ) (t : ℝ)⁻¹) :=
    ENNReal.measurable_ofReal.comp
      ((continuous_subtype_val.min (continuous_subtype_val.inv₀ fun t => t.2.ne')).measurable)
  rw [posRealMeasure_eq_map_expPos, lintegral_map hmeas measurable_expPos]
  have key : ∀ y : ℝ, 0 ≤ y → (Real.exp y)⁻¹ ≤ 2 * (1 + y ^ 2)⁻¹ := fun y hy => by
    have h1 := Real.quadratic_le_exp_of_nonneg hy
    rw [← div_eq_mul_inv, le_div_iff₀ (by positivity), inv_mul_le_iff₀ (Real.exp_pos y)]
    nlinarith
  have hle : ∀ x : ℝ, ENNReal.ofReal (min ((expPos x : {r : ℝ // 0 < r}) : ℝ)
      ((expPos x : {r : ℝ // 0 < r}) : ℝ)⁻¹) ≤ ENNReal.ofReal (2 * (1 + x ^ 2)⁻¹) := by
    intro x
    apply ENNReal.ofReal_le_ofReal
    simp only [coe_expPos]
    rcases le_total 0 x with hx | hx
    · exact (min_le_right _ _).trans (key x hx)
    · refine (min_le_left _ _).trans ?_
      have := key (-x) (by linarith)
      rwa [Real.exp_neg, inv_inv, neg_sq] at this
  calc _ ≤ ∫⁻ x, ENNReal.ofReal (2 * (1 + x ^ 2)⁻¹) := lintegral_mono hle
    _ < ⊤ := (integrable_inv_one_add_sq.const_mul 2).lintegral_lt_top

theorem norm_Eis_le (ω : HChar F) (Ψ : (Fin 2 → Ad F) → ℂ) (h : GA F 2) (K : ℝ) (hK : 0 ≤ K)
    (hb : ∀ t : {r : ℝ // 0 < r}, ∀ u ∈ normOneFundamentalDomain F,
      ‖eisInt ω Ψ h t u‖ ≤ K * min (t : ℝ) (t : ℝ)⁻¹) :
    ‖Eis ω Ψ h‖ ≤ K * ((normOneMeasure F (normOneFundamentalDomain F)).toReal *
      (∫⁻ t, ENNReal.ofReal (min (t : ℝ) (t : ℝ)⁻¹) ∂posRealMeasure).toReal) := by
  set mE := normOneMeasure F (normOneFundamentalDomain F)
  set I := ∫⁻ t, ENNReal.ofReal (min (t : ℝ) (t : ℝ)⁻¹) ∂posRealMeasure
  have hmE : mE ≠ ⊤ := (normOneMeasure_normOneFundamentalDomain_lt_top F).ne
  have hI : I ≠ ⊤ := lintegral_min_lt_top.ne
  have key : ‖Eis ω Ψ h‖ₑ ≤ ENNReal.ofReal K * mE * I := by
    calc ‖Eis ω Ψ h‖ₑ ≤ ∫⁻ t, ‖∫ u in normOneFundamentalDomain F, eisInt ω Ψ h t u ∂normOneMeasure F‖ₑ
          ∂posRealMeasure := enorm_integral_le_lintegral_enorm _
      _ ≤ ∫⁻ t, ∫⁻ u in normOneFundamentalDomain F, ‖eisInt ω Ψ h t u‖ₑ ∂normOneMeasure F
          ∂posRealMeasure := lintegral_mono fun t => enorm_integral_le_lintegral_enorm _
      _ ≤ ∫⁻ t, ENNReal.ofReal K * mE * ENNReal.ofReal (min (t : ℝ) (t : ℝ)⁻¹) ∂posRealMeasure := by
          refine lintegral_mono fun t => ?_
          rw [mul_right_comm, ← ENNReal.ofReal_mul hK, ← setLIntegral_const]
          refine setLIntegral_mono measurable_const fun u hu => ?_
          rw [← ofReal_norm]
          exact ENNReal.ofReal_le_ofReal (hb t u hu)
      _ = ENNReal.ofReal K * mE * I := lintegral_const_mul' _ _ (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hmE)
  have hfin : ENNReal.ofReal K * mE * I ≠ ⊤ := ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hmE) hI
  have h2 := ENNReal.toReal_mono hfin key
  rw [← ofReal_norm, ENNReal.toReal_ofReal (norm_nonneg _), ENNReal.toReal_mul, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal hK] at h2
  linarith [h2]

open Classical in

theorem norm_Phi_le (c : HeightOneSpectrum (𝓞 F) → ℕ) (v : Fin 2 → Ad F) :
    ‖Phi c v‖ ≤ ‖arch (UpperTheory.V.TR.pInf F (v 0)) (UpperTheory.V.TR.pInf F (v 1))‖ *
      (if boxP (fun w => (c w : ℤ) + dd w) v then 1 else 0) := by
  unfold Phi
  rw [norm_mul]
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  split_ifs with h1 h2 h2
  · simp
  · exfalso
    apply h2
    intro w
    dsimp only
    have hd : (0 : ℤ) ≤ dd w := by unfold dd; exact Int.natCast_nonneg _
    refine Fin.forall_fin_two.2 ⟨(h1 w).1.trans (WithZero.exp_le_exp.2 (by omega)), ?_⟩
    have hy := (h1 w).2
    calc Valued.v (pLoc F w (pFin F (v 1))) = Valued.v ((pLoc F w (pFin F (v 1)) - 1) + 1) := by
          rw [sub_add_cancel]
      _ ≤ max (Valued.v (pLoc F w (pFin F (v 1)) - 1)) (Valued.v (1 : w.adicCompletion F)) :=
          Valuation.map_add _ _ _
      _ ≤ WithZero.exp ((c w : ℤ) + dd w) := by
          rw [map_one]
          refine max_le (hy.trans (WithZero.exp_le_exp.2 (by omega))) ?_
          rw [← WithZero.exp_zero]
          exact WithZero.exp_le_exp.2 (by omega)
  · simp
  · simp

open Classical in

theorem norm_PhiH_le (c : HeightOneSpectrum (𝓞 F) → ℕ) (v : Fin 2 → Ad F) :
    ‖PhiH c v‖ ≤ ‖arch (UpperTheory.V.TR.pInf F (v 0)) (UpperTheory.V.TR.pInf F (v 1))‖ *
      (if boxP (fun w => (c w : ℤ) + dd w) v then 1 else 0) := by
  unfold PhiH
  rw [norm_mul]
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  split_ifs with h1 h2 h2
  · exact (Circle.norm_coe _).le
  · exact absurd (fun w => Fin.forall_fin_two.2 ⟨(h1 w).1, (h1 w).2⟩) h2
  · simp
  · simp

end UpperTheory.HilbertEisensteinWeightOne.eisensteinGrowth
