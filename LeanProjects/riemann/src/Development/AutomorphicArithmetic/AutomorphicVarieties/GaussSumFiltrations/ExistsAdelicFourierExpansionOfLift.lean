import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.EvenPos
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.ConstEqZero
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.MaximalCompactGL2FiniteAdeleCharacterization
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.CountSpanInt
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.HasQExpansionAffineTranslateCoeff
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.ScalarStabilizers.FinSupp
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd GlobalTheory.HilbertThetaSeries
open scoped Matrix

noncomputable section

namespace GlobalTheory.HilbertThetaSeries.LiftExp

variable {F : Type} [Field F] [NumberField F]

theorem genD_eq {y : Af F} {𝔪 𝔫 : Ideal (𝓞 F)} (h : GenD y 𝔪) (h' : GenD y 𝔫) : 𝔪 = 𝔫 := by
  have hc : ∀ w : HeightOneSpectrum (𝓞 F), ordI w 𝔪 = ordI w 𝔫 := fun w => by
    have := (h.2 w).symm.trans (h'.2 w)
    rw [WithZero.exp_inj] at this
    omega
  rw [← Ideal.finprod_heightOneSpectrum_factorization h.1, ← Ideal.finprod_heightOneSpectrum_factorization h'.1]
  refine finprod_congr fun w => ?_
  exact congrArg (fun n => w.asIdeal ^ n) (hc w)

theorem coefAt_of_genD {y : Af F} {𝔪 : Ideal (𝓞 F)} (h : GenD y 𝔪) (a : Ideal (𝓞 F) → ℂ) : coefAt a y = a 𝔪 := by
  have h' : ∃ 𝔪, GenD y 𝔪 := ⟨𝔪, h⟩
  rw [coefAt, dif_pos h', genD_eq h'.choose_spec h]

theorem ordI_eventually {I : Ideal (𝓞 F)} (hI : I ≠ ⊥) :
    ∀ᶠ w : HeightOneSpectrum (𝓞 F) in Filter.cofinite, ordI w I = 0 := by
  have := Associates.finite_factors (R := 𝓞 F) hI
  filter_upwards [this] with w hw
  exact_mod_cast hw

theorem exists_unit_genD {𝔪 : Ideal (𝓞 F)} (h : 𝔪 ≠ ⊥) : ∃ y : (Af F)ˣ, GenD (y : Af F) 𝔪 := by
  choose t ht using fun w : HeightOneSpectrum (𝓞 F) => w.valuedAdicCompletion_surjective F
    (WithZero.exp ((ordI w (differentIdeal ℤ (𝓞 F)) : ℤ) - (ordI w 𝔪 : ℤ)))
  have hf : ∀ᶠ w in Filter.cofinite, Valued.v (t w) = 1 := by
    filter_upwards [ordI_eventually h, ordI_eventually (I := differentIdeal ℤ (𝓞 F)) differentIdeal_ne_bot] with w h1 h2
    rw [ht, h1, h2]; simp
  let a : FiniteAdeleRing (𝓞 F) F := ⟨t, by
    filter_upwards [hf] with w hw
    exact (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).2 hw.le⟩
  have hu : IsUnit a := FiniteAdeleRing.isUnit_iff.2 ⟨fun w hw => by
    have := ht w
    rw [show t w = 0 from hw, map_zero] at this
    exact WithZero.exp_ne_zero this.symm, hf⟩
  exact ⟨hu.unit, h, fun w => ht w⟩

theorem aff_mul {R : Type} [CommRing R] (y z : Rˣ) (x : R) : aff (y * z) x = aff y 0 * aff z (((y⁻¹ : Rˣ) : R) * x) := by
  apply Units.ext; ext i j; fin_cases i <;> fin_cases j <;> simp [aff, Matrix.mul_apply, Fin.sum_univ_succ]

theorem toFin_aff (ε : Fˣ) (b : F) :
    toFin (aff ε b) = aff (Units.map (algebraMap F (Af F)).toMonoidHom ε) (algebraMap F (Af F) b) := by
  apply Units.ext; ext i j; fin_cases i <;> fin_cases j <;> simp [toFin, aff, Matrix.GeneralLinearGroup.map]

end GlobalTheory.HilbertThetaSeries.LiftExp

set_option linter.unusedSectionVars false

namespace GlobalTheory.HilbertThetaSeries.LiftExp

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F]

theorem rhom_apply (x : F) (v : InfinitePlace F) : rhom x v = reAt v x := by
  have hv := IsTotallyReal.isReal v
  rw [reAt, ← InfinitePlace.embedding_of_isReal_apply hv, Complex.ofReal_re]; rfl

theorem det_toInf (γ : GL (Fin 2) F) (v : InfinitePlace F) :
    ((toInf γ : GL (Fin 2) (InfinitePlace F → ℝ)) : Matrix (Fin 2) (Fin 2) (InfinitePlace F → ℝ)).det v = reAt v γ.val.det := by
  have : ((toInf γ : GL (Fin 2) (InfinitePlace F → ℝ)) : Matrix (Fin 2) (Fin 2) (InfinitePlace F → ℝ)) = (γ : Matrix (Fin 2) (Fin 2) F).map rhom := rfl
  rw [this]; change ((rhom (F := F)).mapMatrix (γ : Matrix (Fin 2) (Fin 2) F)).det v = _
  rw [← RingHom.map_det, rhom_apply]

theorem det_aff {R : Type} [CommRing R] (y : Rˣ) (x : R) : (aff y x).val.det = y := by
  simp [aff, Matrix.det_fin_two]

theorem slash_weight_smul (k : ℕ) (h : GL (Fin 2) (InfinitePlace F → ℝ)) (c : ℂ) (f : Hn F → ℂ) : sl0 k h (c • f) = c • sl0 k h f := by
  funext z; simp only [sl0, Pi.smul_apply, smul_eq_mul]; ring

theorem tp_one : TP (1 : F) := fun v => by simp [reAt]

theorem et_zero : et (0 : F) = 1 := by simp [et]

theorem trace_int_of_et {x : F} (h : et x = 1) : ∃ n : ℤ, Algebra.trace ℚ F x = n := by
  obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.1 h
  refine ⟨n, ?_⟩
  have h2 : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by simp [Real.pi_ne_zero]
  have h3 : (((Algebra.trace ℚ F x : ℚ) : ℂ)) = ((n : ℚ) : ℂ) := by
    have := hn
    rw [mul_comm (2 * (Real.pi : ℂ) * Complex.I)] at this
    push_cast
    exact mul_right_cancel₀ h2 this
  exact_mod_cast h3

variable {k : ℕ} {Ψ : GL (Fin 2) (Af F) → Hn F → ℂ} {a : (Af F)ˣ → F → ℂ}

theorem coef_unit (hΨ : Sys k Ψ) (ha : ∀ y, HasQ ((((absF y ^ ((k : ℝ) / 2) : ℝ) : ℂ))⁻¹ • Ψ (aff y 0)) (a y))
    (y u : (Af F)ˣ) (hu : ∀ w, Valued.v (pLoc F w (u : Af F)) = 1) : a (y * u) = a y := by
  obtain ⟨-, hmul, hone, -⟩ := Hm.absf F
  have hK : aff u 0 ∈ KLev F 2 1 := ((GlobalTheory.HilbertThetaSeries.kMem F).2.1 u 0 hu (fun w => by simp)).1
  have e : Ψ (aff (y * u) 0) = Ψ (aff y 0) := by
    rw [aff_mul, mul_zero]; exact hΨ.right _ _ hK
  have h1 := ha (y * u)
  rw [e, hmul, hone u hu, mul_one] at h1
  exact hasQ_unique F _ _ _ h1 (ha y)

end GlobalTheory.HilbertThetaSeries.LiftExp

namespace GlobalTheory.HilbertThetaSeries.LiftExp

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F]

theorem sl_toInf (k : ℕ) (γ : GL (Fin 2) F) (f : Hn F → ℂ) :
    sl k (toInf γ) f = ((((∏ v, |reAt v γ.val.det|) ^ ((k : ℝ) / 2) : ℝ) : ℂ)) • sl0 k (toInf γ) f := by
  funext z
  simp only [sl, det_toInf, Pi.smul_apply, smul_eq_mul]

variable {k : ℕ} {Ψ : GL (Fin 2) (Af F) → Hn F → ℂ} {a : (Af F)ˣ → F → ℂ}

theorem coef_rat (hΨ : Sys k Ψ) (ha : ∀ y, HasQ ((((absF y ^ ((k : ℝ) / 2) : ℝ) : ℂ))⁻¹ • Ψ (aff y 0)) (a y))
    (y : (Af F)ˣ) (ξ : Fˣ) (hξ : TP (ξ : F)) : a (Units.map (algebraMap F (Af F)).toMonoidHom ξ * y) 1 = a y ξ := by
  obtain ⟨-, hmul, -, hprod⟩ := Hm.absf F
  obtain ⟨hpos, -⟩ := Hm.absf F
  set ξ' := Units.map (algebraMap F (Af F)).toMonoidHom ξ with hξ'
  have e : toFin (aff ξ 0) * aff y 0 = aff (ξ' * y) 0 := by
    rw [toFin_aff, map_zero, aff_mul, mul_zero]
  have hl := hΨ.left (aff ξ 0) (by rw [det_aff]; exact hξ) (aff y 0)
  rw [e, sl_toInf, det_aff] at hl
  have hq := GlobalTheory.T.hasQExpansion_affineTranslate_coeff F k _ (a (ξ' * y)) ξ 0 hξ (ha (ξ' * y))
  have hP := hprod ξ
  have key : (((absF (ξ' * y) ^ ((k : ℝ) / 2) : ℝ) : ℂ))⁻¹ =
      (((absF y ^ ((k : ℝ) / 2) : ℝ) : ℂ))⁻¹ * (((∏ v, |reAt v (ξ : F)|) ^ ((k : ℝ) / 2) : ℝ) : ℂ) := by
    rw [hmul, Real.mul_rpow (hpos _).le (hpos _).le]
    have h0 : (0 : ℝ) ≤ ∏ v, |reAt v (ξ : F)| := Finset.prod_nonneg fun v _ => abs_nonneg _
    have h1 : (∏ v, |reAt v (ξ : F)|) ^ ((k : ℝ) / 2) * absF ξ' ^ ((k : ℝ) / 2) = 1 := by
      rw [← Real.mul_rpow h0 (hpos _).le, hP, Real.one_rpow]
    rw [eq_inv_of_mul_eq_one_left h1, Complex.ofReal_mul, mul_inv, Complex.ofReal_inv, mul_comm]
  have hf : sl0 k (toInf (aff ξ 0)) ((((absF (ξ' * y) ^ ((k : ℝ) / 2) : ℝ) : ℂ))⁻¹ • Ψ (aff (ξ' * y) 0)) =
      (((absF y ^ ((k : ℝ) / 2) : ℝ) : ℂ))⁻¹ • Ψ (aff y 0) := by
    rw [slash_weight_smul, ← hl, smul_smul, key]
  rw [hf] at hq
  have := congrFun (hasQ_unique F _ _ _ hq (ha y)) (ξ : F)
  rw [div_self ξ.ne_zero, mul_zero, et_zero, mul_one] at this
  exact this

theorem coef_dual (hΨ : Sys k Ψ) (ha : ∀ y, HasQ ((((absF y ^ ((k : ℝ) / 2) : ℝ) : ℂ))⁻¹ • Ψ (aff y 0)) (a y))
    (y : (Af F)ˣ) (ξ : F) (hξ : ξ ≠ 0) (hne : a y ξ ≠ 0) : ∃ 𝔪, GenD (algebraMap F (Af F) ξ * (y : Af F)) 𝔪 := by
  obtain ⟨-, hK, -, hval, -⟩ := GlobalTheory.HilbertThetaSeries.kMem F
  refine GlobalTheory.HilbertThetaSeries.DualIdele.genD_of_trace F y ξ hξ fun b hb => ?_
  have hx : ∀ w, Valued.v (pLoc F w (((y⁻¹ : (Af F)ˣ) : Af F) * algebraMap F (Af F) b)) ≤ 1 := fun w => by
    rw [map_mul, map_mul, hval]
    have h1 : Valued.v (pLoc F w ((y⁻¹ : (Af F)ˣ) : Af F)) * Valued.v (pLoc F w (y : Af F)) = 1 := by
      rw [← map_mul, ← map_mul, Units.inv_mul, map_one, map_one]
    calc _ ≤ Valued.v (pLoc F w ((y⁻¹ : (Af F)ˣ) : Af F)) * Valued.v (pLoc F w (y : Af F)) := mul_le_mul_right (hb w) _
      _ = 1 := h1
  have hu := (hK 1 _ (fun w => by simp) hx).1
  have e : toFin (aff 1 b) * aff y 0 = aff y 0 * aff 1 (((y⁻¹ : (Af F)ˣ) : Af F) * algebraMap F (Af F) b) := by
    rw [toFin_aff, map_one, ← aff_mul, mul_one]
    apply Units.ext; ext i j; fin_cases i <;> fin_cases j <;> simp [aff, Matrix.mul_apply, Fin.sum_univ_succ]
  have hl := hΨ.left (aff 1 b) (by rw [det_aff]; exact tp_one) (aff y 0)
  rw [e, hΨ.right _ _ hu, sl_toInf, det_aff] at hl
  simp only [Units.val_one, reAt, map_one, Complex.one_re, abs_one, Finset.prod_const_one, Real.one_rpow,
    Complex.ofReal_one, one_smul] at hl
  have hq := GlobalTheory.T.hasQExpansion_affineTranslate_coeff F k _ (a y) 1 b tp_one (ha y)
  rw [slash_weight_smul, hl] at hq
  have := congrFun (hasQ_unique F _ _ _ hq (ha y)) ξ
  simp only [Units.val_one, div_one] at this
  have h2 : et (ξ * b) = 1 := by
    have := mul_left_cancel₀ hne (this.trans (mul_one _).symm)
    exact this
  exact trace_int_of_et h2

end GlobalTheory.HilbertThetaSeries.LiftExp

namespace GlobalTheory.HilbertThetaSeries.LiftExp

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F]

def pt (x : InfinitePlace F → ℝ) (y : (InfinitePlace F → ℝ)ˣ) (hy : ∀ v, 0 < y.val v) : Hn F :=
  fun v => UpperHalfPlane.mk ((x v : ℂ) + Complex.I * (y.val v : ℂ)) (by simpa using hy v)

theorem sl_aff_I (k : ℕ) (x : InfinitePlace F → ℝ) (y : (InfinitePlace F → ℝ)ˣ) (hy : ∀ v, 0 < y.val v) (f : Hn F → ℂ) :
    sl k (aff y x) f (fun _ => UpperHalfPlane.I) = (((∏ v, y.val v) ^ ((k : ℝ) / 2) : ℝ) : ℂ) * f (pt x y hy) := by
  have hd : ∀ v (z : ℂ), UpperHalfPlane.denom (cmp v (aff y x)) z = 1 := fun v z => by
    simp [UpperHalfPlane.denom, cmp, aff]
  have hn : ∀ v (z : ℂ), UpperHalfPlane.num (cmp v (aff y x)) z = (y.val v : ℂ) * z + x v := fun v z => by
    simp [UpperHalfPlane.num, cmp, aff]
  have ha : act (aff y x) (fun _ => UpperHalfPlane.I) = pt x y hy := by
    funext v
    apply UpperHalfPlane.ext
    rw [act, UpperHalfPlane.coe_smul_of_det_pos (by simpa [cmp, aff, Matrix.det_fin_two] using hy v), hd, hn]
    simp [pt]; ring
  have hp : ∏ v, |(aff y x).val.det v| = ∏ v, y.val v :=
    Finset.prod_congr rfl fun v _ => by rw [det_aff, abs_of_pos (hy v)]
  simp only [sl, sl0, hd, ha, hp, Finset.prod_const_one, inv_one, one_pow, one_mul]

variable {k : ℕ} {Ψ : GL (Fin 2) (Af F) → Hn F → ℂ} {a : (Af F)ˣ → F → ℂ}

theorem ne_zero_of_tp {ξ : F} (h : TP ξ) : ξ ≠ 0 := by
  rintro rfl
  obtain ⟨v⟩ : Nonempty (InfinitePlace F) := inferInstance
  simpa [reAt] using h v

theorem coefAt_eq_coef (hΨ : Sys k Ψ) (ha : ∀ y, HasQ ((((absF y ^ ((k : ℝ) / 2) : ℝ) : ℂ))⁻¹ • Ψ (aff y 0)) (a y))
    (c : Ideal (𝓞 F) → ℂ) (hc : ∀ 𝔪, 𝔪 ≠ ⊥ → ∃ Y : (Af F)ˣ, GenD (Y : Af F) 𝔪 ∧ c 𝔪 = a Y 1)
    (y : (Af F)ˣ) (ξ : F) (hξ : TP ξ) : coefAt c (algebraMap F (Af F) ξ * (y : Af F)) = a y ξ := by
  have h0 := ne_zero_of_tp hξ
  by_cases h : ∃ 𝔪, GenD (algebraMap F (Af F) ξ * (y : Af F)) 𝔪
  · obtain ⟨𝔪, hm⟩ := h
    obtain ⟨Y, hY, hcY⟩ := hc 𝔪 hm.1
    have hr := coef_rat hΨ ha y (Units.mk0 ξ h0) hξ
    set y' := Units.map (algebraMap F (Af F)).toMonoidHom (Units.mk0 ξ h0) * y with hy'
    have hv : (y' : Af F) = algebraMap F (Af F) ξ * (y : Af F) := rfl
    have hu := coef_unit hΨ ha Y (Y⁻¹ * y') fun w => by
      rw [Units.val_mul, map_mul, map_mul, hv, hm.2 w, ← hY.2 w, ← map_mul, ← map_mul, Units.inv_mul, map_one, map_one]
    rw [mul_inv_cancel_left] at hu
    rw [coefAt_of_genD hm, hcY, ← hu, hr, Units.val_mk0]
  · rw [coefAt, dif_neg h]
    by_contra hne
    exact h (coef_dual hΨ ha y ξ h0 (Ne.symm hne))

end GlobalTheory.HilbertThetaSeries.LiftExp

open GlobalTheory.HilbertThetaSeries.LiftExp in

theorem GlobalTheory.HilbertThetaSeries.lift_hasExp : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (k : ℕ) (Ψ : GL (Fin 2) (Af F) → Hn F → ℂ) (φ : GA F 2 → ℂ) (a : (Af F)ˣ → F → ℂ), Sys k Ψ → IsLift k Ψ φ → (∀ y, HasQ ((((absF y ^ ((k : ℝ) / 2) : ℝ) : ℂ))⁻¹ • Ψ (aff y 0)) (a y)) → ∃ c : Ideal (𝓞 F) → ℂ, HasExp φ k (fun y => a y 0) c ∧ ∀ 𝔪, 𝔪 ≠ ⊥ → ∃ y, c 𝔪 = a y 1 := by
  classical
  intro F _ _ _ k Ψ φ a hΨ hφ ha
  let c : Ideal (𝓞 F) → ℂ := fun 𝔪 => if h : 𝔪 ≠ ⊥ then a (exists_unit_genD h).choose 1 else 0
  have hc : ∀ 𝔪, 𝔪 ≠ ⊥ → ∃ Y : (Af F)ˣ, GenD (Y : Af F) 𝔪 ∧ c 𝔪 = a Y 1 := fun 𝔪 h =>
    ⟨_, (exists_unit_genD h).choose_spec, dif_pos h⟩
  refine ⟨c, fun x y hy yf => ?_, fun 𝔪 h => (hc 𝔪 h).imp fun _ h => h.2⟩
  have hP : 0 < ∏ v, y.val v := Finset.prod_pos fun v _ => hy v
  have hP' : (((∏ v, y.val v) ^ ((k : ℝ) / 2) : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (Real.rpow_pos_of_pos hP _).ne'
  rw [hφ.2 (aff y x) (fun v => by rw [det_aff]; exact hy v), sl_aff_I k x y hy,
    Real.mul_rpow hP.le ((Hm.absf F).1 yf).le, Complex.ofReal_mul, mul_div_mul_left _ _ hP']
  obtain ⟨⟨D, -, hD⟩, hs⟩ := ha yf
  have h1 := (hs (pt x y hy)).update 0 0
  have h2 := (hasSum_subtype_iff_of_support_subset (s := {ξ : F | ∀ v, 0 < reAt v ξ}) (fun ξ hξ => by
    have hξ0 : ξ ≠ 0 := by rintro rfl; simp at hξ
    rw [Function.mem_support, Function.update_of_ne hξ0] at hξ
    exact (hD ξ (left_ne_zero_of_mul hξ)).1.resolve_left hξ0)).2 h1
  have e0 : ez (0 : F) (pt x y hy) = 1 := by simp [ez, reAt]
  rw [e0, mul_one, zero_sub, Pi.smul_apply, smul_eq_mul, neg_add_eq_sub, mul_comm, ← div_eq_mul_inv] at h2
  refine QUniq.hasSum_congr' h2 fun ξ => ?_
  rw [Function.comp_apply, Function.update_of_ne (ne_zero_of_tp ξ.2), coefAt_eq_coef hΨ ha c hc yf ξ.1 ξ.2]
  rfl

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd GlobalTheory.HilbertThetaSeries
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_adelic_fourier_expansion_of_lift : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (k : ℕ) (Ψ : GL (Fin 2) (Af F) → Hn F → ℂ) (φ : GA F 2 → ℂ) (a : (Af F)ˣ → F → ℂ), Sys k Ψ → IsLift k Ψ φ → (∀ y, HasQ ((((absF y ^ ((k : ℝ) / 2) : ℝ) : ℂ))⁻¹ • Ψ (aff y 0)) (a y)) → ∃ c : Ideal (𝓞 F) → ℂ, HasExp φ k (fun y => a y 0) c ∧ ∀ 𝔪, 𝔪 ≠ ⊥ → ∃ y, c 𝔪 = a y 1 := by
  first | exact @GlobalTheory.HilbertThetaSeries.lift_hasExp | exact GlobalTheory.HilbertThetaSeries.lift_hasExp | (intros; apply GlobalTheory.HilbertThetaSeries.lift_hasExp <;> assumption)
