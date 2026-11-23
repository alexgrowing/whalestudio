import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.WeightChange
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.HolLin
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.ScalarStabilizers.Mulsm
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.ScalarStabilizers.Zfinof
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.ScalarStabilizers.Trzero
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.ScalarStabilizers.Mulaut
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.ScalarStabilizers.Fixunit
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.ScalarStabilizers.FinSupp
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.ScalarStabilizers.Boxfin

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Base

namespace UpperTheory.V.Sd

private theorem conv {G : Type} [AddCommGroup G] {f g : G → ℂ} {S T : ℂ} (hf : HasSum f S) (hg : HasSum g T) :
    HasSum (fun ξ => ∑' η, f η * g (ξ - η)) (S * T) := by
  have h1 := hf.mul hg (summable_mul_of_summable_norm hf.summable.norm hg.summable.norm)
  let e : G × G ≃ G × G :=
    ⟨fun p => (p.2, p.1 - p.2), fun p => (p.1 + p.2, p.1), fun p => by simp, fun p => by simp⟩
  have h2 := e.hasSum_iff.2 h1
  exact h2.prod_fiberwise fun ξ => (h2.summable.prod_factor ξ).hasSum

variable {F : Type} [Field F] [NumberField F]

private theorem genD_unique {y : Af F} {𝔪 𝔫 : Ideal (𝓞 F)} (h : GenD y 𝔪) (h' : GenD y 𝔫) : 𝔪 = 𝔫 := by
  have hc : ∀ w : HeightOneSpectrum (𝓞 F), ordI w 𝔪 = ordI w 𝔫 := fun w => by
    have := (h.2 w).symm.trans (h'.2 w)
    rw [WithZero.exp_inj] at this
    omega
  rw [← Ideal.finprod_heightOneSpectrum_factorization h.1, ← Ideal.finprod_heightOneSpectrum_factorization h'.1]
  refine finprod_congr fun w => ?_
  exact congrArg (fun n => w.asIdeal ^ n) (hc w)

private theorem coefAt_eq {y : Af F} {𝔪 : Ideal (𝓞 F)} (h : GenD y 𝔪) (a : Ideal (𝓞 F) → ℂ) : coefAt a y = a 𝔪 := by
  have h' : ∃ 𝔪, GenD y 𝔪 := ⟨𝔪, h⟩
  rw [coefAt, dif_pos h', genD_unique h'.choose_spec h]

private theorem coefAt_zero {y : Af F} (h : ¬ ∃ 𝔪, GenD y 𝔪) (a : Ideal (𝓞 F) → ℂ) : coefAt a y = 0 := dif_neg h

private theorem coefAt_unit {u : Af F} (hu : ∀ w, Valued.v (pLoc F w u) = 1) (y : Af F) (a : Ideal (𝓞 F) → ℂ) :
    coefAt a (y * u) = coefAt a y := by
  have h : ∀ 𝔪, GenD (y * u) 𝔪 ↔ GenD y 𝔪 := fun 𝔪 => by simp only [GenD, map_mul, hu, mul_one]
  by_cases h' : ∃ 𝔪, GenD y 𝔪
  · obtain ⟨𝔪, h'⟩ := h'
    rw [coefAt_eq h', coefAt_eq ((h _).2 h')]
  · rw [coefAt_zero h', coefAt_zero (by simpa only [h] using h')]

private theorem ordI_fin {I : Ideal (𝓞 F)} (hI : I ≠ ⊥) : ∀ᶠ w : HeightOneSpectrum (𝓞 F) in Filter.cofinite, ordI w I = 0 := by
  have := Associates.finite_factors (R := 𝓞 F) hI
  filter_upwards [this] with w hw
  exact_mod_cast hw

private theorem exists_genD {𝔪 : Ideal (𝓞 F)} (h : 𝔪 ≠ ⊥) : ∃ y : (Af F)ˣ, GenD (y : Af F) 𝔪 := by
  choose t ht using fun w : HeightOneSpectrum (𝓞 F) => w.valuedAdicCompletion_surjective F
    (WithZero.exp ((ordI w (differentIdeal ℤ (𝓞 F)) : ℤ) - (ordI w 𝔪 : ℤ)))
  have hf : ∀ᶠ w in Filter.cofinite, Valued.v (t w) = 1 := by
    filter_upwards [ordI_fin h, ordI_fin (I := differentIdeal ℤ (𝓞 F)) differentIdeal_ne_bot] with w h1 h2
    rw [ht, h1, h2]; simp
  let a : FiniteAdeleRing (𝓞 F) F := ⟨t, by
    filter_upwards [hf] with w hw
    exact (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).2 hw.le⟩
  have hu : IsUnit a := FiniteAdeleRing.isUnit_iff.2 ⟨fun w hw => by
    have := ht w
    rw [show t w = 0 from hw, map_zero] at this
    exact WithZero.exp_ne_zero this.symm, hf⟩
  exact ⟨hu.unit, h, fun w => ht w⟩

private theorem exists_ideal (n : Pl F → ℕ) (hn : ∀ᶠ w in Filter.cofinite, n w = 0) :
    ∃ 𝔪 : Ideal (𝓞 F), 𝔪 ≠ ⊥ ∧ ∀ w, ordI w 𝔪 = n w := by
  have h0 : (∏ᶠ w : Pl F, w.asIdeal ^ n w) ≠ ⊥ :=
    finprod_induction (fun I : Ideal (𝓞 F) => I ≠ 0) one_ne_zero (fun _ _ => mul_ne_zero) fun w => pow_ne_zero _ w.ne_bot
  refine ⟨_, h0, fun w => ?_⟩
  have h1 := FractionalIdeal.count_coe F w h0
  have h2 := FractionalIdeal.count_finprod F w (fun w => (n w : ℤ)) (by filter_upwards [hn] with w hw using by simp [hw])
  rw [FractionalIdeal.coeIdeal_finprod _ _ le_rfl] at h1
  simp only [FractionalIdeal.coeIdeal_pow] at h1
  simp only [zpow_natCast] at h2
  exact_mod_cast h1.symm.trans h2

private theorem genD_of_le {y : Af F} (hy : IsUnit y)
    (h : ∀ w, Valued.v (pLoc F w y) ≤ WithZero.exp (ordI w (differentIdeal ℤ (𝓞 F)) : ℤ)) : ∃ 𝔪, GenD y 𝔪 := by
  obtain ⟨h1, h2⟩ := FiniteAdeleRing.isUnit_iff.1 hy
  have h3 : ∀ w, Valued.v (pLoc F w y) ≠ 0 := fun w => (map_ne_zero _).2 (h1 w)
  obtain ⟨𝔪, h0, hm⟩ := exists_ideal
    (fun w => ((ordI w (differentIdeal ℤ (𝓞 F)) : ℤ) - WithZero.log (Valued.v (pLoc F w y))).toNat) (by
      filter_upwards [h2, ordI_fin (I := differentIdeal ℤ (𝓞 F)) differentIdeal_ne_bot] with w e1 e2
      rw [show Valued.v (pLoc F w y) = 1 from e1, e2]; simp)
  refine ⟨𝔪, h0, fun w => ?_⟩
  have h4 := h w
  rw [← WithZero.exp_log (h3 w), WithZero.exp_le_exp] at h4
  rw [hm, ← WithZero.exp_log (h3 w), WithZero.exp_inj, WithZero.log_exp]
  omega

private theorem genD_add {y z : Af F} (hu : IsUnit (y + z)) (hy : ∃ 𝔪, GenD y 𝔪) (hz : ∃ 𝔪, GenD z 𝔪) : ∃ 𝔪, GenD (y + z) 𝔪 := by
  obtain ⟨𝔪, -, hy⟩ := hy
  obtain ⟨𝔫, -, hz⟩ := hz
  refine genD_of_le hu fun w => ?_
  rw [map_add]
  refine Valuation.map_add_le _ ?_ ?_
  · rw [hy, WithZero.exp_le_exp]; omega
  · rw [hz, WithZero.exp_le_exp]; omega

variable [IsTotallyReal F]

private theorem reAt_eq (v : InfinitePlace F) (x : F) :
    reAt v x = InfinitePlace.embedding_of_isReal (IsTotallyReal.isReal v) x := by
  rw [reAt, ← InfinitePlace.embedding_of_isReal_apply (IsTotallyReal.isReal v), Complex.ofReal_re]

private theorem pInf_alg (v : InfinitePlace F) (x : F) : TR.pInf F (algebraMap F (Ad F) x) v = reAt v x := by
  rw [reAt_eq]
  change InfinitePlace.Completion.ringEquivRealOfIsReal (IsTotallyReal.isReal v) (algebraMap F (InfiniteAdeleRing F) x v) = _
  simp

private theorem rat_aff (ξ : Fˣ) (t : (TR.Rinf F)ˣ) (ht : ∀ v, t.val v = reAt v (ξ : F)) (y : (Af F)ˣ) :
    ratGL F 2 (aff ξ 0) * (TR.infGL F 2 (aff 1 0) * finGL F 2 (aff y 0)) =
      TR.infGL F 2 (aff t 0) * finGL F 2 (aff (Units.map (algebraMap F (Af F)).toMonoidHom ξ * y) 0) := by
  have h1 : TR.pInf F (algebraMap F (Ad F) ξ) = t := funext fun v => by rw [pInf_alg, ht]
  have h2 : pFin F (algebraMap F (Ad F) ξ) = algebraMap F (Af F) ξ := rfl
  refine TR.ga_ext ?_ ?_
  · simp only [map_mul, TR.pInf_infGL, TR.pInf_finGL, mul_one]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [ratGL, aff, Matrix.mul_apply, Fin.sum_univ_succ, h1]
  · simp only [map_mul, TR.pFin_infGL, pFin_finGL, one_mul]
    ext i j : 2
    fin_cases i <;> fin_cases j <;> simp [ratGL, aff, Matrix.mul_apply, Fin.sum_univ_succ, h2]

private theorem const_unit {k : ℕ} {c : Pl F → ℕ} {ω : HChar F} {ψ : TR.Sm F 2} (h : IsHol k c ω ψ) {d₀ b} (he : HasExp ψ.1 k d₀ b)
    (y u : (Af F)ˣ) (hu : ∀ w, Valued.v (pLoc F w (u : Af F)) = 1) : d₀ (y * u) = d₀ y := by
  obtain ⟨-, a2, a3, -⟩ := Hm.absf F
  have h1 := he 0 1 (by simp) y
  have h2 := he 0 1 (by simp) (y * u)
  have e : aff (y * u) (0 : Af F) = aff y 0 * aff u 0 := by
    ext i j : 2
    fin_cases i <;> fin_cases j <;> simp [aff, Matrix.mul_apply, Fin.sum_univ_succ]
  simp only [Units.val_mul, ← mul_assoc, coefAt_unit hu] at h2
  rw [e, map_mul, ← mul_assoc, Hm.fixunit F ψ h.aut.level c h.level u hu, a2, a3 u hu, mul_one] at h2
  exact sub_right_injective (h2.unique h1)

private theorem const_rat {k : ℕ} {ψ : TR.Sm F 2} (h : TR.IsAutForm ψ) {d₀ b} (he : HasExp ψ.1 k d₀ b)
    (y : (Af F)ˣ) (ξ : Fˣ) (hξ : ∀ v, 0 < reAt v (ξ : F)) : d₀ (Units.map (algebraMap F (Af F)).toMonoidHom ξ * y) = d₀ y := by
  obtain ⟨-, a2, -, a4⟩ := Hm.absf F
  let t : (TR.Rinf F)ˣ := ⟨fun v => reAt v (ξ : F), fun v => (reAt v (ξ : F))⁻¹, funext fun v => mul_inv_cancel₀ (hξ v).ne',
    funext fun v => inv_mul_cancel₀ (hξ v).ne'⟩
  have h1 := he 0 1 (by simp) y
  have h2 := he 0 t hξ (Units.map (algebraMap F (Af F)).toMonoidHom ξ * y)
  have e1 : (∏ v, t.val v) * absF (Units.map (algebraMap F (Af F)).toMonoidHom ξ * y) =
      (∏ v, (1 : (TR.Rinf F)ˣ).val v) * absF y := by
    have := a4 ξ
    simp only [fun v => abs_of_pos (hξ v)] at this
    rw [a2, ← mul_assoc]
    congr 1
    simpa using this
  rw [← rat_aff ξ t (fun _ => rfl), h.left, e1] at h2
  have hm : ∀ v (a b : F), reAt v (a * b) = reAt v a * reAt v b := fun v a b => by simp only [reAt_eq, map_mul]
  let e : {η : F // ∀ v, 0 < reAt v η} ≃ {η : F // ∀ v, 0 < reAt v η} :=
    (Equiv.mulRight₀ (ξ : F) ξ.ne_zero).subtypeEquiv fun η => forall_congr' fun v => by
      simp [hm, hξ v]
  have h3 := e.hasSum_iff.2 h1
  refine sub_right_injective (h2.unique ?_)
  convert h3 using 2 with η
  simp [e, t, hm, mul_assoc, mul_left_comm, mul_comm]

open Classical in
private def cf (a : Ideal (𝓞 F) → ℂ) (y : Af F) (ξ : F) : ℂ :=
  if ∀ v, 0 < reAt v ξ then coefAt a (algebraMap F (Af F) ξ * y) else 0

private theorem hasSum_cf (a : Ideal (𝓞 F) → ℂ) (y : Af F) (E : F → ℂ) (S : ℂ) :
    HasSum (fun ξ : {ξ : F // ∀ v, 0 < reAt v ξ} => coefAt a (algebraMap F (Af F) ξ.1 * y) * E ξ.1) S ↔
      HasSum (fun ξ => cf a y ξ * E ξ) S := by
  rw [← hasSum_subtype_iff_of_support_subset (s := {ξ : F | ∀ v, 0 < reAt v ξ})]
  · refine Iff.of_eq (congrArg (HasSum · S) (funext fun ξ => ?_))
    have := ξ.2
    simp [cf, this]
  · intro ξ h
    by_contra h'
    exact h (by simp only [cf]; rw [if_neg (show ¬ ∀ v, 0 < reAt v ξ from h'), zero_mul])

private theorem cf_ne {a : Ideal (𝓞 F) → ℂ} {y : Af F} {ξ : F} (h : cf a y ξ ≠ 0) :
    (∀ v, 0 < reAt v ξ) ∧ ∃ 𝔪, GenD (algebraMap F (Af F) ξ * y) 𝔪 ∧ cf a y ξ = a 𝔪 := by
  by_cases h1 : ∀ v, 0 < reAt v ξ
  · rw [cf, if_pos h1] at h ⊢
    by_cases h2 : ∃ 𝔪, GenD (algebraMap F (Af F) ξ * y) 𝔪
    · obtain ⟨𝔪, h2⟩ := h2
      exact ⟨h1, 𝔪, h2, coefAt_eq h2 a⟩
    · exact absurd (coefAt_zero h2 a) h
  · exact absurd (if_neg h1) h

private theorem cf_unit {u : Af F} (hu : ∀ w, Valued.v (pLoc F w u) = 1) (y : Af F) (a : Ideal (𝓞 F) → ℂ) :
    cf a (y * u) = cf a y := funext fun ξ => by simp only [cf, ← mul_assoc, coefAt_unit hu]

private theorem cf_rat {ξ : F} (hξ : ∀ v, 0 < reAt v ξ) (y : Af F) (a : Ideal (𝓞 F) → ℂ) (η : F) :
    cf a (algebraMap F (Af F) ξ * y) η = cf a y (η * ξ) := by
  have hm : ∀ v, 0 < reAt v (η * ξ) ↔ 0 < reAt v η := fun v => by
    have := hξ v
    simp only [reAt_eq, map_mul] at this ⊢
    exact mul_pos_iff_of_pos_right this
  simp only [cf, hm, map_mul, mul_assoc]

private def cv (a b : Ideal (𝓞 F) → ℂ) (y : Af F) (ξ : F) : ℂ := ∑' η, cf a y η * cf b y (ξ - η)

private theorem ne_zero_of_pos {ξ : F} (hξ : ∀ v, 0 < reAt v ξ) : ξ ≠ 0 := by
  rintro rfl
  obtain ⟨v⟩ : Nonempty (InfinitePlace F) := inferInstance
  simpa [reAt] using hξ v

private theorem cv_rat {ξ : F} (hξ : ∀ v, 0 < reAt v ξ) (y : Af F) (a b : Ideal (𝓞 F) → ℂ) :
    cv a b (algebraMap F (Af F) ξ * y) 1 = cv a b y ξ := by
  rw [cv, cv, ← (Equiv.mulRight₀ ξ (ne_zero_of_pos hξ)).tsum_eq (fun η => cf a y η * cf b y (ξ - η))]
  simp [cf_rat hξ, sub_mul]

private theorem cv_ne {a b : Ideal (𝓞 F) → ℂ} {y : (Af F)ˣ} {ξ : F} (h : cv a b y ξ ≠ 0) :
    (∀ v, 0 < reAt v ξ) ∧ ∃ 𝔪, GenD (algebraMap F (Af F) ξ * (y : Af F)) 𝔪 := by
  obtain ⟨η, hη⟩ : ∃ η, cf a y η * cf b y (ξ - η) ≠ 0 := by
    by_contra h'
    push Not at h'
    exact h (by simp only [cv, h', tsum_zero])
  obtain ⟨h1, 𝔪, h2, -⟩ := cf_ne (left_ne_zero_of_mul hη)
  obtain ⟨h3, 𝔫, h4, -⟩ := cf_ne (right_ne_zero_of_mul hη)
  have h5 : ∀ v, 0 < reAt v ξ := fun v => by
    have e1 := h1 v
    have e2 := h3 v
    simp only [reAt_eq, map_sub] at e1 e2 ⊢
    linarith
  have e : algebraMap F (Af F) η * (y : Af F) + algebraMap F (Af F) (ξ - η) * (y : Af F) = algebraMap F (Af F) ξ * (y : Af F) := by
    rw [map_sub]; ring
  refine ⟨h5, e ▸ genD_add ?_ ⟨_, h2⟩ ⟨_, h4⟩⟩
  rw [e]
  exact ((ne_zero_of_pos h5).isUnit.map _).mul y.isUnit

private theorem cv_norm {l : ℕ} [Fact l.Prime] (ι : Qbar l ≃+* ℂ) {a b : Ideal (𝓞 F) → ℂ}
    (ha : ∀ 𝔪, 𝔪 ≠ ⊥ → ‖ι.symm (a 𝔪)‖ ≤ 1) (hb : ∀ 𝔪, 𝔪 ≠ ⊥ → ‖ι.symm (b 𝔪)‖ < 1) (y : (Af F)ˣ) (ξ : F) :
    ‖ι.symm (cv a b y ξ)‖ < 1 := by
  have hf := Hm.boxfin F y ξ
  rw [cv, tsum_eq_sum (s := hf.toFinset)]
  · refine Finset.sum_induction _ (fun z => ‖ι.symm z‖ < 1) (fun x z hx hz => ?_) (by simp) fun η _ => ?_
    · rw [map_add]
      exact (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt hx hz)
    · by_cases h : cf a y η * cf b y (ξ - η) = 0
      · simp [h]
      obtain ⟨-, 𝔪, h2, e1⟩ := cf_ne (left_ne_zero_of_mul h)
      obtain ⟨-, 𝔫, h4, e2⟩ := cf_ne (right_ne_zero_of_mul h)
      rw [e1, e2, map_mul, norm_mul]
      exact mul_lt_one_of_nonneg_of_lt_one_right (ha _ h2.1) (norm_nonneg _) (hb _ h4.1)
  · intro η hη
    by_contra h
    obtain ⟨h1, 𝔪, h2, -⟩ := cf_ne (left_ne_zero_of_mul h)
    obtain ⟨h3, -⟩ := cf_ne (right_ne_zero_of_mul h)
    refine hη (hf.mem_toFinset.2 ⟨h1, fun v => ?_, _, h2⟩)
    have e2 := h3 v
    simp only [reAt_eq, map_sub] at e2 ⊢
    linarith

private theorem hol_mul {k k' : ℕ} {c : Pl F → ℕ} {ω : HChar F} (hω : IsOfFinOrder ω) {φ ψ : TR.Sm F 2} (hφ : IsHol k c ω φ)
    (hψ : IsHol k' c 1 ψ) : ∃ χ : TR.Sm F 2, χ.1 = φ.1 * ψ.1 ∧ IsHol (k + k') c ω χ := by
  obtain ⟨h1, h2⟩ := Hm.mulsm F 2 φ ψ
  let χ : TR.Sm F 2 := ⟨_, h1⟩
  have hE : ∀ v i j g, (TR.Eop v i j χ).1 g = (TR.Eop v i j φ).1 g * ψ.1 g + φ.1 g * (TR.Eop v i j ψ).1 g :=
    fun v i j g => congrFun (h2 χ rfl _) g
  have hχ : ∀ g, χ.1 g = φ.1 g * ψ.1 g := fun _ => rfl
  have h3 : ∀ v, TR.Eop v 0 0 χ + TR.Eop v 1 1 χ = 0 := fun v => Subtype.ext (funext fun g => by
    have e1 := congrArg (·.1 g) (Hm.trzero F ω hω φ hφ.cent v)
    have e2 := congrArg (·.1 g) (Hm.trzero F 1 IsOfFinOrder.one ψ hψ.cent v)
    simp only [Submodule.coe_add, Pi.add_apply, Submodule.coe_zero, Pi.zero_apply, hE] at e1 e2 ⊢
    linear_combination ψ.1 g * e1 + φ.1 g * e2)
  have h4 : ∀ v, TR.Eop v 0 1 χ - TR.Eop v 1 0 χ = (Complex.I * (k + k' : ℕ)) • χ := fun v => Subtype.ext (funext fun g => by
    have e1 := congrArg (·.1 g) (hφ.wt v)
    have e2 := congrArg (·.1 g) (hψ.wt v)
    simp only [Submodule.coe_sub, Pi.sub_apply, Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, hE, hχ] at e1 e2 ⊢
    push_cast
    linear_combination ψ.1 g * e1 + φ.1 g * e2)
  have h5 : ∀ v, TR.Eop v 0 0 χ - TR.Eop v 1 1 χ = Complex.I • (TR.Eop v 0 1 χ + TR.Eop v 1 0 χ) :=
    fun v => Subtype.ext (funext fun g => by
      have e1 := congrArg (·.1 g) (hφ.low v)
      have e2 := congrArg (·.1 g) (hψ.low v)
      simp only [Submodule.coe_sub, Pi.sub_apply, Submodule.coe_add, Pi.add_apply, Submodule.coe_smul, Pi.smul_apply,
        smul_eq_mul, hE] at e1 e2 ⊢
      linear_combination ψ.1 g * e1 + φ.1 g * e2)
  refine ⟨χ, rfl, Hm.mulaut F 2 φ ψ χ rfl hφ.aut hψ.aut (Hm.zfinof F _ χ h3 h4 h5), fun w u hu => ?_, fun z g => ?_, h4, h5⟩
  · refine Subtype.ext (funext fun g => ?_)
    exact congrArg₂ (· * ·) (congrArg (·.1 g) (hφ.level w u hu)) (congrArg (·.1 g) (hψ.level w u hu))
  · rw [hχ, hχ, hφ.cent, hψ.cent]
    simp [mul_assoc]

end UpperTheory.V.Sd

open UpperTheory.V.Sd in
theorem UpperTheory.V.Sd.holMul :
    UpperTheory.V.Sd.HolMul := by
  classical
  intro F _ _ _ l _ ι k k' c ω hω φ ψ a d₀ b hφ hψ ea eb ha hd hb
  obtain ⟨χ, hχ, hh⟩ := hol_mul hω hφ ((holLin F k' _ 1).2.2.2.2 ψ c (fun _ => Nat.zero_le _) hψ)
  choose! Y hY using fun 𝔪 : Ideal (𝓞 F) => exists_genD (𝔪 := 𝔪)
  let A : (Af F)ˣ → ℂ := fun y => cf a y 1 * d₀ y + cv a b y 1
  have one : ∀ v : InfinitePlace F, 0 < reAt v (1 : F) := fun v => by simp [reAt]
  have cf1 : ∀ y : Af F, cf a y 1 = coefAt a y := fun y => by rw [cf, if_pos one, map_one, one_mul]
  have hA : ∀ y : (Af F)ˣ, coefAt (fun 𝔪 => A (Y 𝔪)) y = A y := fun y => by
    by_cases h : ∃ 𝔪, GenD (y : Af F) 𝔪
    · obtain ⟨𝔪, h⟩ := h
      have hu : ∀ w, Valued.v (pLoc F w ((y⁻¹ * Y 𝔪 : (Af F)ˣ) : Af F)) = 1 := fun w => by
        have e := congrArg (fun x : (Af F)ˣ => Valued.v (pLoc F w (x : Af F))) (mul_inv_cancel_left y (Y 𝔪))
        simp only [Units.val_mul (a := y), map_mul, (hY 𝔪 h.1).2 w, h.2 w] at e
        exact (mul_eq_left₀ WithZero.exp_ne_zero).1 e
      rw [coefAt_eq h, ← mul_inv_cancel_left y (Y 𝔪)]
      simp only [A, cv, Units.val_mul (a := y), cf_unit hu, const_unit hψ eb y _ hu]
    · rw [coefAt_zero h]
      have : cv a b y 1 = 0 := by
        by_contra h'
        exact h (by simpa using (cv_ne h').2)
      simp only [A, this, cf1, coefAt_zero h, zero_mul, add_zero]
  refine ⟨χ, fun 𝔪 => A (Y 𝔪), hh, fun x t ht y => ?_, fun 𝔪 hm => ?_⟩
  · set E : F → ℂ := fun ξ =>
      Complex.exp (2 * Real.pi * Complex.I * ∑ v, (reAt v ξ : ℂ) * ((x v : ℂ) + Complex.I * (t.val v : ℂ))) with hE
    have hE' : ∀ ξ η, E η * E (ξ - η) = E ξ := fun ξ η => by
      simp only [hE, ← Complex.exp_add, ← mul_add, ← Finset.sum_add_distrib, ← add_mul, reAt_eq, map_sub]
      simp
    have h1 := (hasSum_cf a y E _).1 (ea x t ht y)
    have h2 := (hasSum_cf b y E _).1 (eb x t ht y)
    have h3 := (h1.mul_right (d₀ y)).add (conv h1 h2)
    refine (hasSum_cf (fun 𝔪 => A (Y 𝔪)) y E _).2 ?_
    have hp : 0 < (∏ v, t.val v) * absF y := mul_pos (Finset.prod_pos fun v _ => ht v) ((Hm.absf F).1 y)
    convert h3 using 1
    · rfl
    · funext ξ
      have e : ∑' η, cf a y η * E η * (cf b y (ξ - η) * E (ξ - η)) = cv a b y ξ * E ξ := by
        rw [cv, ← tsum_mul_right]
        exact tsum_congr fun η => by rw [← hE' ξ η]; ring
      rw [e]
      by_cases h : ∀ v, 0 < reAt v ξ
      · have e1 := hA (Units.map (algebraMap F (Af F)).toMonoidHom (Units.mk0 ξ (ne_zero_of_pos h)) * y)
        simp only [A, const_rat hψ.aut eb y (Units.mk0 ξ (ne_zero_of_pos h)) h] at e1
        change coefAt _ (algebraMap F (Af F) ξ * (y : Af F)) =
          cf a (algebraMap F (Af F) ξ * (y : Af F)) 1 * _ + cv a b (algebraMap F (Af F) ξ * (y : Af F)) 1 at e1
        rw [cf, if_pos h, e1, cf_rat h, cv_rat h, one_mul]
        ring
      · have : cv a b y ξ = 0 := by
          by_contra h'
          exact h (cv_ne h').1
        simp only [cf, if_neg h, this, zero_mul, add_zero]
    · rw [hχ, Pi.mul_apply, Nat.cast_add, add_div, Real.rpow_add hp]
      push_cast
      simp only [Pi.zero_apply]
      rw [← div_mul_div_comm]
      ring
  · have e : A (Y 𝔪) - a 𝔪 = a 𝔪 * (d₀ (Y 𝔪) - 1) + cv a b (Y 𝔪) 1 := by
      simp only [A, cf1, coefAt_eq (hY 𝔪 hm)]; ring
    rw [e, map_add, map_mul, map_sub, map_one]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt ?_ (cv_norm ι ha hb _ _))
    rw [norm_mul]
    exact mul_lt_one_of_nonneg_of_lt_one_right (ha _ hm) (norm_nonneg _) (hd _)
