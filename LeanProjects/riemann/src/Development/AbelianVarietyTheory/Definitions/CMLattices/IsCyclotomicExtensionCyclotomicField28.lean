import Mathlib
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.PrincipalRootReZeroImSq
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.ExistsEquivOfSumEq

noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Polynomial
open scoped TensorProduct Pointwise

namespace GlobalTheory.CM

section General

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem baseChange_neg_form (D : Datum H) (x y : ℝ ⊗[ℤ] D.La) :
    (-D.EF).baseChange ℝ x y = -D.EF.baseChange ℝ x y := by
  induction x with
  | zero => simp
  | add a b ha hb => simp only [map_add, LinearMap.add_apply, ha, hb]; ring
  | tmul r a =>
    induction y with
    | zero => simp
    | add a b ha hb => simp only [map_add, ha, hb]; ring
    | tmul s b => simp

def oppDatum (D : Datum H) : Datum H where
  La := D.La
  fin := D.fin
  proj := D.proj
  EF := -D.EF
  alt x := by simp [D.alt]
  unimod := by
    have : (⇑(-D.EF) : D.La → _) = (fun f => -f) ∘ D.EF := rfl
    rw [this]
    exact neg_involutive.bijective.comp D.unimod
  adj a x y := by simp [D.adj]
  p := D.q
  q := D.p
  rank := by rw [D.rank, add_comm]
  dom := by
    obtain ⟨J, h1, h2, h3, h4⟩ := D.dom
    refine ⟨-J, fun x => by simp [h1], fun x y => ?_, fun x hx => ?_, fun a A t hA ht => ?_⟩
    · simp [baseChange_neg_form, h2]
    · simpa [baseChange_neg_form] using h3 x hx
    · obtain ⟨e1, e2, e3⟩ := h4 a A (starRingEnd ℂ t) hA (by
        rw [ht, map_sum]
        refine Finset.sum_congr rfl fun τ _ => ?_
        simp [add_comm])
      refine ⟨by rw [LinearMap.neg_comp, LinearMap.comp_neg, e1], by simpa using e2, ?_⟩
      rw [LinearMap.neg_comp, map_neg, e3]
      simp

@[simp] theorem oppDatum_p (D : Datum H) : (oppDatum D).p = D.q := rfl

@[simp] theorem oppDatum_q (D : Datum H) : (oppDatum D).q = D.p := rfl

theorem exists_type_period (D : Datum H) : ∃ (g : ℕ) (ty : Fin g → (E →+* ℂ)) (Pe : D.La →+ (Fin g → ℂ)),
    IsTypeFn H D.p D.q ty ∧ IsPeriod D ty Pe := by
  classical
  let n : (E →+* ℂ) → ℕ := fun τ => if τ (H.rt : E) = H.rt0 then D.p else D.q
  let e := (Fintype.equivFin (Σ τ, Fin (n τ))).symm
  have key : ∀ τ, Nat.card {i // (e i).1 = τ} = n τ := fun τ => by
    rw [Nat.card_congr ((e.subtypeEquiv (q := fun s => s.1 = τ) fun _ => Iff.rfl).trans (Equiv.sigmaSubtype τ))]
    simp
  have hty : IsTypeFn H D.p D.q fun i => (e i).1 :=
    fun τ => ⟨fun h => (key τ).trans (if_pos h), fun h => (key τ).trans (if_neg h)⟩
  obtain ⟨Pe, hP⟩ := PeriodNonempty.exists_isPeriod E H D _ _ hty
  exact ⟨_, _, Pe, hty, hP⟩

end General

namespace CyclotomicTwentyEight

abbrev CyclotomicFieldTwentyEight : Type := CyclotomicField 28 ℚ

instance isCyclotomicExtension_cyclotomicField28 : IsCyclotomicExtension {28} ℚ CyclotomicFieldTwentyEight := CyclotomicField.isCyclotomicExtension 28 ℚ

instance isCMField_cyclotomicField28 : IsCMField CyclotomicFieldTwentyEight := IsCyclotomicExtension.Rat.isCMField CyclotomicFieldTwentyEight (S := {28}) ⟨28, rfl, by norm_num⟩

theorem zeta_prim : IsPrimitiveRoot (IsCyclotomicExtension.zeta 28 ℚ CyclotomicFieldTwentyEight) 28 := IsCyclotomicExtension.zeta_spec 28 ℚ CyclotomicFieldTwentyEight

def z : 𝓞 CyclotomicFieldTwentyEight := zeta_prim.toInteger

theorem z_prim : IsPrimitiveRoot z 28 := zeta_prim.toInteger_isPrimitiveRoot

theorem z_pow_14 : z ^ 14 = -1 :=
  (z_prim.pow (by norm_num) (by norm_num : 28 = 14 * 2)).eq_neg_one_of_two_right

theorem z_root : z ^ 12 - z ^ 10 + z ^ 8 - z ^ 6 + z ^ 4 - z ^ 2 + 1 = 0 := by
  have h : IsPrimitiveRoot (z ^ 4) 7 := z_prim.pow (by norm_num) (by norm_num)
  have h2 := h.geom_sum_eq_zero (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at h2
  linear_combination h2 - (z ^ 2 + z ^ 6 + z ^ 10) * z_pow_14

def half : 𝓞 CyclotomicFieldTwentyEight := 1 - z ^ 2 + z ^ 4 + z ^ 8

theorem half_sq : half ^ 2 - half + 2 = 0 := by
  unfold half
  linear_combination 2 * z_root + z ^ 2 * z_pow_14

theorem rt_sq : (2 * half - 1) ^ 2 = -((7 : ℕ) : 𝓞 CyclotomicFieldTwentyEight) := by
  push_cast
  linear_combination 4 * half_sq

theorem unram : Algebra.Unramified (𝓞 (maximalRealSubfield CyclotomicFieldTwentyEight)) (𝓞 CyclotomicFieldTwentyEight) := by
  apply HostModel.unramified_of_isCoprime half (z ^ 7)
  have h1 : (z ^ 7) ^ 2 = -((1 : ℕ) : 𝓞 CyclotomicFieldTwentyEight) := by push_cast; linear_combination z_pow_14
  have h2 : IsCMField.ringOfIntegersComplexConj CyclotomicFieldTwentyEight (z ^ 7) = -z ^ 7 :=
    RingOfIntegers.ext (HostModel.complexConj_eq_neg_of_sq_eq_neg (HostModel.coe_sq_eq_neg h1))
  rw [HostModel.sub_complexConj_eq_of_two_mul rt_sq (by ring), h2]
  exact ⟨-(2 * half - 1), 3 * z ^ 7, by linear_combination -4 * half_sq + 6 * z_pow_14⟩

def host : Host CyclotomicFieldTwentyEight where
  d := 7
  d_mod := by norm_num
  d_prime := by norm_num
  rt := 2 * half - 1
  rt_sq := rt_sq
  w0 := half
  two_weight_eq_one_add_root := by ring
  bar := (IsCMField.ringOfIntegersComplexConj CyclotomicFieldTwentyEight).toRingEquiv
  bar_eq _ := rfl
  unram := unram
  rt0 := Complex.I * (Real.sqrt 7 : ℝ)
  sqrt_neg_disc_sq := by
    rw [mul_pow, Complex.I_sq, ← Complex.ofReal_pow, Real.sq_sqrt (by norm_num)]
    push_cast
    ring

theorem conj_cyclotomicTwentyEight_eq_neg_pow_thirteen : IsCMField.ringOfIntegersComplexConj CyclotomicFieldTwentyEight z = -z ^ 13 := by
  apply RingOfIntegers.ext
  let φ : CyclotomicFieldTwentyEight →+* ℂ := Classical.choice inferInstance
  apply φ.injective
  have e : φ (z : CyclotomicFieldTwentyEight) ^ 14 = -1 := by
    have := congrArg (fun x : 𝓞 CyclotomicFieldTwentyEight => φ (x : CyclotomicFieldTwentyEight)) z_pow_14
    simpa using this
  have hn : ‖φ (z : CyclotomicFieldTwentyEight)‖ = 1 := by
    have := congrArg norm e
    rw [norm_pow, norm_neg, norm_one] at this
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) (by norm_num)).1 this
  have hc := Complex.mul_conj' (φ (z : CyclotomicFieldTwentyEight))
  rw [hn] at hc
  change φ (IsCMField.complexConj CyclotomicFieldTwentyEight (z : CyclotomicFieldTwentyEight)) = _
  rw [IsCMField.complexEmbedding_complexConj]
  simp only [map_neg, map_pow, RingOfIntegers.coe_eq_algebraMap]
  simp only [RingOfIntegers.coe_eq_algebraMap] at e hc
  push_cast at hc
  linear_combination -(algebraMap (𝓞 CyclotomicFieldTwentyEight) CyclotomicFieldTwentyEight z |> φ) ^ 13 * hc + (starRingEnd ℂ) (φ (algebraMap (𝓞 CyclotomicFieldTwentyEight) CyclotomicFieldTwentyEight z)) * e

def dd : 𝓞 CyclotomicFieldTwentyEight := 12 * z ^ 11 - 10 * z ^ 9 + 8 * z ^ 7 - 6 * z ^ 5 + 4 * z ^ 3 - 2 * z

theorem aeval_derivative : aeval (z : CyclotomicFieldTwentyEight) (derivative (minpoly ℚ (z : CyclotomicFieldTwentyEight))) = (dd : CyclotomicFieldTwentyEight) := by
  have hi : IsIntegral ℚ (z : CyclotomicFieldTwentyEight) := Algebra.IsIntegral.isIntegral _
  have hm : minpoly ℚ (z : CyclotomicFieldTwentyEight) = X ^ 12 - X ^ 10 + X ^ 8 - X ^ 6 + X ^ 4 - X ^ 2 + 1 := by
    symm
    refine eq_of_monic_of_dvd_of_natDegree_le (minpoly.monic hi) (by monicity!) (minpoly.dvd _ _ ?_) ?_
    · have := congrArg (fun x : 𝓞 CyclotomicFieldTwentyEight => (x : CyclotomicFieldTwentyEight)) z_root
      simpa using this
    · have : minpoly ℚ (z : CyclotomicFieldTwentyEight) = cyclotomic 28 ℚ := (cyclotomic_eq_minpoly_rat zeta_prim (by norm_num)).symm
      rw [this, natDegree_cyclotomic, show Nat.totient 28 = 12 by decide]
      compute_degree
  rw [hm]
  simp [dd, map_ofNat]
  ring

theorem trace_dual (w : CyclotomicFieldTwentyEight) :
    (∀ a : 𝓞 CyclotomicFieldTwentyEight, ∃ n : ℤ, Algebra.trace ℚ CyclotomicFieldTwentyEight ((a : CyclotomicFieldTwentyEight) * w) = n) ↔ ∃ b : 𝓞 CyclotomicFieldTwentyEight, w = (dd : CyclotomicFieldTwentyEight)⁻¹ * b := by
  have hcl := IsCyclotomicExtension.Rat.isIntegralClosure_adjoin_singleton zeta_prim
  have hmem : ∀ x : CyclotomicFieldTwentyEight, x ∈ Algebra.adjoin ℤ {(z : CyclotomicFieldTwentyEight)} ↔ ∃ a : 𝓞 CyclotomicFieldTwentyEight, (a : CyclotomicFieldTwentyEight) = x := fun x => by
    constructor
    · intro hx
      exact ⟨⟨x, hcl.isIntegral_iff.2 ⟨⟨x, hx⟩, rfl⟩⟩, rfl⟩
    · rintro ⟨a, rfl⟩
      obtain ⟨y, hy⟩ := hcl.isIntegral_iff.1 a.isIntegral_coe
      have h2 : (y : CyclotomicFieldTwentyEight) ∈ Algebra.adjoin ℤ {(z : CyclotomicFieldTwentyEight)} := y.2
      have h3 : (y : CyclotomicFieldTwentyEight) = (a : CyclotomicFieldTwentyEight) := hy
      rwa [h3] at h2
  have h := traceForm_dualSubmodule_adjoin ℤ ℚ (x := (z : CyclotomicFieldTwentyEight))
    (IsCyclotomicExtension.adjoin_primitive_root_eq_top zeta_prim) z.isIntegral_coe
  rw [aeval_derivative] at h
  have h2 := SetLike.ext_iff.1 h w
  rw [LinearMap.BilinForm.mem_dualSubmodule, Submodule.mem_smul_pointwise_iff_exists] at h2
  simp only [Subalgebra.mem_toSubmodule, hmem, Submodule.mem_one, Algebra.traceForm_apply] at h2
  constructor
  · intro hw
    obtain ⟨_, ⟨b, rfl⟩, hb⟩ := h2.1 (by
      rintro _ ⟨a, rfl⟩
      obtain ⟨n, hn⟩ := hw a
      exact ⟨n, by rw [mul_comm, hn]; simp⟩)
    exact ⟨b, hb.symm⟩
  · rintro ⟨b, hb⟩ a
    obtain ⟨n, hn⟩ := h2.2 ⟨_, ⟨b, rfl⟩, hb.symm⟩ _ ⟨a, rfl⟩
    exact ⟨n, by rw [mul_comm, ← hn]; simp⟩

def bt : 𝓞 CyclotomicFieldTwentyEight := (1 + z ^ 7) * (1 - z ^ 4)

theorem conj_bt : IsCMField.ringOfIntegersComplexConj CyclotomicFieldTwentyEight bt = (1 - z ^ 7) * (1 + z ^ 10) := by
  have h28 : z ^ 28 = 1 := z_prim.pow_eq_one
  have e1 : (-z ^ 13) ^ 7 = -z ^ 7 := by linear_combination -(z ^ 63 + z ^ 35 + z ^ 7) * h28
  have e2 : (-z ^ 13) ^ 4 = -z ^ 10 := by linear_combination z ^ 24 * h28 + z ^ 10 * z_pow_14
  rw [bt, map_mul, map_add, map_sub, map_one, map_pow, map_pow, conj_cyclotomicTwentyEight_eq_neg_pow_thirteen, e1, e2]
  ring

theorem norm_bt : bt * IsCMField.ringOfIntegersComplexConj CyclotomicFieldTwentyEight bt * host.rt = (-z + z ^ 3 - z ^ 9) * dd := by
  rw [conj_bt]
  change _ * (2 * half - 1) = _
  unfold bt half dd
  linear_combination ((1) * z ^ 0 + (-3) * z ^ 2 + (3) * z ^ 4 + (-1) * z ^ 6 + (6) * z ^ 8 + (-5) * z ^ 10 + (3) * z ^ 12 + (3) * z ^ 14 + (-3) * z ^ 16 + (-2) * z ^ 18 + (2) * z ^ 22 + (2) * z ^ 24) * z_root

theorem unit_eq : (-z + z ^ 3 - z ^ 9) * (z ^ 3 + z ^ 7) = 1 := by
  linear_combination ((-1) * z ^ 0 + (-1) * z ^ 2 + (-1) * z ^ 4) * z_root

theorem exists_datum : ∃ D : Datum host, D.p = 1 ∧ D.q = 0 := by
  set c := IsCMField.complexConj CyclotomicFieldTwentyEight with hc
  have hN : (bt : CyclotomicFieldTwentyEight) * c (bt : CyclotomicFieldTwentyEight) * (host.rt : CyclotomicFieldTwentyEight) = ((-z + z ^ 3 - z ^ 9 : 𝓞 CyclotomicFieldTwentyEight) : CyclotomicFieldTwentyEight) * (dd : CyclotomicFieldTwentyEight) := by
    have := congrArg (algebraMap (𝓞 CyclotomicFieldTwentyEight) CyclotomicFieldTwentyEight) norm_bt
    rw [map_mul, map_mul, map_mul] at this
    exact this
  have hU : ((-z + z ^ 3 - z ^ 9 : 𝓞 CyclotomicFieldTwentyEight) : CyclotomicFieldTwentyEight) * ((z ^ 3 + z ^ 7 : 𝓞 CyclotomicFieldTwentyEight) : CyclotomicFieldTwentyEight) = 1 := by
    have := congrArg (algebraMap (𝓞 CyclotomicFieldTwentyEight) CyclotomicFieldTwentyEight) unit_eq
    rwa [map_mul, map_one] at this
  have hdd : (dd : CyclotomicFieldTwentyEight) ≠ 0 := by
    rw [← aeval_derivative]
    exact (Algebra.IsSeparable.isSeparable ℚ (z : CyclotomicFieldTwentyEight)).aeval_derivative_ne_zero (minpoly.aeval _ _)
  have hne : (bt : CyclotomicFieldTwentyEight) * c (bt : CyclotomicFieldTwentyEight) * (host.rt : CyclotomicFieldTwentyEight) ≠ 0 := by
    rw [hN]; exact mul_ne_zero (left_ne_zero_of_mul_eq_one hU) hdd
  have hb : (bt : CyclotomicFieldTwentyEight) ≠ 0 := left_ne_zero_of_mul (left_ne_zero_of_mul hne)
  have hcb : c (bt : CyclotomicFieldTwentyEight) ≠ 0 := right_ne_zero_of_mul (left_ne_zero_of_mul hne)
  have hrt : (host.rt : CyclotomicFieldTwentyEight) ≠ 0 := right_ne_zero_of_mul hne
  have hmem : ∀ y : CyclotomicFieldTwentyEight, y ∈ Submodule.span (𝓞 CyclotomicFieldTwentyEight) {(bt : CyclotomicFieldTwentyEight)⁻¹} ↔ ∃ a : 𝓞 CyclotomicFieldTwentyEight, (a : CyclotomicFieldTwentyEight) * (bt : CyclotomicFieldTwentyEight)⁻¹ = y :=
    fun y => Submodule.mem_span_singleton
  obtain ⟨D, -, hp, hq, -⟩ := PrincipalDatum.exists_datum CyclotomicFieldTwentyEight host (Submodule.span (𝓞 CyclotomicFieldTwentyEight) {(bt : CyclotomicFieldTwentyEight)⁻¹})
    (Submodule.fg_span_singleton _) (by simpa using hb) fun y => by
      have key := trace_dual ((bt : CyclotomicFieldTwentyEight)⁻¹ * c y / (host.rt : CyclotomicFieldTwentyEight))
      constructor
      · intro hy x hx
        obtain ⟨a, rfl⟩ := (hmem y).1 hy
        obtain ⟨b, rfl⟩ := (hmem x).1 hx
        have := key.2 ⟨host.bar a * (z ^ 3 + z ^ 7), by
          have e : ((host.bar a * (z ^ 3 + z ^ 7) : 𝓞 CyclotomicFieldTwentyEight) : CyclotomicFieldTwentyEight) = c a * ((z ^ 3 + z ^ 7 : 𝓞 CyclotomicFieldTwentyEight) : CyclotomicFieldTwentyEight) := by
            rw [← host.bar_eq]; exact map_mul (algebraMap (𝓞 CyclotomicFieldTwentyEight) CyclotomicFieldTwentyEight) _ _
          rw [e, map_mul, map_inv₀]
          field_simp
          linear_combination -c a * ((z ^ 3 + z ^ 7 : 𝓞 CyclotomicFieldTwentyEight) : CyclotomicFieldTwentyEight) * hN - c a * (dd : CyclotomicFieldTwentyEight) * hU⟩ b
        rwa [← mul_div_assoc, ← mul_assoc] at this
      · intro hy
        obtain ⟨b, hb'⟩ := key.1 fun a => by
          have := hy _ ((hmem _).2 ⟨a, rfl⟩)
          rwa [← mul_div_assoc, ← mul_assoc]
        refine (hmem y).2 ⟨host.bar (b * (-z + z ^ 3 - z ^ 9)), c.injective ?_⟩
        have e : ((b * (-z + z ^ 3 - z ^ 9) : 𝓞 CyclotomicFieldTwentyEight) : CyclotomicFieldTwentyEight) = b * ((-z + z ^ 3 - z ^ 9 : 𝓞 CyclotomicFieldTwentyEight) : CyclotomicFieldTwentyEight) :=
          map_mul (algebraMap (𝓞 CyclotomicFieldTwentyEight) CyclotomicFieldTwentyEight) _ _
        rw [map_mul, map_inv₀, host.bar_eq, IsCMField.complexConj_apply_apply, e]
        field_simp at hb' ⊢
        apply mul_right_cancel₀ hdd
        linear_combination -(b : CyclotomicFieldTwentyEight) * hN - c (bt : CyclotomicFieldTwentyEight) * hb'
  exact ⟨D, hp, hq⟩

end CyclotomicTwentyEight

end GlobalTheory.CM
