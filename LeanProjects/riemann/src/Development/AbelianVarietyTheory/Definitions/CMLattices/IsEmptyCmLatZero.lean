import Mathlib
import Development.AbelianVarietyTheory.Definitions.CMLattices.ExistsIsThetaDegOfIsLocalModel
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.PrincipalRootReZeroImSq
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.ExistsEquivOfSumEq
import Development.AbelianVarietyTheory.Statements.PrincipalLattices.EqZeroOfOppositeSign
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.TwoMulEqOfIsTypeFn

noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Polynomial
open scoped TensorProduct Pointwise

namespace GlobalTheory.CM.LatModel

section General

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem baseChange_neg_apply (D : Datum H) (x y : ℝ ⊗[ℤ] D.La) :
    (-D.EF).baseChange ℝ x y = -D.EF.baseChange ℝ x y := by
  induction x with
  | zero => simp
  | add a b ha hb => simp only [map_add, LinearMap.add_apply, ha, hb]; ring
  | tmul r a =>
    induction y with
    | zero => simp
    | add a b ha hb => simp only [map_add, ha, hb]; ring
    | tmul s b => simp

def negDatum (D : Datum H) : Datum H where
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
    · simp [baseChange_neg_apply, h2]
    · simpa [baseChange_neg_apply] using h3 x hx
    · obtain ⟨e1, e2, e3⟩ := h4 a A (starRingEnd ℂ t) hA (by
        rw [ht, map_sum]
        refine Finset.sum_congr rfl fun τ _ => ?_
        simp [add_comm])
      refine ⟨by rw [LinearMap.neg_comp, LinearMap.comp_neg, e1], by simpa using e2, ?_⟩
      rw [LinearMap.neg_comp, map_neg, e3]
      simp

def selfLat {D : Datum H} (hp : D.p = 1) (hq : D.q = 0) {g : ℕ} {ty : Fin g → (E →+* ℂ)}
    {Pe : D.La →+ (Fin g → ℂ)} (hP : IsPeriod D ty Pe) (hty : IsTypeFn H 1 0 ty) : CMLat hP 1 0 where
  D₁ b := match b with
    | true => D
    | false => negDatum D
  sigP := ⟨hp, hq⟩
  sigM := ⟨hq, hp⟩
  f j := match j with
    | .inl _ => LinearMap.id
    | .inr k => k.elim0
  pure j a := match j, a with
    | .inl _, a => by
      have := PureType.lat_eq_top hP hty
      simp [this]
    | .inr k, _ => k.elim0
  hh _ := 1
  form j a b := match j, a, b with
    | .inl _, a, b => by rw [one_smul]; rfl
    | .inr k, _, _ => k.elim0
  span := ⟨1, one_pos, fun a => ⟨fun j => match j with
    | .inl _ => a
    | .inr k => k.elim0, by simp; rfl⟩⟩

def selfLatNeg {D : Datum H} (hp : D.p = 1) (hq : D.q = 0) {g : ℕ} {ty : Fin g → (E →+* ℂ)}
    {Pe : (negDatum D).La →+ (Fin g → ℂ)} (hP : IsPeriod (negDatum D) ty Pe) (hty : IsTypeFn H 0 1 ty) :
    CMLat hP 0 1 where
  D₁ b := match b with
    | true => D
    | false => negDatum D
  sigP := ⟨hp, hq⟩
  sigM := ⟨hq, hp⟩
  f j := match j with
    | .inl k => k.elim0
    | .inr _ => LinearMap.id
  pure j a := match j, a with
    | .inl k, _ => k.elim0
    | .inr _, a => fun j hj => by
      exfalso
      have h2 : ty j (H.rt : E) ^ 2 = H.rt0 ^ 2 := by
        rw [← map_pow, HostModel.coe_sq_eq_neg H.rt_sq, H.sqrt_neg_disc_sq, map_neg, map_natCast]
      have h3 := (sq_eq_sq_iff_eq_or_eq_neg.1 h2).resolve_right (by simpa using hj)
      have : Nonempty {i // ty i = ty j} := ⟨⟨j, rfl⟩⟩
      exact absurd ((hty (ty j)).1 h3) Nat.card_pos.ne'
  hh _ := 1
  form j a b := match j, a, b with
    | .inl k, _, _ => k.elim0
    | .inr _, a, b => by rw [one_smul]; rfl
  span := ⟨1, one_pos, fun a => ⟨fun j => match j with
    | .inl k => k.elim0
    | .inr _ => a, by simp; rfl⟩⟩

end General

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

theorem exists_cmLat : ∃ (D : Datum host) (g : ℕ) (ty : Fin g → (CyclotomicFieldTwentyEight →+* ℂ)) (Pe : D.La →+ (Fin g → ℂ))
    (hP : IsPeriod D ty Pe) (Z : CMLat hP 1 0), D.p = 1 ∧ D.q = 0 ∧ Nontrivial D.La ∧
      ∀ j, Function.Injective (Z.f j) ∧ Z.hh j = 1 := by
  obtain ⟨D, hp, hq⟩ := exists_datum
  obtain ⟨g, ty, hty⟩ := PureTypeModel.exists_isTypeFn host 1 0
  obtain ⟨Pe, hP⟩ := PeriodNonempty.exists_isPeriod CyclotomicFieldTwentyEight host D g ty (by rw [hp, hq]; exact hty)
  refine ⟨D, g, ty, Pe, hP, selfLat hp hq hP hty, hp, hq, ?_, fun j => ?_⟩
  · refine Module.nontrivial_of_finrank_pos (R := 𝓞 CyclotomicFieldTwentyEight) ?_
    rw [D.rank, hp]; omega
  · rcases j with j | j
    · exact ⟨fun _ _ h => h, rfl⟩
    · exact j.elim0

theorem exists_cmLat_neg : ∃ (D : Datum host) (g : ℕ) (ty : Fin g → (CyclotomicFieldTwentyEight →+* ℂ)) (Pe : D.La →+ (Fin g → ℂ))
    (hP : IsPeriod D ty Pe) (Z : CMLat hP 0 1), D.p = 0 ∧ D.q = 1 ∧ ∀ j, Function.Injective (Z.f j) ∧ Z.hh j = 1 := by
  obtain ⟨D, hp, hq⟩ := exists_datum
  obtain ⟨g, ty, hty⟩ := PureTypeModel.exists_isTypeFn host 0 1
  obtain ⟨Pe, hP⟩ := PeriodNonempty.exists_isPeriod CyclotomicFieldTwentyEight host (negDatum D) g ty (by
    change IsTypeFn host D.q D.p ty
    rw [hp, hq]; exact hty)
  refine ⟨negDatum D, g, ty, Pe, hP, selfLatNeg hp hq hP hty, hq, hp, fun j => ?_⟩
  rcases j with j | j
  · exact j.elim0
  · exact ⟨fun _ _ h => h, rfl⟩

theorem logOm_quadratic {K : Type} [Field K] [NumberField K] {d : ℕ} [NeZero d] (h2 : Module.finrank ℚ K = 2)
    (hD : discr K = -d) (χ : DirichletCharacter ℂ d) :
    logOm K χ = (Real.eulerMascheroniConstant + Real.log (2 * Real.pi / √d) : ℝ) - deriv χ.LFunction 1 / χ.LFunction 1 := by
  rw [logOm, rootDiscr_def, h2, hD, Real.sqrt_eq_rpow]
  simp

theorem hasPeriod_unique {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {M : Type} [Field M]
    [NumberField M] {ω : 𝓞 M} {C : Ell H (𝓞 M) ω} {x y : ℝ} (hx : C.HasPeriod x) (hy : C.HasPeriod y) : x = y := by
  obtain ⟨n, hn, rfl⟩ := hx
  obtain ⟨m, hm, rfl⟩ := hy
  rw [show n = m from funext fun s => ((hm s).2 _).1 (((hn s).2 _).2 rfl)]

section Mixed

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem bar_hh {D : Datum H} {g : ℕ} {ty : Fin g → (E →+* ℂ)} {Pe : D.La →+ (Fin g → ℂ)} {hP : IsPeriod D ty Pe}
    {p q : ℕ} (Z : CMLat hP p q) (j : Fin p ⊕ Fin q) : H.bar (Z.hh j) = Z.hh j := by
  have skew : ∀ (D : Datum H) x y, D.EF x y = -D.EF y x := fun D x y => by
    have := D.alt (x + y)
    simp only [map_add, LinearMap.add_apply, D.alt] at this
    linarith
  have := (Z.D₁ j.isLeft).proj
  have : Nontrivial (Z.D₁ j.isLeft).La :=
    Module.nontrivial_of_finrank_pos (R := 𝓞 E) (by rw [Z.finrank_D₁]; exact one_pos)
  obtain ⟨b, hb⟩ := exists_ne (0 : (Z.D₁ j.isLeft).La)
  have e : H.bar (Z.hh j) • b = Z.hh j • b := (Z.D₁ j.isLeft).unimod.1 (LinearMap.ext fun a => by
    rw [skew, ← (Z.D₁ j.isLeft).adj, ← Z.form, ← skew, Z.form])
  rw [← sub_eq_zero, ← sub_smul, smul_eq_zero] at e
  exact sub_eq_zero.1 (e.resolve_right hb)

theorem im_mul_form_pos {D : Datum H} {g : ℕ} {ty : Fin g → (E →+* ℂ)} {Pe : D.La →+ (Fin g → ℂ)}
    (hP : IsPeriod D ty Pe) {ρ : ℂ} (hρ : ρ.im ≠ 0) {a : D.La} (ha : a ∈ PureType.lat hP ρ) (h0 : a ≠ 0) :
    0 < ρ.im * D.EF (H.w0 • a) a := by
  obtain ⟨Hm, -, hpos, hE⟩ := hP.2.2.2.2
  have hz : Pe a ≠ 0 := fun h => h0 (hP.2.1 (h.trans (map_zero Pe).symm))
  have h1 := hE (H.w0 • a) a
  have h2 := hE a a
  rw [D.alt] at h2
  have h3 : hermForm Hm (Pe (H.w0 • a)) (Pe a) = ((1 + ρ) / 2) * hermForm Hm (Pe a) (Pe a) := by
    rw [PureType.period_w0_smul hP ha, hermForm, hermForm, smul_dotProduct, smul_eq_mul]
  have h4 : ((1 + ρ) / 2).im = ρ.im / 2 := by simp
  rw [h3, Complex.mul_im, h2, h4] at h1
  rw [← h1]
  have := mul_pos (mul_self_pos.2 hρ) (hpos _ hz)
  push_cast
  linarith

theorem hh_sign {D : Datum H} {g : ℕ} {ty : Fin g → (E →+* ℂ)} {Pe : D.La →+ (Fin g → ℂ)} {hP : IsPeriod D ty Pe}
    {p q : ℕ} (Z : CMLat hP p q) (hpq : p + q = D.p + D.q) (j : Fin p ⊕ Fin q) {a : (Z.D₁ j.isLeft).La} (ha : a ≠ 0) :
    0 < (Z.D₁ j.isLeft).EF (Z.hh j • H.w0 • a) a * (Z.D₁ j.isLeft).EF (H.w0 • a) a := by
  have him : H.rt0.im ≠ 0 := by
    intro h
    have e := congrArg Complex.re H.sqrt_neg_disc_sq
    have hd : (0 : ℝ) < H.d := Nat.cast_pos.2 H.d_prime.pos
    simp [pow_two, h] at e
    nlinarith [mul_self_nonneg H.rt0.re]
  have him' : (if j.isLeft then H.rt0 else -H.rt0).im ≠ 0 := by split_ifs <;> simpa using him
  have h1 := im_mul_form_pos hP him' (Z.pure j a) fun e => ha (Z.f_injective hpq j (e.trans (map_zero _).symm))
  rw [← map_smul, Z.form] at h1
  obtain ⟨g₁, ty₁, P₁, ht, hP₁⟩ := exists_type_period (Z.D₁ j.isLeft)
  have h2 : a ∈ PureType.lat hP₁ (if j.isLeft then H.rt0 else -H.rt0) := by
    rcases j with j | j
    · simp only [Sum.isLeft_inl] at ht
      rw [Z.sigP.1, Z.sigP.2] at ht
      exact (CMLat.ofPositive Z.sigP.1 Z.sigP.2 hP₁ ht).pure (.inl 0) a
    · simp only [Sum.isLeft_inr] at ht
      rw [Z.sigM.1, Z.sigM.2] at ht
      exact (CMLat.ofNegative Z.sigM.1 Z.sigM.2 hP₁ ht).pure (.inr 0) a
  have h3 := im_mul_form_pos hP₁ him' h2 ha
  have h4 := mul_pos h1 h3
  have h5 := mul_self_pos.2 him'
  rw [mul_mul_mul_comm] at h4
  exact_mod_cast (pos_iff_pos_of_mul_pos h4).1 h5

theorem exists_sum (D₁ D₂ : Datum H) {g₁ g₂ : ℕ} {t₁ : Fin g₁ → (E →+* ℂ)} {t₂ : Fin g₂ → (E →+* ℂ)}
    {P₁ : D₁.La →+ (Fin g₁ → ℂ)} {P₂ : D₂.La →+ (Fin g₂ → ℂ)} (h₁ : IsPeriod D₁ t₁ P₁) (h₂ : IsPeriod D₂ t₂ P₂)
    (y₁ : IsTypeFn H D₁.p D₁.q t₁) (y₂ : IsTypeFn H D₂.p D₂.q t₂) :
    ∃ (D : Datum H) (e : D.La ≃ₗ[𝓞 E] D₁.La × D₂.La) (P : D.La →+ (Fin (g₁ + g₂) → ℂ)),
      D.p = D₁.p + D₂.p ∧ D.q = D₁.q + D₂.q ∧ (∀ x y, D.EF x y = D₁.EF (e x).1 (e y).1 + D₂.EF (e x).2 (e y).2) ∧
      IsTypeFn H D.p D.q (Fin.append t₁ t₂) ∧ IsPeriod D (Fin.append t₁ t₂) P ∧
      ∀ x, P x = Fin.append (P₁ (e x).1) (P₂ (e x).2) := by
  obtain ⟨l₁, i₁, d₁, s₁, M₁, m₁, p₁, e₁⟩ := h₁
  obtain ⟨l₂, i₂, d₂, s₂, M₂, m₂, p₂, e₂⟩ := h₂
  let EF : LinearMap.BilinForm ℤ (D₁.La × D₂.La) :=
    D₁.EF.compl₁₂ (LinearMap.fst ℤ _ _) (LinearMap.fst ℤ _ _) + D₂.EF.compl₁₂ (LinearMap.snd ℤ _ _) (LinearMap.snd ℤ _ _)
  have hEF : ∀ x y, EF x y = D₁.EF x.1 y.1 + D₂.EF x.2 y.2 := fun _ _ => rfl
  let Q : D₁.La × D₂.La →+ (Fin (g₁ + g₂) → ℂ) := AddMonoidHom.mk' (fun x => Fin.append (P₁ x.1) (P₂ x.2))
    fun x y => funext fun i => by refine Fin.addCases (fun i => ?_) (fun i => ?_) i <;> simp
  have hQ : ∀ x, Q x = Fin.append (P₁ x.1) (P₂ x.2) := fun _ => rfl
  let M : Matrix (Fin (g₁ + g₂)) (Fin (g₁ + g₂)) ℂ :=
    Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks M₁ 0 0 M₂)
  have hM : ∀ z w, hermForm M z w = hermForm M₁ (fun i => z (Fin.castAdd _ i)) (fun i => w (Fin.castAdd _ i)) +
      hermForm M₂ (fun i => z (Fin.natAdd _ i)) (fun i => w (Fin.natAdd _ i)) := fun z w => by
    simp [hermForm, M, dotProduct, Matrix.mulVec, Fin.sum_univ_add]
  have card : ∀ τ, Nat.card {i // Fin.append t₁ t₂ i = τ} = Nat.card {i // t₁ i = τ} + Nat.card {i // t₂ i = τ} :=
    fun τ => by
      rw [← Nat.card_sum]
      exact Nat.card_congr ((finSumFinEquiv.subtypeEquiv (p := fun s => Sum.elim t₁ t₂ s = τ) (by
        rintro (i | i) <;> simp)).symm.trans Equiv.subtypeSum)
  have hty : IsTypeFn H (D₁.p + D₂.p) (D₁.q + D₂.q) (Fin.append t₁ t₂) := fun τ =>
    ⟨fun h => by rw [card, (y₁ τ).1 h, (y₂ τ).1 h], fun h => by rw [card, (y₁ τ).2 h, (y₂ τ).2 h]⟩
  have hl : ∀ (a : 𝓞 E) x i, Q (a • x) i = Fin.append t₁ t₂ i (a : E) * Q x i := fun a x i => by
    refine Fin.addCases (fun i => ?_) (fun i => ?_) i <;> simp [hQ, l₁, l₂]
  have hi : Function.Injective Q := fun x y h => Prod.ext
    (i₁ (funext fun i => by simpa [hQ] using congrFun h (Fin.castAdd _ i)))
    (i₂ (funext fun i => by simpa [hQ] using congrFun h (Fin.natAdd _ i)))
  have hd : DiscreteTopology Q.range := by
    have c₁ : ∀ z : Q.range, (fun i => z.1 (Fin.castAdd g₂ i)) ∈ P₁.range := by
      rintro ⟨_, x, rfl⟩; exact ⟨x.1, by simp [hQ]⟩
    have c₂ : ∀ z : Q.range, (fun i => z.1 (Fin.natAdd g₁ i)) ∈ P₂.range := by
      rintro ⟨_, x, rfl⟩; exact ⟨x.2, by simp [hQ]⟩
    have k : ∀ j, Continuous fun z : Q.range => z.1 j := fun j => (continuous_apply j).comp continuous_subtype_val
    refine DiscreteTopology.of_continuous_injective (β := P₁.range × P₂.range)
      (((continuous_pi fun i => k _).subtype_mk c₁).prodMk ((continuous_pi fun i => k _).subtype_mk c₂)) ?_
    intro z w h
    have a := congrArg (fun u => u.1.1) h
    have b := congrArg (fun u => u.2.1) h
    exact Subtype.ext (funext fun i => Fin.addCases (fun i => congrFun a i) (fun i => congrFun b i) i)
  have hs : Submodule.span ℝ (Set.range Q) = ⊤ := by
    have A : ∀ z : Fin g₁ → ℂ, Fin.append z (0 : Fin g₂ → ℂ) ∈ Submodule.span ℝ (Set.range Q) := fun z => by
      have hz : z ∈ Submodule.span ℝ (Set.range P₁) := s₁ ▸ Submodule.mem_top
      induction hz using Submodule.span_induction with
      | mem x hx => obtain ⟨a, rfl⟩ := hx; exact Submodule.subset_span ⟨(a, 0), by simp [hQ]⟩
      | zero => convert Submodule.zero_mem _; funext i; refine Fin.addCases (fun i => ?_) (fun i => ?_) i <;> simp
      | add x y _ _ hx hy =>
        convert Submodule.add_mem _ hx hy; funext i; refine Fin.addCases (fun i => ?_) (fun i => ?_) i <;> simp
      | smul r x _ hx =>
        convert Submodule.smul_mem _ r hx; funext i; refine Fin.addCases (fun i => ?_) (fun i => ?_) i <;> simp
    have B : ∀ z : Fin g₂ → ℂ, Fin.append (0 : Fin g₁ → ℂ) z ∈ Submodule.span ℝ (Set.range Q) := fun z => by
      have hz : z ∈ Submodule.span ℝ (Set.range P₂) := s₂ ▸ Submodule.mem_top
      induction hz using Submodule.span_induction with
      | mem x hx => obtain ⟨a, rfl⟩ := hx; exact Submodule.subset_span ⟨(0, a), by simp [hQ]⟩
      | zero => convert Submodule.zero_mem _; funext i; refine Fin.addCases (fun i => ?_) (fun i => ?_) i <;> simp
      | add x y _ _ hx hy =>
        convert Submodule.add_mem _ hx hy; funext i; refine Fin.addCases (fun i => ?_) (fun i => ?_) i <;> simp
      | smul r x _ hx =>
        convert Submodule.smul_mem _ r hx; funext i; refine Fin.addCases (fun i => ?_) (fun i => ?_) i <;> simp
    refine top_le_iff.1 fun z _ => ?_
    convert Submodule.add_mem _ (A fun i => z (Fin.castAdd _ i)) (B fun i => z (Fin.natAdd _ i))
    funext i; refine Fin.addCases (fun i => ?_) (fun i => ?_) i <;> simp
  have hH : M.IsHermitian := (Matrix.IsHermitian.fromBlocks m₁ (by simp) m₂).submatrix _
  have hp : ∀ z : Fin (g₁ + g₂) → ℂ, z ≠ 0 → 0 < (hermForm M z z).re := fun z hz => by
    rw [hM, Complex.add_re]
    by_cases a : (fun i => z (Fin.castAdd g₂ i)) = 0 <;> by_cases b : (fun i => z (Fin.natAdd g₁ i)) = 0
    · exact absurd (funext fun i => Fin.addCases (fun i => congrFun a i) (fun i => congrFun b i) i) hz
    · simpa [a, hermForm] using p₂ _ b
    · simpa [b, hermForm] using p₁ _ a
    · exact add_pos (p₁ _ a) (p₂ _ b)
  have he : ∀ x y, (hermForm M (Q x) (Q y)).im = EF x y := fun x y => by
    simp [hM, hQ, hEF, e₁, e₂]
  have hb : Function.Bijective EF := by
    refine ⟨(injective_iff_map_eq_zero EF).2 fun x h => Prod.ext (D₁.unimod.1 (LinearMap.ext fun y => ?_))
      (D₂.unimod.1 (LinearMap.ext fun y => ?_)), fun φ => ?_⟩
    · simpa [hEF] using LinearMap.congr_fun h (y, 0)
    · simpa [hEF] using LinearMap.congr_fun h (0, y)
    · obtain ⟨a, ha⟩ := D₁.unimod.2 (φ ∘ₗ LinearMap.inl ℤ _ _)
      obtain ⟨b, hb⟩ := D₂.unimod.2 (φ ∘ₗ LinearMap.inr ℤ _ _)
      refine ⟨(a, b), LinearMap.ext fun y => ?_⟩
      rw [hEF, ha, hb]
      simp [← map_add]
  obtain ⟨D, e, hp', hq', hD⟩ := PeriodDatum.exists_datum E H _ EF _ _ _ _ Q M hty hb
    (fun a x y => by simp [hEF, D₁.adj, D₂.adj]) hl hi hd hs hH hp he
  have hr : Set.range (Q.comp e.toLinearMap.toAddMonoidHom) = Set.range Q := e.surjective.range_comp Q
  refine ⟨D, e, Q.comp e.toLinearMap.toAddMonoidHom, hp', hq', hD, by rw [hp', hq']; exact hty,
    ⟨fun a x i => by simpa using hl a (e x) i, hi.comp e.injective, ?_, by rw [hr, hs], M, hH, hp,
      fun x y => by rw [hD]; exact he _ _⟩, fun _ => rfl⟩
  rwa [show (Q.comp e.toLinearMap.toAddMonoidHom).range = Q.range from SetLike.coe_injective hr]

theorem exists_cmLat_mixed (D₀ : Datum H) (hp : D₀.p = 1) (hq : D₀.q = 0) :
    ∃ (D : Datum H) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (Pe : D.La →+ (Fin g → ℂ)) (hP : IsPeriod D ty Pe)
      (Z : CMLat hP 1 1), D.p = 1 ∧ D.q = 1 ∧ IsTypeFn H 1 1 ty ∧ ∀ j, Function.Injective (Z.f j) ∧ Z.hh j = 1 := by
  obtain ⟨g₁, t₁, P₁, y₁, h₁⟩ := exists_type_period D₀
  obtain ⟨g₂, t₂, P₂, y₂, h₂⟩ := exists_type_period (oppDatum D₀)
  obtain ⟨D, e, P, a, b, hE, hy, hP, hv⟩ := exists_sum D₀ (oppDatum D₀) h₁ h₂ y₁ y₂
  simp only [oppDatum_p, oppDatum_q, hp, hq] at a b y₁ y₂
  let f₁ : D₀.La →ₗ[𝓞 E] D.La := e.symm.toLinearMap ∘ₗ LinearMap.inl _ _ _
  let f₂ : (oppDatum D₀).La →ₗ[𝓞 E] D.La := e.symm.toLinearMap ∘ₗ LinearMap.inr _ _ _
  have k₁ : ∀ x, e (f₁ x) = (x, 0) := fun x => by simp [f₁]
  have k₂ : ∀ x, e (f₂ x) = (0, x) := fun x => by simp [f₂]
  have u₁ : ∀ x, f₁ x ∈ PureType.lat hP H.rt0 := fun x i => Fin.addCases (fun i hi => by
    have : P₁ x i = 0 := (CMLat.ofPositive hp hq h₁ y₁).pure (.inl 0) x i (by simpa using hi)
    rw [hv, k₁]; simpa using this) (fun i _ => by rw [hv, k₁]; simp) i
  have u₂ : ∀ x, f₂ x ∈ PureType.lat hP (-H.rt0) := fun x i => Fin.addCases (fun i _ => by rw [hv, k₂]; simp)
    (fun i hi => by
      have : P₂ x i = 0 := (CMLat.ofNegative (D := oppDatum D₀) hq hp h₂ y₂).pure (.inr 0) x i (by simpa using hi)
      rw [hv, k₂]; simpa using this) i
  have v₁ : ∀ x y, D.EF (f₁ x) (f₁ y) = D₀.EF ((1 : 𝓞 E) • x) y := fun x y => by rw [hE, k₁, k₁]; simp
  have v₂ : ∀ x y, D.EF (f₂ x) (f₂ y) = (oppDatum D₀).EF ((1 : 𝓞 E) • x) y := fun x y => by rw [hE, k₂, k₂]; simp
  have w : ∀ x, x = f₁ (e x).1 + f₂ (e x).2 := fun x => e.injective (by rw [map_add, k₁, k₂]; simp)
  let Z : CMLat hP 1 1 :=
    { D₁ := fun b => match b with
        | true => D₀
        | false => oppDatum D₀
      sigP := ⟨hp, hq⟩
      sigM := ⟨hq, hp⟩
      f := fun j => match j with
        | .inl _ => f₁
        | .inr _ => f₂
      pure := fun j x => match j, x with
        | .inl _, x => u₁ x
        | .inr _, x => u₂ x
      hh := fun _ => 1
      form := fun j x y => match j, x, y with
        | .inl _, x, y => v₁ x y
        | .inr _, x, y => v₂ x y
      span := ⟨1, one_pos, fun x => ⟨fun j => match j with
        | .inl _ => (e x).1
        | .inr _ => (e x).2, by
          rw [one_smul, Fintype.sum_sum_type, Fin.sum_univ_one, Fin.sum_univ_one]
          exact w x⟩⟩ }
  exact ⟨D, _, _, P, hP, Z, a, b, by rw [a, b] at hy; exact hy,
    fun j => ⟨Z.f_injective (by rw [a, b]) j, rfl⟩⟩

theorem exists_cmLat_mixed_cyclotomic :
    ∃ (D : Datum CyclotomicTwentyEight.host) (g : ℕ) (ty : Fin g → (CyclotomicTwentyEight.CyclotomicFieldTwentyEight →+* ℂ)) (Pe : D.La →+ (Fin g → ℂ))
      (hP : IsPeriod D ty Pe) (Z : CMLat hP 1 1), D.p = 1 ∧ D.q = 1 ∧ IsTypeFn CyclotomicTwentyEight.host 1 1 ty ∧
      ∀ j, Function.Injective (Z.f j) ∧ Z.hh j = 1 := by
  obtain ⟨D, hp, hq⟩ := CyclotomicTwentyEight.exists_datum
  exact exists_cmLat_mixed D hp hq

theorem isFam_of_isTen {R : Type} [CommRing R] {ω : R} {C : Ell H R ω} {D : Datum H} {h : D.La → D.La → OK H}
    {T : PAT H (AlgebraicGeometry.Spec (CommRingCat.of R))} (t : IsTen C D h T) : IsFam C T h ⊤ fun a => t.ten.tmul a.1 :=
  ⟨fun a => t.ten.isLinearHom_tmul a.1, fun a b => t.ten.tmul_add a.1 b.1, fun s a => t.lin s a.1,
    fun a b => t.lam a.1 b.1⟩

theorem isEmpty_cmLat_zero {D : Datum H} {g : ℕ} {ty : Fin g → (E →+* ℂ)} {Pe : D.La →+ (Fin g → ℂ)}
    (hP : IsPeriod D ty Pe) [Nontrivial D.La] : IsEmpty (CMLat hP 0 0) := by
  refine ⟨fun Z => ?_⟩
  obtain ⟨n, hn, hs⟩ := Z.span
  obtain ⟨a, ha⟩ := exists_ne (0 : D.La)
  obtain ⟨x, hx⟩ := hs a
  have e : n • Pe a = 0 := by rw [← map_nsmul, hx]; simp
  exact ha (hP.2.1 (((smul_eq_zero.1 e).resolve_left hn.ne').trans (map_zero Pe).symm))

end Mixed

end GlobalTheory.CM.LatModel
