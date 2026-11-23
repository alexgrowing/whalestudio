import Mathlib
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.ToMatrixTrFormBaseChange
import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.PowObjGeometricallyConnected
import Development.AbelianVarietyTheory.Statements.PrincipalLattices.LogHermFormOfUnitDiscriminant
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ReEqZeroAndImSq
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Serre
open scoped CategoryTheory.Obj UpperHalfPlane TensorProduct

noncomputable section

namespace GlobalTheory.PrincipalDatum

open GlobalTheory.HostModel

variable {E : Type} [Field E] [NumberField E]

omit [NumberField E] in
theorem coe_add' (a b : 𝓞 E) : ((a + b : 𝓞 E) : E) = a + b := rfl

omit [NumberField E] in
theorem coe_mul' (a b : 𝓞 E) : ((a * b : 𝓞 E) : E) = a * b := rfl

theorem exists_clear (𝔞 : Submodule (𝓞 E) E) (h : 𝔞.FG) :
    ∃ N : ℤ, N ≠ 0 ∧ ∃ ψ : 𝔞 →ₗ[𝓞 E] 𝓞 E, ∀ x, (ψ x : E) = N * (x : E) := by
  obtain ⟨a, ⟨N, hN, rfl⟩, ha⟩ :=
    FractionalIdeal.isFractional_of_fg (S := Algebra.algebraMapSubmonoid (𝓞 E) (nonZeroDivisors ℤ)) h
  choose f hf using ha
  have hf' : ∀ x : 𝔞, ((f x x.2 : 𝓞 E) : E) = N * (x : E) := fun x => by
    have := hf x x.2
    rw [Algebra.smul_def] at this
    simpa using this
  refine ⟨N, nonZeroDivisors.ne_zero hN, ⟨⟨fun x => f x x.2, fun x y => ?_⟩, fun c x => ?_⟩, hf'⟩
  · apply RingOfIntegers.ext
    rw [coe_add', hf', hf', hf', Submodule.coe_add, mul_add]
  · apply RingOfIntegers.ext
    simp only [RingHom.id_apply, smul_eq_mul]
    rw [coe_mul', hf', hf', Submodule.coe_smul, Algebra.smul_def]
    simp only [RingOfIntegers.coe_eq_algebraMap]
    ring

def act (M : Type) [AddCommGroup M] [Module (𝓞 E) M] (a : 𝓞 E) : ℝ ⊗[ℤ] M →ₗ[ℝ] ℝ ⊗[ℤ] M :=
  (DistribSMul.toLinearMap ℤ M a).baseChange ℝ

section Act

variable {M : Type} [AddCommGroup M] [Module (𝓞 E) M]

omit [NumberField E] in
@[simp] theorem act_tmul (a : 𝓞 E) (r : ℝ) (x : M) : act M a (r ⊗ₜ x) = r ⊗ₜ (a • x) := rfl

omit [NumberField E] in
theorem act_act (a b : 𝓞 E) (v : ℝ ⊗[ℤ] M) : act M a (act M b v) = act M (a * b) v := by
  induction v using TensorProduct.induction_on with
  | zero => simp
  | add v w h h' => simp only [map_add, h, h']
  | tmul r x => simp [mul_smul]

omit [NumberField E] in
theorem act_natCast (n : ℕ) (v : ℝ ⊗[ℤ] M) : act M (n : 𝓞 E) v = (n : ℝ) • v := by
  induction v using TensorProduct.induction_on with
  | zero => simp
  | add v w h h' => simp only [map_add, h, h', smul_add]
  | tmul r x => rw [act_tmul, Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul, TensorProduct.tmul_smul]

omit [NumberField E] in
theorem act_neg (a : 𝓞 E) (v : ℝ ⊗[ℤ] M) : act M (-a) v = -act M a v := by
  induction v using TensorProduct.induction_on with
  | zero => simp
  | add v w h h' => simp only [map_add, h, h', neg_add]
  | tmul r x => simp [TensorProduct.tmul_neg]

omit [NumberField E] in
theorem eq_act (a : 𝓞 E) (A : ℝ ⊗[ℤ] M →ₗ[ℝ] ℝ ⊗[ℤ] M) (hA : ∀ x, A (1 ⊗ₜ x) = 1 ⊗ₜ (a • x)) :
    A = act M a := by
  ext x
  exact hA x

theorem trace_act (ψ : M →ₗ[𝓞 E] 𝓞 E) (hψ : Function.Injective ψ)
    (hr : Module.finrank ℤ M = Module.finrank ℤ (𝓞 E)) (a : 𝓞 E) :
    LinearMap.trace ℝ _ (act M a) = (Algebra.trace ℤ (𝓞 E) a : ℤ) := by
  haveI : Module.Finite ℤ M := Module.Finite.of_injective (ψ.restrictScalars ℤ) hψ
  haveI : Module.IsTorsionFree ℤ M := Function.Injective.moduleIsTorsionFree (ψ.restrictScalars ℤ) hψ (by simp)
  have hi : Function.Injective ((ψ.restrictScalars ℤ).baseChange ℝ) :=
    Module.Flat.lTensor_preserves_injective_linearMap _ hψ
  let e := LinearMap.linearEquivOfInjective _ hi (by rw [Module.finrank_baseChange, Module.finrank_baseChange, hr])
  have h : act M a = e.symm.conj ((Algebra.lmul ℤ (𝓞 E) a).baseChange ℝ) := by
    ext x
    apply e.injective
    simp [e, LinearEquiv.conj_apply]
  rw [h, LinearMap.trace_conj', LinearMap.trace_baseChange]
  rfl

end Act

variable [IsCMField E]

theorem principal_root_re_zero_im_sq (H : Host E) : H.rt0.re = 0 ∧ H.rt0.im ^ 2 = H.d := by
  first
  | exact @_root_.GlobalTheory.SquareEqNegReIm.re_eq_zero_and_im_sq
  | exact _root_.GlobalTheory.SquareEqNegReIm.re_eq_zero_and_im_sq
  | (apply _root_.GlobalTheory.SquareEqNegReIm.re_eq_zero_and_im_sq <;> assumption)
  | (intros; apply _root_.GlobalTheory.SquareEqNegReIm.re_eq_zero_and_im_sq <;> assumption)
  | (intros; apply @_root_.GlobalTheory.SquareEqNegReIm.re_eq_zero_and_im_sq <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.SquareEqNegReIm.re_eq_zero_and_im_sq ..)

theorem exists_complexStructure (H : Host E) {M : Type} [AddCommGroup M] [Module (𝓞 E) M]
    (ψ : M →ₗ[𝓞 E] 𝓞 E) (hψ : Function.Injective ψ) (hr : Module.finrank ℤ M = Module.finrank ℤ (𝓞 E))
    (EF : LinearMap.BilinForm ℤ M) (adj : ∀ (a : 𝓞 E) x y, EF (a • x) y = EF x (H.bar a • y))
    (c : ℤ) (hc : 0 < (c : ℝ) * H.rt0.im) (hEF : ∀ x y, c * EF (H.rt • x) y = trForm H (ψ x) (ψ y)) :
    ∃ J : ℝ ⊗[ℤ] M →ₗ[ℝ] ℝ ⊗[ℤ] M, (∀ x, J (J x) = -x) ∧
    (∀ x y, EF.baseChange ℝ (J x) (J y) = EF.baseChange ℝ x y) ∧
    (∀ x, x ≠ 0 → 0 < EF.baseChange ℝ (J x) x) ∧
    ∀ (a : 𝓞 E) (A : ℝ ⊗[ℤ] M →ₗ[ℝ] ℝ ⊗[ℤ] M) (t : ℂ), (∀ x : M, A (1 ⊗ₜ x) = 1 ⊗ₜ (a • x)) →
      t = ∑ τ ∈ Finset.univ.filter (fun τ : E →+* ℂ => τ (H.rt : E) = H.rt0),
        (((1 : ℕ) : ℂ) * τ (a : E) + ((0 : ℕ) : ℂ) * starRingEnd ℂ (τ (a : E))) →
      J ∘ₗ A = A ∘ₗ J ∧ LinearMap.trace ℝ _ A = 2 * t.re ∧ LinearMap.trace ℝ _ (J ∘ₗ A) = -2 * t.im := by
  obtain ⟨hre, him⟩ := principal_root_re_zero_im_sq H
  set s := H.rt0.im with hs
  have hs0 : s ≠ 0 := fun h => by simp [h] at hc
  have hRR : ∀ v, act M H.rt (act M H.rt v) = -(s ^ 2 • v) := fun v => by
    rw [act_act, ← pow_two, H.rt_sq, act_neg, act_natCast, him]
  have hadj : ∀ (a : 𝓞 E) v w, EF.baseChange ℝ (act M a v) w = EF.baseChange ℝ v (act M (H.bar a) w) := by
    intro a v w
    induction v using TensorProduct.induction_on with
    | zero => simp
    | add v v' h h' => simp only [map_add, LinearMap.add_apply, h, h']
    | tmul r x =>
      induction w using TensorProduct.induction_on with
      | zero => simp
      | add w w' h h' => simp only [map_add, h, h']
      | tmul r' y => simp [adj]
  have hpos : ∀ v w, c * EF.baseChange ℝ (act M H.rt v) w = (trForm H).baseChange ℝ
      ((ψ.restrictScalars ℤ).baseChange ℝ v) ((ψ.restrictScalars ℤ).baseChange ℝ w) := by
    intro v w
    induction v using TensorProduct.induction_on with
    | zero => simp
    | add v v' h h' => simp only [map_add, LinearMap.add_apply, mul_add, h, h']
    | tmul r x =>
      induction w using TensorProduct.induction_on with
      | zero => simp
      | add w w' h h' => simp only [map_add, mul_add, h, h']
      | tmul r' y => simp [← hEF, _root_.mul_assoc]
  refine ⟨s⁻¹ • act M H.rt, fun x => ?_, fun x y => ?_, fun x hx => ?_, fun a A t hA ht => ?_⟩
  · simp only [LinearMap.smul_apply, map_smul, hRR, smul_neg, smul_smul]
    rw [show s⁻¹ * (s⁻¹ * s ^ 2) = 1 by field_simp, one_smul]
  · simp only [LinearMap.smul_apply, map_smul, hadj, bar_rt, act_neg, hRR, neg_neg, smul_eq_mul]
    field_simp
  · have hi : Function.Injective ((ψ.restrictScalars ℤ).baseChange ℝ) :=
      Module.Flat.lTensor_preserves_injective_linearMap _ hψ
    have h := trForm_baseChange_pos H ((map_ne_zero_iff _ hi).2 hx)
    rw [← hpos] at h
    simp only [LinearMap.smul_apply, map_smul, smul_eq_mul]
    have h2 := div_pos h hc
    have hc0 : (c : ℝ) ≠ 0 := left_ne_zero_of_mul hc.ne'
    rw [mul_div_mul_left _ _ hc0] at h2
    rwa [inv_mul_eq_div]
  · obtain rfl := eq_act a A hA
    simp only [Nat.cast_one, _root_.one_mul, Nat.cast_zero, zero_mul, add_zero] at ht
    refine ⟨?_, ?_, ?_⟩
    · refine LinearMap.ext fun v => ?_
      simp only [LinearMap.comp_apply, LinearMap.smul_apply, map_smul, act_act, _root_.mul_comm]
    · have h := congrArg Complex.re (sum_add_conj_eq_trace H a)
      rw [Finset.sum_add_distrib, ← map_sum, ← ht] at h
      rw [trace_act ψ hψ hr]
      simp at h
      linarith
    · have h1 : (s⁻¹ • act M H.rt) ∘ₗ act M a = s⁻¹ • act M (H.rt * a) := by
        refine LinearMap.ext fun v => ?_
        simp only [LinearMap.comp_apply, LinearMap.smul_apply, act_act]
      have h := congrArg Complex.re (sum_add_conj_eq_trace H (H.rt * a))
      have h2 : ∑ τ ∈ Finset.univ.filter (fun τ : E →+* ℂ => τ (H.rt : E) = H.rt0), τ ((H.rt * a : 𝓞 E) : E) =
          H.rt0 * t := by
        rw [ht, Finset.mul_sum]
        refine Finset.sum_congr rfl fun τ hτ => ?_
        rw [coe_mul', map_mul, (Finset.mem_filter.1 hτ).2]
      rw [Finset.sum_add_distrib, ← map_sum, h2] at h
      rw [h1, map_smul, trace_act ψ hψ hr, smul_eq_mul]
      simp [hre, ← hs] at h
      rw [← h]
      field_simp
      ring

theorem exists_datum : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (𝔞 : Submodule (𝓞 E) E), 𝔞.FG → 𝔞 ≠ ⊥ → (∀ y : E, y ∈ 𝔞 ↔ ∀ x ∈ 𝔞, ∃ n : ℤ, Algebra.trace ℚ E (x * IsCMField.complexConj E y / (H.rt : E)) = n) → ∃ (D : Datum H) (e : D.La ≃ₗ[𝓞 E] 𝔞), D.p = 1 ∧ D.q = 0 ∧ ∀ x y, ((D.EF x y : ℚ) : ℝ) * H.rt0.im = ((Algebra.trace ℚ E ((e x : E) * IsCMField.complexConj E (e y : E) / (H.rt : E)) : ℚ) : ℝ) * √(H.d) := by
  intro E _ _ _ H 𝔞 hfg hne hdual
  obtain ⟨hre, him⟩ := principal_root_re_zero_im_sq H
  obtain ⟨N, hN, ψ, hψ⟩ := exists_clear 𝔞 hfg
  have hNE : (N : E) ≠ 0 := by exact_mod_cast hN
  have hinj : Function.Injective ψ := fun x y h => by
    apply Subtype.ext
    apply mul_left_cancel₀ hNE
    rw [← hψ, ← hψ, h]
  have hrt : (H.rt : E) ≠ 0 := RingOfIntegers.coe_ne_zero_iff.2 (rt_ne_zero H)
  have hcrt : IsCMField.complexConj E (H.rt : E) = -(H.rt : E) := by
    rw [← H.bar_eq, bar_rt]; rfl
  obtain ⟨ε, hε, hεs⟩ : ∃ ε : ℤ, ε * ε = 1 ∧ (ε : ℝ) * H.rt0.im = √(H.d) := by
    rw [← him, Real.sqrt_sq_eq_abs]
    rcases abs_cases H.rt0.im with h | h
    · exact ⟨1, rfl, by simp [h.1]⟩
    · exact ⟨-1, rfl, by simp [h.1]⟩
  have hεq : (ε : ℚ) * ε = 1 := by exact_mod_cast hε
  choose f hf using fun x y : 𝔞 => (hdual y).1 y.2 x x.2
  have key : ∀ x y : 𝔞, ((ε * f x y : ℤ) : ℚ) =
      ε * Algebra.trace ℚ E ((x : E) * IsCMField.complexConj E (y : E) / (H.rt : E)) := fun x y => by
    rw [hf, Int.cast_mul]
  let EF : LinearMap.BilinForm ℤ 𝔞 := LinearMap.mk₂ ℤ (fun x y => ε * f x y)
    (fun x x' y => by
      apply Int.cast_injective (α := ℚ)
      rw [Int.cast_add, key, key, key, Submodule.coe_add, add_mul, add_div, map_add, mul_add])
    (fun c x y => by
      apply Int.cast_injective (α := ℚ)
      rw [smul_eq_mul, Int.cast_mul c, key, key, mul_left_comm (c : ℚ), ← zsmul_eq_mul _ c, ← map_zsmul]
      simp [_root_.mul_assoc, mul_div_assoc])
    (fun x y y' => by
      apply Int.cast_injective (α := ℚ)
      rw [Int.cast_add, key, key, key, Submodule.coe_add, map_add, mul_add, add_div, map_add, mul_add])
    (fun c x y => by
      apply Int.cast_injective (α := ℚ)
      rw [smul_eq_mul, Int.cast_mul c, key, key, mul_left_comm (c : ℚ), ← zsmul_eq_mul _ c, ← map_zsmul]
      simp [mul_left_comm, mul_div_assoc])
  have hEF : ∀ x y : 𝔞, (EF x y : ℚ) =
      ε * Algebra.trace ℚ E ((x : E) * IsCMField.complexConj E (y : E) / (H.rt : E)) := key
  have hconj : ∀ z : E, Algebra.trace ℚ E (IsCMField.complexConj E z) = Algebra.trace ℚ E z := fun z =>
    Algebra.trace_eq_of_algEquiv ((IsCMField.complexConj E).restrictScalars ℚ) z
  have hskew : ∀ x y, EF x y = -EF y x := fun x y => by
    apply Int.cast_injective (α := ℚ)
    rw [Int.cast_neg, hEF, hEF, ← hconj, map_div₀, map_mul, IsCMField.complexConj_apply_apply, hcrt, div_neg,
      map_neg, mul_neg, _root_.mul_comm (y : E)]
  have hadj : ∀ (a : 𝓞 E) x y, EF (a • x) y = EF x (H.bar a • y) := fun a x y => by
    apply Int.cast_injective (α := ℚ)
    rw [hEF, hEF, Submodule.coe_smul, Submodule.coe_smul, Algebra.smul_def, Algebra.smul_def, map_mul,
      ← RingOfIntegers.coe_eq_algebraMap, ← RingOfIntegers.coe_eq_algebraMap, H.bar_eq,
      IsCMField.complexConj_apply_apply, mul_left_comm (x : E), _root_.mul_assoc]
  have htr : ∀ x y, ε * N ^ 2 * EF (H.rt • x) y = trForm H (ψ x) (ψ y) := fun x y => by
    apply Int.cast_injective (α := ℚ)
    rw [trForm_apply', Algebra.coe_trace_int, Int.cast_mul, hEF, coe_mul', H.bar_eq, hψ, hψ,
      Submodule.coe_smul, Algebra.smul_def, ← RingOfIntegers.coe_eq_algebraMap, map_mul (IsCMField.complexConj E), map_intCast,
      show (N : E) * x * (N * IsCMField.complexConj E y) =
        (N ^ 2 : ℤ) • ((H.rt : E) * x * IsCMField.complexConj E y / H.rt) by
          rw [zsmul_eq_mul]; push_cast; field_simp, map_zsmul, zsmul_eq_mul]
    push_cast
    linear_combination (N : ℚ) ^ 2 *
      Algebra.trace ℚ E ((H.rt : E) * x * IsCMField.complexConj E y / H.rt) * hεq
  have hbij : Function.Bijective EF := by
    constructor
    · refine (injective_iff_map_eq_zero _).2 fun x hx => ?_
      by_contra h
      have h1 := trForm_pos H ((map_ne_zero_iff _ hinj).2 h)
      rw [← htr, hadj, hx] at h1
      simp at h1
    · intro φ
      obtain ⟨g, hg⟩ := (Module.Baer.of_divisible ℚ).extension_property_addMonoidHom
        𝔞.subtype.toAddMonoidHom 𝔞.subtype_injective ((Int.castAddHom ℚ).comp φ.toAddMonoidHom)
      have hg' : ∀ x : 𝔞, g x = φ x := fun x => DFunLike.congr_fun hg x
      obtain ⟨z, hz⟩ := ((Algebra.traceForm ℚ E).toDual (traceForm_nondegenerate ℚ E)).surjective
        g.toRatLinearMap
      have hz' : ∀ x : E, Algebra.trace ℚ E (x * IsCMField.complexConj E (IsCMField.complexConj E (z * H.rt)) /
          (H.rt : E)) = g x := fun x => by
        have := LinearMap.congr_fun hz x
        rw [IsCMField.complexConj_apply_apply, ← _root_.mul_assoc, mul_div_cancel_right₀ _ hrt, _root_.mul_comm]
        exact this
      let y : 𝔞 := ⟨_, (hdual _).2 fun x hx => ⟨φ ⟨x, hx⟩, (hz' x).trans (hg' ⟨x, hx⟩)⟩⟩
      refine ⟨-(ε • y), LinearMap.ext fun x => ?_⟩
      rw [hskew, map_neg, neg_neg, map_zsmul]
      apply Int.cast_injective (α := ℚ)
      rw [smul_eq_mul, Int.cast_mul, hEF, hz', hg', ← _root_.mul_assoc, hεq, _root_.one_mul]
  haveI : Module.Finite (𝓞 E) 𝔞 := Module.Finite.iff_fg.2 hfg
  haveI : Module.Finite ℤ 𝔞 := Module.Finite.of_injective (ψ.restrictScalars ℤ) hinj
  haveI := Module.finitePresentation_of_finite (𝓞 E) 𝔞
  have hr : Module.finrank ℤ 𝔞 = Module.finrank ℤ (𝓞 E) := by
    obtain ⟨x₀, hx₀, h0⟩ := (Submodule.ne_bot_iff _).1 hne
    refine le_antisymm (LinearMap.finrank_le_finrank_of_injective (f := ψ.restrictScalars ℤ) hinj)
      (LinearMap.finrank_le_finrank_of_injective
        (f := (LinearMap.toSpanSingleton (𝓞 E) 𝔞 ⟨x₀, hx₀⟩).restrictScalars ℤ) ?_)
    exact smul_left_injective (𝓞 E) (m := (⟨x₀, hx₀⟩ : 𝔞)) (by simpa using h0)
  have hd : (0 : ℝ) < √(H.d) := Real.sqrt_pos.2 (by exact_mod_cast H.d_prime.pos)
  refine ⟨{ La := 𝔞, fin := inferInstance, proj := Module.Flat.projective_of_finitePresentation, EF := EF,
            alt := fun x => by have := hskew x x; omega,
            unimod := hbij, adj := hadj, p := 1, q := 0,
            rank := by rw [finrank_eq_of_injective ψ hinj hr, Module.finrank_self],
            dom := exists_complexStructure H ψ hinj hr EF hadj (ε * N ^ 2) ?_ htr },
    LinearEquiv.refl _ _, rfl, rfl, fun x y => ?_⟩
  · push_cast
    rw [mul_right_comm, hεs]
    have : (N : ℝ) ≠ 0 := by exact_mod_cast hN
    positivity
  · change ((EF x y : ℚ) : ℝ) * _ = ((Algebra.trace ℚ E (((x : 𝔞) : E) * IsCMField.complexConj E ((y : 𝔞) : E) /
      (H.rt : E)) : ℚ) : ℝ) * _
    have h := hεs.symm
    rw [hEF, h]
    push_cast
    ring

end GlobalTheory.PrincipalDatum
