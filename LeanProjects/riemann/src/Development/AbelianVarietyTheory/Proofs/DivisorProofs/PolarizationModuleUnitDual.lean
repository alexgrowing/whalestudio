import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.PolarisationModuleIndex

noncomputable section

open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.PolarisationModuleIndex

namespace GlobalTheory.PolModLattice

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

def altForm (x y : E) : E := x * bar y - bar x * y

def formSpan (L : Submodule (OF E) E) : Submodule (OF E) E :=
  Submodule.span (OF E) {w | ∃ x ∈ L, ∃ y ∈ L, w = altForm x y}

variable (E) in

def invDiff : Submodule (OF E) E where
  carrier := {v | ∃ w : maximalRealSubfield E, (w : E) = v ∧
    ∀ a : OF E, ∃ n : ℤ, Algebra.trace ℚ (maximalRealSubfield E) (w * (a : maximalRealSubfield E)) = n}
  zero_mem' := ⟨0, by simp, fun a => ⟨0, by simp⟩⟩
  add_mem' := by
    rintro _ _ ⟨w, rfl, hw⟩ ⟨w', rfl, hw'⟩
    refine ⟨w + w', by simp, fun a => ?_⟩
    obtain ⟨m, hm⟩ := hw a
    obtain ⟨n, hn⟩ := hw' a
    exact ⟨m + n, by rw [add_mul, map_add, hm, hn]; push_cast; rfl⟩
  smul_mem' := by
    rintro c _ ⟨w, rfl, hw⟩
    refine ⟨(c : maximalRealSubfield E) * w, ?_, fun a => ?_⟩
    · rw [Algebra.smul_def]; rfl
    · obtain ⟨n, hn⟩ := hw (c * a)
      exact ⟨n, by rw [← hn]; congr 1; push_cast; ring⟩

theorem coe_OF (a : OF E) : (((a : maximalRealSubfield E)) : E) = algebraMap (OF E) E a := rfl

theorem bar_real (w : maximalRealSubfield E) : bar (w : E) = w := IsCMField.complexConj_apply_eq_self E w

theorem real_of_bar {v : E} (h : bar v = v) : ∃ w : maximalRealSubfield E, (w : E) = v :=
  ⟨⟨v, (IsCMField.complexConj_eq_self_iff E v).1 h⟩, rfl⟩

theorem bar_smul (a : OF E) (x : E) : bar (a • x) = a • bar x := by
  rw [Algebra.smul_def, Algebra.smul_def, bar, map_mul, ← bar, ← bar, ← coe_OF, bar_real]

theorem altForm_bar (x y : E) : bar (altForm x y) = - altForm x y := by
  simp only [altForm, bar, map_sub, map_mul, IsCMField.complexConj_apply_apply]; ring

open Classical in
theorem univ_aut : (Finset.univ : Finset (E ≃ₐ[maximalRealSubfield E] E)) = {1, IsCMField.complexConj E} := by
  have hc : Nat.card (E ≃ₐ[maximalRealSubfield E] E) = 2 :=
    (Algebra.IsQuadraticExtension.finrank_eq_two (maximalRealSubfield E) E) ▸ IsGalois.card_aut_eq_finrank _ E
  obtain ⟨τ, hτ, hu⟩ := (Nat.card_eq_two_iff' 1).1 hc
  ext σ
  simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton, true_iff]
  by_cases h : σ = 1
  · exact Or.inl h
  · exact Or.inr (by rw [hu σ h, hu _ (IsCMField.complexConj_ne_one E)])

theorem trace_eq (u : E) (w : maximalRealSubfield E) (hw : (w : E) = u + bar u) :
    Algebra.trace ℚ E u = Algebra.trace ℚ (maximalRealSubfield E) w := by
  rw [← Algebra.trace_trace (S := maximalRealSubfield E)]
  congr 1
  apply FaithfulSMul.algebraMap_injective (maximalRealSubfield E) E
  classical
  rw [trace_eq_sum_automorphisms, univ_aut, Finset.sum_pair (Ne.symm (IsCMField.complexConj_ne_one E))]
  simp only [AlgEquiv.one_apply]
  exact hw.symm

open scoped nonZeroDivisors in
theorem isUnit_invDiff : IsUnit (invDiff E) := by
  let K := maximalRealSubfield E
  let f : K →ₐ[OF E] E := IsScalarTower.toAlgHom (OF E) K E
  haveI : NeZero (1 : FractionalIdeal (OF E)⁰ K) := ⟨one_ne_zero⟩
  let 𝔡 : FractionalIdeal (OF E)⁰ K := FractionalIdeal.dual ℤ ℚ 1
  have h0 : 𝔡 ≠ 0 := FractionalIdeal.dual_ne_zero ℤ ℚ one_ne_zero
  have hmul : (𝔡 : Submodule (OF E) K) * ((𝔡⁻¹ : FractionalIdeal (OF E)⁰ K) : Submodule (OF E) K) = 1 := by
    rw [← FractionalIdeal.coe_mul, mul_inv_cancel₀ h0, FractionalIdeal.coe_one]
  have heq : invDiff E = (𝔡 : Submodule (OF E) K).map f.toLinearMap := by
    ext v
    constructor
    · rintro ⟨w, rfl, hw⟩
      refine ⟨w, ?_, rfl⟩
      show w ∈ 𝔡
      rw [FractionalIdeal.mem_dual one_ne_zero]
      intro a ha
      obtain ⟨b, rfl⟩ := (FractionalIdeal.mem_one_iff _).1 ha
      obtain ⟨n, hn⟩ := hw b
      exact ⟨n, by rw [Algebra.traceForm_apply]; simpa using hn.symm⟩
    · rintro ⟨w, hw, rfl⟩
      refine ⟨w, rfl, fun a => ?_⟩
      have hw' : w ∈ 𝔡 := hw
      rw [FractionalIdeal.mem_dual one_ne_zero] at hw'
      obtain ⟨n, hn⟩ := hw' (algebraMap (OF E) K a) ((FractionalIdeal.mem_one_iff _).2 ⟨a, rfl⟩)
      exact ⟨n, by rw [Algebra.traceForm_apply] at hn; simpa using hn.symm⟩
  refine ⟨⟨invDiff E, ((𝔡⁻¹ : FractionalIdeal (OF E)⁰ K) : Submodule (OF E) K).map f.toLinearMap, ?_, ?_⟩, rfl⟩
  · rw [heq, ← Submodule.map_mul, hmul, Submodule.map_one]
  · rw [heq, ← Submodule.map_mul, mul_comm, hmul, Submodule.map_one]

def imagPart (E : Type) [Field E] [NumberField E] [IsCMField E] : Submodule (OF E) E where
  carrier := {j | bar j = -j}
  zero_mem' := by simp [bar]
  add_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq, bar, map_add] at ha hb ⊢
    rw [ha, hb]; ring
  smul_mem' := by
    intro c a ha
    simp only [Set.mem_setOf_eq] at ha ⊢
    rw [bar_smul, ha, smul_neg]

theorem formSpan_le_imag (L : Submodule (OF E) E) : formSpan L ≤ imagPart E := by
  rw [formSpan, Submodule.span_le]
  rintro _ ⟨x, -, y, -, rfl⟩
  exact altForm_bar x y

theorem exists_imag_int : ∃ δ : 𝓞 E, (δ : E) ≠ 0 ∧ bar (δ : E) = -(δ : E) := by
  obtain ⟨x, hx⟩ : ∃ x : E, bar x ≠ x := by
    by_contra h
    push_neg at h
    exact IsCMField.complexConj_ne_one E (AlgEquiv.ext fun x => h x)
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 E) x
  have key : ∃ c : 𝓞 E, bar (c : E) ≠ c := by
    by_contra h
    push_neg at h
    apply hx
    simp only [bar, map_div₀] at h ⊢
    rw [h a, h b]
  obtain ⟨c, hc⟩ := key
  refine ⟨c - IsCMField.ringOfIntegersComplexConj E c, ?_, ?_⟩
  · simp only [map_sub, IsCMField.coe_ringOfIntegersComplexConj]
    exact sub_ne_zero.2 (Ne.symm hc)
  · simp only [map_sub, IsCMField.coe_ringOfIntegersComplexConj, bar, IsCMField.complexConj_apply_apply]
    ring

theorem isIntegral_formSpan (L : Submodule (OF E) E) (N : ℕ) (hN : ∀ x ∈ L, IsIntegral ℤ ((N : E) * x)) :
    ∀ w ∈ formSpan L, IsIntegral ℤ ((N : E) ^ 2 * w) := by
  intro w hw
  induction hw using Submodule.span_induction with
  | mem w hw =>
    obtain ⟨x, hx, y, hy, rfl⟩ := hw
    have hb : ∀ t : E, IsIntegral ℤ t → IsIntegral ℤ (bar t) := fun t ht =>
      ht.map ((IsCMField.complexConj E).toAlgHom.restrictScalars ℤ)
    have e : (N : E) ^ 2 * altForm x y = (N * x) * bar (N * y) - bar (N * x) * (N * y) := by
      simp only [altForm, bar, map_mul, map_natCast]; ring
    rw [e]
    exact ((hN x hx).mul (hb _ (hN y hy))).sub ((hb _ (hN x hx)).mul (hN y hy))
  | zero => simpa using isIntegral_zero
  | add a b _ _ ha hb => rw [mul_add]; exact ha.add hb
  | smul c a _ ha =>
    rw [Algebra.smul_def, mul_left_comm]
    exact (c.2.map (IsScalarTower.toAlgHom ℤ (maximalRealSubfield E) E)).mul ha

open scoped nonZeroDivisors in
theorem exists_inv (L : Submodule (OF E) E)
    (hL : ∃ N : ℕ, 0 < N ∧ (∀ x : 𝓞 E, (N : E) * algebraMap (𝓞 E) E x ∈ L) ∧ ∀ x ∈ L, IsIntegral ℤ ((N : E) * x)) :
    ∃ J : Submodule (OF E) E, formSpan L * J = 1 ∧ ∀ j ∈ J, bar j = -j := by
  obtain ⟨N, hN0, hNL, hNi⟩ := hL
  obtain ⟨δ, hδ0, hδb⟩ := exists_imag_int (E := E)
  let K := maximalRealSubfield E
  let f : K →ₐ[OF E] E := IsScalarTower.toAlgHom (OF E) K E
  let g : K →ₗ[OF E] E := (LinearMap.mulRight (OF E) (δ : E)).comp f.toLinearMap
  let IK : Submodule (OF E) K := (formSpan L).comap g
  have hg : ∀ a : K, g a = (a : E) * δ := fun a => rfl

  have hsplit : formSpan L = IK.map f.toLinearMap * Submodule.span (OF E) {(δ : E)} := by
    apply le_antisymm
    · intro w hw
      have hwi : bar w = -w := formSpan_le_imag L hw
      have hr : bar (w / δ) = w / δ := by
        simp only [bar, map_div₀] at hwi hδb ⊢
        rw [hwi, hδb, neg_div_neg_eq]
      obtain ⟨a, ha⟩ := real_of_bar hr
      have haI : a ∈ IK := by
        show g a ∈ formSpan L
        rw [hg, ha, div_mul_cancel₀ _ hδ0]
        exact hw
      have : w = f a * δ := by
        show w = (a : E) * δ
        rw [ha, div_mul_cancel₀ _ hδ0]
      rw [this]
      exact Submodule.mul_mem_mul ⟨a, haI, rfl⟩ (Submodule.mem_span_singleton_self _)
    · refine Submodule.mul_le.2 fun u hu s hs => ?_
      obtain ⟨a, ha, rfl⟩ := hu
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hs
      rw [mul_smul_comm]
      exact (formSpan L).smul_mem c ha

  have hδ2 : bar ((δ : E) * δ) = (δ : E) * δ := by
    simp only [bar, map_mul] at hδb ⊢; rw [hδb]; ring
  obtain ⟨d, hd⟩ : ∃ d : OF E, algebraMap (OF E) E d = (δ : E) * δ := by
    obtain ⟨d, hd⟩ := (IsCMField.RingOfIntegers.complexConj_eq_self_iff E (δ * δ)).1 (by
      push_cast; exact hδ2)
    exact ⟨d, by rw [hd]; push_cast; rfl⟩
  have hd0 : d ≠ 0 := by
    rintro rfl
    rw [map_zero] at hd
    exact mul_self_ne_zero.2 hδ0 hd.symm
  have hfrac : IsFractional (OF E)⁰ IK := by
    refine ⟨(N : OF E) ^ 2 * d, mem_nonZeroDivisors_of_ne_zero (mul_ne_zero (pow_ne_zero _ (by exact_mod_cast hN0.ne')) hd0), ?_⟩
    intro a ha
    have h1 := isIntegral_formSpan L N hNi _ ha
    rw [hg] at h1
    have h2 : IsIntegral ℤ (f (((N : OF E) ^ 2 * d) • a)) := by
      have e : f (((N : OF E) ^ 2 * d) • a) = (N : E) ^ 2 * ((a : E) * δ) * δ := by
        rw [Algebra.smul_def, map_mul, AlgHom.commutes, map_mul, map_pow, map_natCast, hd]
        change (N : E) ^ 2 * (δ * δ) * (a : E) = _
        ring
      rw [e]
      exact h1.mul δ.2
    have h3 : IsIntegral ℤ (((N : OF E) ^ 2 * d) • a) :=
      (isIntegral_algHom_iff (f.restrictScalars ℤ) f.toRingHom.injective).1 h2
    exact ⟨⟨_, h3⟩, rfl⟩
  let 𝔦 : FractionalIdeal (OF E)⁰ K := ⟨IK, hfrac⟩
  have h𝔦 : 𝔦 ≠ 0 := by
    intro h
    have hm : (-(N : K) ^ 2 - (N : K) ^ 2 : K) ∈ IK := by
      show g _ ∈ formSpan L
      have hx := hNL 1
      have hy : (N : E) * (δ : E) ∈ L := hNL δ
      rw [map_one, mul_one] at hx
      have hmem : altForm (N : E) ((N : E) * (δ : E)) ∈ formSpan L := Submodule.subset_span ⟨_, hx, _, hy, rfl⟩
      convert hmem using 1
      rw [hg]
      simp only [altForm, bar, map_mul, map_natCast] at hδb ⊢
      rw [hδb]
      push_cast
      ring
    have : (-(N : K) ^ 2 - (N : K) ^ 2 : K) ∈ (𝔦 : Submodule (OF E) K) := hm
    rw [h, FractionalIdeal.coe_zero, Submodule.mem_bot] at this
    have hN : (N : K) ≠ 0 := by exact_mod_cast hN0.ne'
    rw [show (-(N : K) ^ 2 - (N : K) ^ 2 : K) = -2 * (N : K) ^ 2 by ring] at this
    exact (mul_ne_zero (by norm_num) (pow_ne_zero 2 hN)) this
  have hmul : IK * ((𝔦⁻¹ : FractionalIdeal (OF E)⁰ K) : Submodule (OF E) K) = 1 := by
    rw [show IK = (𝔦 : Submodule (OF E) K) from rfl, ← FractionalIdeal.coe_mul, mul_inv_cancel₀ h𝔦,
      FractionalIdeal.coe_one]
  refine ⟨((𝔦⁻¹ : FractionalIdeal (OF E)⁰ K) : Submodule (OF E) K).map f.toLinearMap *
    Submodule.span (OF E) {(δ : E)⁻¹}, ?_, ?_⟩
  · rw [hsplit, mul_mul_mul_comm, ← Submodule.map_mul, hmul, Submodule.map_one,
      Submodule.span_mul_span, Set.singleton_mul_singleton, mul_inv_cancel₀ hδ0, ← Submodule.one_eq_span, mul_one]
  · intro j hj
    have hle : ((𝔦⁻¹ : FractionalIdeal (OF E)⁰ K) : Submodule (OF E) K).map f.toLinearMap *
        Submodule.span (OF E) {(δ : E)⁻¹} ≤ imagPart E := by
      refine Submodule.mul_le.2 fun u hu s hs => ?_
      obtain ⟨a, -, rfl⟩ := hu
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hs
      show bar _ = -_
      rw [mul_smul_comm, bar_smul]
      simp only [bar, map_mul, map_inv₀] at hδb ⊢
      rw [hδb]
      have : IsCMField.complexConj E (f.toLinearMap a) = f.toLinearMap a := IsCMField.complexConj_apply_eq_self E a
      rw [this, inv_neg, mul_neg, smul_neg]
    exact hle hj

end GlobalTheory.PolModLattice

open GlobalTheory.PolModLattice in

theorem GlobalTheory.PolModLattice.polMod_isUnit_mul_eq_dual : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (L : Submodule (OF E) E),
    (∃ N : ℕ, 0 < N ∧ (∀ x : 𝓞 E, (N : E) * algebraMap (𝓞 E) E x ∈ L) ∧ ∀ x ∈ L, IsIntegral ℤ ((N : E) * x)) →
    IsUnit (polMod L) ∧ polMod L * L = dualLat L := by
  intro E _ _ _ L hL
  obtain ⟨J, hIJ, hJ⟩ := exists_inv L hL
  have hJI : J * formSpan L = 1 := by rw [mul_comm]; exact hIJ
  have hM : polMod L = J * invDiff E := by
    apply le_antisymm
    · intro ξ hξ
      have h1 : Submodule.span (OF E) {ξ} * formSpan L ≤ invDiff E := by
        rw [formSpan, Submodule.span_mul_span, Submodule.span_le]
        rintro _ ⟨a, ha, b, ⟨x, hx, y, hy, rfl⟩, rfl⟩
        rw [Set.mem_singleton_iff.1 ha]
        have hr : bar (ξ * altForm x y) = ξ * altForm x y := by
          rw [bar, map_mul, ← bar, ← bar, altForm_bar, hξ.1]; ring
        obtain ⟨w, hw⟩ := real_of_bar hr
        refine ⟨w, hw, fun c => ?_⟩
        obtain ⟨n, hn⟩ := hξ.2 (c • x) (L.smul_mem c hx) y hy
        refine ⟨n, ?_⟩
        rw [← hn]
        symm
        apply trace_eq
        push_cast
        rw [hw, coe_OF]
        have hb : IsCMField.complexConj E ξ = -ξ := hξ.1
        simp only [altForm, bar, map_mul, IsCMField.complexConj_apply_apply, Algebra.smul_def]
        rw [hb, show IsCMField.complexConj E (algebraMap (OF E) E c) = _ from bar_algebraMap c]
        ring
      have h2 : Submodule.span (OF E) {ξ} ≤ J * invDiff E := calc
        Submodule.span (OF E) {ξ} = Submodule.span (OF E) {ξ} * (formSpan L * J) := by rw [hIJ, mul_one]
        _ = (Submodule.span (OF E) {ξ} * formSpan L) * J := (mul_assoc _ _ _).symm
        _ ≤ invDiff E * J := mul_le_mul_left h1 _
        _ = J * invDiff E := mul_comm _ _
      exact h2 (Submodule.mem_span_singleton_self ξ)
    · refine Submodule.mul_le.2 fun j hj v hv => ?_
      obtain ⟨w, rfl, hw⟩ := hv
      refine ⟨by rw [bar, map_mul, ← bar, ← bar, hJ j hj, bar_real]; ring, fun x hx y hy => ?_⟩
      have hm : j * altForm x y ∈ (1 : Submodule (OF E) E) := hJI ▸ Submodule.mul_mem_mul hj (Submodule.subset_span ⟨x, hx, y, hy, rfl⟩)
      obtain ⟨a, ha⟩ := Submodule.mem_one.1 hm
      obtain ⟨n, hn⟩ := hw a
      refine ⟨n, ?_⟩
      rw [← hn]
      apply trace_eq
      push_cast
      rw [coe_OF, ha]
      have hb : IsCMField.complexConj E j = -j := hJ j hj
      simp only [altForm, bar, map_mul, IsCMField.complexConj_apply_apply]
      rw [hb, show IsCMField.complexConj E (w : E) = w from bar_real w]
      ring
  refine ⟨?_, le_antisymm (polMod_mul_le L) ?_⟩
  · rw [hM]
    exact (show IsUnit J from ⟨⟨J, formSpan L, hJI, hIJ⟩, rfl⟩).mul isUnit_invDiff
  · rw [hM]
    intro z hz
    have h1 : Submodule.span (OF E) {z} * formSpan L ≤ invDiff E * L := by
      rw [formSpan, Submodule.span_mul_span, Submodule.span_le]
      rintro _ ⟨a, ha, b, ⟨x, hx, y, hy, rfl⟩, rfl⟩
      rw [Set.mem_singleton_iff.1 ha]
      have key : ∀ t ∈ L, z * bar t + bar z * t ∈ invDiff E := by
        intro t ht
        have hr : bar (z * bar t + bar z * t) = z * bar t + bar z * t := by
          simp only [bar, map_add, map_mul, IsCMField.complexConj_apply_apply]; ring
        obtain ⟨w, hw⟩ := real_of_bar hr
        refine ⟨w, hw, fun c => ?_⟩
        obtain ⟨n, hn⟩ := hz (c • t) (L.smul_mem c ht)
        refine ⟨n, ?_⟩
        rw [← hn]
        symm
        apply trace_eq
        push_cast
        rw [hw, coe_OF, bar_smul]
        simp only [bar, map_mul, IsCMField.complexConj_apply_apply, Algebra.smul_def]
        rw [show IsCMField.complexConj E (algebraMap (OF E) E c) = _ from bar_algebraMap c]
        ring
      have e : z * altForm x y = (z * bar y + bar z * y) * x - (z * bar x + bar z * x) * y := by
        simp only [altForm]; ring
      show z * altForm x y ∈ _
      rw [e]
      exact sub_mem (Submodule.mul_mem_mul (key y hy) hx) (Submodule.mul_mem_mul (key x hx) hy)
    have h2 : Submodule.span (OF E) {z} ≤ J * invDiff E * L := calc
      Submodule.span (OF E) {z} = Submodule.span (OF E) {z} * (formSpan L * J) := by rw [hIJ, mul_one]
      _ = (Submodule.span (OF E) {z} * formSpan L) * J := (mul_assoc _ _ _).symm
      _ ≤ invDiff E * L * J := mul_le_mul_left h1 _
      _ = J * invDiff E * L := by rw [mul_comm, mul_assoc]
    exact h2 (Submodule.mem_span_singleton_self z)
