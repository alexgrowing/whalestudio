import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsHolFormConst
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.PolarisationModuleIndex
open NumberField GlobalTheory.CMVal GlobalTheory.RealMult

namespace GlobalTheory.PolGen

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem eq_zero_of_trace {F : Type} [Field F] [NumberField F] (D : F)
    (h : ∀ a : 𝓞 F, Algebra.trace ℚ F ((a : F) * D) = 0) : D = 0 := by
  by_contra hD
  have halg : IsAlgebraic ℤ D⁻¹ :=
    (IsFractionRing.isAlgebraic_iff ℤ ℚ F).2 (Algebra.IsAlgebraic.isAlgebraic _)
  obtain ⟨m, hm, hint⟩ := halg.exists_integral_multiple
  have h1 : Algebra.trace ℚ F ((m • D⁻¹) * D) = 0 := h ⟨m • D⁻¹, hint⟩
  have e : (m • D⁻¹) * D = algebraMap ℚ F (m : ℚ) := by
    rw [zsmul_eq_mul, mul_assoc, inv_mul_cancel₀ hD]; simp
  rw [e, Algebra.trace_algebraMap, nsmul_eq_mul] at h1
  have h2 : (Module.finrank ℚ F : ℚ) ≠ 0 := by exact_mod_cast Module.finrank_pos.ne'
  have h3 : (m : ℚ) ≠ 0 := by exact_mod_cast hm
  exact mul_ne_zero h2 h3 h1

omit [IsCMField E] in

theorem trace_coe_mul (k : maximalRealSubfield E) (w : E) :
    Algebra.trace ℚ E ((k : E) * w) =
      Algebra.trace ℚ (maximalRealSubfield E) (k * Algebra.trace (maximalRealSubfield E) E w) := by
  rw [← Algebra.trace_trace (S := maximalRealSubfield E)]
  congr 1
  rw [← smul_eq_mul k, ← map_smul]
  rfl

theorem genAt_polMod : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (L : Submodule (OF E) E) (𝔠 : FracId (maximalRealSubfield E))
    (mu : E) (c1 : maximalRealSubfield E) (Q : E → E → maximalRealSubfield E) (l : ℕ) (c₀ : 𝔠.elt), c1 ≠ 0 →
    IsCMField.complexConj E mu = -mu →
    (∀ (a : OF E), ∀ x ∈ L, ∀ x' ∈ L, Q (algebraMap (OF E) E a * x) x' = (a : maximalRealSubfield E) * Q x x') →
    (∀ x ∈ L, ∀ x' ∈ L, Algebra.trace ℚ E (mu * x * IsCMField.complexConj E x') =
      2 * Algebra.trace ℚ (maximalRealSubfield E) (c1 * Q x x')) →
    (∀ x ∈ L, ∀ x' ∈ L, Q x x' ∈ dualLat 𝔠) →
    (∀ t ∈ dualLat 𝔠, t ∈ Submodule.span (𝓞 (maximalRealSubfield E)) {t | ∃ x ∈ L, ∃ x' ∈ L, t = Q x x'}) →
    (∀ c : 𝔠.elt, ∃ (n : ℕ) (t : 𝓞 (maximalRealSubfield E)), n.Coprime l ∧ n • c = t • c₀) →
    mu ≠ 0 ∧ GlobalTheory.IndefiniteRowSideFullHecke.PolarisationModuleIndex.GenAt l (GlobalTheory.IndefiniteRowSideFullHecke.PolarisationModuleIndex.polMod L)
      ((((c₀ : maximalRealSubfield E) / (2 * c1) : maximalRealSubfield E) : E) * mu) := by
  intro E _ _ _ L 𝔠 mu c1 Q l c₀ h1 h2 h3 h4 h5 h6 h7
  have hL : ∀ (a : OF E), ∀ x ∈ L, algebraMap (OF E) E a * x ∈ L := fun a x hx => by
    rw [← Algebra.smul_def]; exact L.smul_mem a hx
  have hcoe : ∀ a : OF E, algebraMap (OF E) E a = ((a : maximalRealSubfield E) : E) := fun a => rfl
  have hc0 : (𝔠 : FractionalIdeal (nonZeroDivisors (𝓞 (maximalRealSubfield E))) (maximalRealSubfield E)) ≠ 0 :=
    𝔠.ne_zero
  have hd0 : dualLat 𝔠 ≠ 0 := FractionalIdeal.dual_ne_zero ℤ ℚ hc0
  have key : ∀ x ∈ L, ∀ x' ∈ L, Algebra.trace (maximalRealSubfield E) E (mu * x * IsCMField.complexConj E x') =
      2 * c1 * Q x x' := by
    intro x hx x' hx'
    rw [← sub_eq_zero]
    apply eq_zero_of_trace
    intro a
    have h := h4 _ (hL a x hx) x' hx'
    rw [h3 a x hx x' hx'] at h
    have e : mu * (algebraMap (OF E) E a * x) * IsCMField.complexConj E x' =
        ((a : maximalRealSubfield E) : E) * (mu * x * IsCMField.complexConj E x') := by
      rw [hcoe]; ring
    rw [e, trace_coe_mul] at h
    have e2 : (a : maximalRealSubfield E) * (2 * c1 * Q x x') =
        c1 * (a * Q x x') + c1 * (a * Q x x') := by ring
    rw [mul_sub, map_sub, h, e2, map_add]; ring
  have key2 : ∀ (k : maximalRealSubfield E), ∀ x ∈ L, ∀ x' ∈ L,
      Algebra.trace ℚ E ((k : E) * mu * x * IsCMField.complexConj E x') =
        Algebra.trace ℚ (maximalRealSubfield E) (k * (2 * c1 * Q x x')) := by
    intro k x hx x' hx'
    rw [← key x hx x' hx', ← trace_coe_mul]
    congr 1; ring
  have h2c : (2 * c1 : maximalRealSubfield E) ≠ 0 := mul_ne_zero two_ne_zero h1
  have hmu : mu ≠ 0 := by
    rintro rfl
    apply hd0
    rw [FractionalIdeal.eq_zero_iff]
    intro t ht
    have h := h6 t ht
    have hle : Submodule.span (𝓞 (maximalRealSubfield E)) {t | ∃ x ∈ L, ∃ x' ∈ L, t = Q x x'} ≤ ⊥ := by
      rw [Submodule.span_le]
      rintro _ ⟨x, hx, x', hx', rfl⟩
      have := key x hx x' hx'
      rw [zero_mul, zero_mul, map_zero] at this
      exact (mul_eq_zero.1 this.symm).resolve_left h2c
    exact hle h
  have hfix : ∀ k : maximalRealSubfield E, IsCMField.complexConj E (k : E) = k := fun k =>
    (IsCMField.complexConj E).commutes k
  refine ⟨hmu, ⟨?_, ?_⟩, ?_⟩
  · show IsCMField.complexConj E _ = _
    rw [map_mul, hfix, h2]; ring
  · intro x hx x' hx'
    obtain ⟨n, hn⟩ := (FractionalIdeal.mem_dual hc0).1 (h5 x hx x' hx') c₀ c₀.2
    refine ⟨n, ?_⟩
    refine (key2 _ x hx x' hx').trans ?_
    rw [Algebra.traceForm_apply] at hn
    have e : (c₀ : maximalRealSubfield E) / (2 * c1) * (2 * c1 * Q x x') = Q x x' * c₀ := by
      field_simp
    rw [e, ← hn]; simp
  · rintro ν ⟨hν1, hν2⟩
    have hs : IsCMField.complexConj E (ν / mu) = ν / mu := by
      have hν1' : IsCMField.complexConj E ν = -ν := hν1
      rw [map_div₀, hν1', h2, neg_div_neg_eq]
    let s : maximalRealSubfield E := ⟨ν / mu, (IsCMField.complexConj_eq_self_iff E _).1 hs⟩
    have hνs : ν = (s : E) * mu := by
      show ν = ν / mu * mu
      field_simp
    have hmem : 2 * c1 * s ∈ (𝔠 : FractionalIdeal (nonZeroDivisors (𝓞 (maximalRealSubfield E))) (maximalRealSubfield E)) := by
      rw [← FractionalIdeal.dual_dual ℤ ℚ (𝔠 : FractionalIdeal (nonZeroDivisors (𝓞 (maximalRealSubfield E))) (maximalRealSubfield E))]
      refine (FractionalIdeal.mem_dual hd0).2 ?_
      intro t ht
      have h : ∀ a : OF E, Algebra.trace ℚ (maximalRealSubfield E) (2 * c1 * s * (a * t)) ∈ (algebraMap ℤ ℚ).range := by
        have h := h6 t ht
        clear ht
        induction h using Submodule.span_induction with
        | mem t ht =>
          obtain ⟨x, hx, x', hx', rfl⟩ := ht
          intro a
          obtain ⟨n, hn⟩ := hν2 _ (hL a x hx) x' hx'
          refine ⟨n, ?_⟩
          rw [hνs] at hn
          have h := (key2 s _ (hL a x hx) x' hx').symm.trans hn
          rw [h3 a x hx x' hx'] at h
          have e : 2 * c1 * s * (a * Q x x') = s * (2 * c1 * (a * Q x x')) := by ring
          rw [e, h]; simp
        | zero => intro a; simp
        | add t u _ _ ht hu =>
          intro a
          rw [mul_add, mul_add, map_add]
          exact add_mem (ht a) (hu a)
        | smul b t _ ht =>
          intro a
          have e : (a : maximalRealSubfield E) * b • t = ((a * b : OF E) : maximalRealSubfield E) * t := by
            rw [Algebra.smul_def, ← mul_assoc]
            congr 1
          rw [e]; exact ht _
      have := h 1
      rw [Algebra.traceForm_apply]
      simpa using this
    obtain ⟨n, t, hn, hnt⟩ := h7 ⟨2 * c1 * s, hmem⟩
    refine ⟨n, hn, t, ?_⟩
    have e : (n : maximalRealSubfield E) * (2 * c1 * s) = (t : maximalRealSubfield E) * c₀ := by
      have := congrArg Subtype.val hnt
      simpa [nsmul_eq_mul, Algebra.smul_def] using this
    have e2 : (n : maximalRealSubfield E) * s = (t : maximalRealSubfield E) * (c₀ / (2 * c1)) := by
      rw [mul_div_assoc', ← e]; field_simp
    have e3 := congrArg (fun z : maximalRealSubfield E => (z : E)) e2
    simp only [Subfield.coe_mul, SubringClass.coe_natCast] at e3
    rw [hcoe, hνs, ← mul_assoc, ← mul_assoc, e3]

end GlobalTheory.PolGen
