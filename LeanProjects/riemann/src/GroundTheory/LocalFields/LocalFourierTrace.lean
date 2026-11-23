import Mathlib
import GroundTheory.LocalFields.Different
import GroundTheory.LocalFields.LocalFourierExistence

noncomputable section

namespace GroundTheory.LocalField

open ValuativeRel
open scoped nonZeroDivisors

attribute [local instance high] FaithfulSMul.to_isTorsionFree

section Dual

variable {L : Type*} [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]

theorem mem_valBall_ord_iff {c : L} (hc : c ≠ 0) {x : L} :
    x ∈ valBall L (ord c) ↔ ∃ y : 𝒪[L], x = c * y := by
  refine ⟨exists_mul_of_mem_valBall hc, ?_⟩
  rintro ⟨y, rfl⟩
  have := mul_mem_valBall (mem_valBall_ord (x := c)) (mem_valBall_zero_iff.mpr y.2)
  rwa [add_zero] at this

variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L] [Algebra.IsSeparable K L]

theorem forall_trace_mul_mem_iff (x : L) :
    (∀ z : 𝒪[L], Algebra.trace K L (x * z) ∈ 𝒪[K]) ↔
      x ∈ valBall L (-(differentExponent K L : ℤ)) := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[L]
  have hϖ0 : (ϖ : L) ≠ 0 := fun h => hϖ.ne_zero (Subtype.ext h)
  have hD : ((differentIdeal 𝒪[K] 𝒪[L] : Ideal 𝒪[L]) : FractionalIdeal 𝒪[L]⁰ L) =
      FractionalIdeal.spanSingleton 𝒪[L]⁰ ((ϖ : L) ^ differentExponent K L) := by
    rw [differentIdeal_eq_maximalIdeal_pow, hϖ.maximalIdeal_eq, Ideal.span_singleton_pow,
      FractionalIdeal.coeIdeal_span_singleton]
    rfl
  have hdual : FractionalIdeal.dual 𝒪[K] K (1 : FractionalIdeal 𝒪[L]⁰ L) =
      FractionalIdeal.spanSingleton 𝒪[L]⁰ ((ϖ : L) ^ differentExponent K L)⁻¹ := by
    rw [← FractionalIdeal.spanSingleton_inv, ← hD, coeIdeal_differentIdeal 𝒪[K] K L 𝒪[L], inv_inv]
  have hc0 : ((ϖ : L) ^ differentExponent K L)⁻¹ ≠ 0 := inv_ne_zero (pow_ne_zero _ hϖ0)
  have hc : ord ((ϖ : L) ^ differentExponent K L)⁻¹ = -(differentExponent K L : ℤ) := by
    rw [ord_inv (pow_ne_zero _ hϖ0), ord_pow hϖ0, ord_uniformizer hϖ, mul_one]
  have key : x ∈ FractionalIdeal.dual 𝒪[K] K (1 : FractionalIdeal 𝒪[L]⁰ L) ↔
      ∀ z : 𝒪[L], Algebra.trace K L (x * z) ∈ 𝒪[K] := by
    rw [FractionalIdeal.mem_dual (@one_ne_zero (FractionalIdeal 𝒪[L]⁰ L) _ _ _)]
    constructor
    · intro h z
      obtain ⟨a, ha⟩ := h (z : L) (FractionalIdeal.mem_one_iff _ |>.mpr ⟨z, rfl⟩)
      rw [Algebra.traceForm_apply] at ha
      rw [← ha]
      exact a.2
    · intro h a ha
      obtain ⟨z, rfl⟩ := (FractionalIdeal.mem_one_iff _).mp ha
      exact ⟨⟨_, h z⟩, by rw [Algebra.traceForm_apply]; rfl⟩
  rw [← key, hdual, FractionalIdeal.mem_spanSingleton, ← hc, mem_valBall_ord_iff hc0]
  constructor
  · rintro ⟨y, rfl⟩
    exact ⟨y, by rw [Algebra.smul_def, mul_comm]; rfl⟩
  · rintro ⟨y, rfl⟩
    exact ⟨y, by rw [Algebra.smul_def, mul_comm]; rfl⟩

end Dual

section TraceChar

variable {K L : Type*} [Field K] [Field L] [Algebra K L]

variable (L) in

def traceChar (ψ : AddChar K Circle) : AddChar L Circle :=
  ψ.compAddMonoidHom (Algebra.trace K L).toAddMonoidHom

theorem traceChar_apply (ψ : AddChar K Circle) (x : L) :
    traceChar L ψ x = ψ (Algebra.trace K L x) := rfl

theorem trace_algebraMap_mul (a : K) (x : L) :
    Algebra.trace K L (algebraMap K L a * x) = a * Algebra.trace K L x := by
  rw [← Algebra.smul_def, LinearMap.map_smul, smul_eq_mul]

variable [ValuativeRel K] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [ValuativeExtension K L]

theorem mem_valBall_algebraMap_mul {m : ℤ} {x : L} (hx : x ∈ valBall L m) {a : K}
    (ha : a ∈ 𝒪[K]) : algebraMap K L a * x ∈ valBall L m := by
  have := mul_mem_valBall (mem_valBall_zero_iff.mpr ((algebraMap_mem_integer_iff K L a).mpr ha)) hx
  rwa [zero_add] at this

variable [TopologicalSpace K] [IsNonarchimedeanLocalField K] [FiniteDimensional K L]

variable {ψ : AddChar K Circle} (hψ : Continuous ψ) (hψ1 : ψ ≠ 1)
include hψ hψ1

omit [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L] in

theorem forall_integer_mul_eq_one_iff (t : K) :
    (∀ a ∈ 𝒪[K], ψ (a * t) = 1) ↔ t ∈ valBall K (addCharConductor ψ) := by
  rcases eq_or_ne t 0 with rfl | ht
  · simp only [mul_zero, AddChar.map_zero_eq_one, implies_true, true_iff]
    exact zero_mem _
  rw [mem_valBall_iff_le_ord ht, ← isTrivialOn_iff hψ hψ1]
  constructor
  · intro h x hx
    obtain ⟨y, rfl⟩ := (mem_valBall_ord_iff ht).mp hx
    rw [mul_comm]
    exact h y y.2
  · intro h a ha
    apply h
    rw [mem_valBall_ord_iff ht]
    exact ⟨⟨a, ha⟩, mul_comm _ _⟩

variable [Algebra.IsSeparable K L]

theorem isTrivialOn_traceChar_iff (m : ℤ) :
    IsTrivialOn (traceChar L ψ) m ↔
      (ramificationIndex K L : ℤ) * addCharConductor ψ - differentExponent K L ≤ m := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[K]
  have hϖ0 : (ϖ : K) ≠ 0 := fun h => hϖ.ne_zero (Subtype.ext h)
  obtain ⟨c, hcdef⟩ : ∃ c : K, c = (ϖ : K) ^ addCharConductor ψ := ⟨_, rfl⟩
  have hc0 : c ≠ 0 := hcdef ▸ zpow_ne_zero _ hϖ0
  have hcK : ord c = addCharConductor ψ := by rw [hcdef, ord_zpow hϖ0, ord_uniformizer hϖ, mul_one]
  have hcL : ord (algebraMap K L c) = ramificationIndex K L * addCharConductor ψ := by
    rw [ord_algebraMap, hcK]
  have step1 : IsTrivialOn (traceChar L ψ) m ↔
      ∀ x ∈ valBall L m, Algebra.trace K L x ∈ valBall K (addCharConductor ψ) := by
    constructor
    · intro h x hx
      rw [← forall_integer_mul_eq_one_iff hψ hψ1]
      intro a ha
      rw [← trace_algebraMap_mul]
      exact h _ (mem_valBall_algebraMap_mul hx ha)
    · intro h x hx
      rw [traceChar_apply]
      exact isTrivialOn_addCharConductor hψ hψ1 _ (h x hx)
  rw [step1]
  constructor
  · intro h
    obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[L]
    have hπ0 : (π : L) ≠ 0 := fun h => hπ.ne_zero (Subtype.ext h)
    obtain ⟨w, hwdef⟩ : ∃ w : L,
        w = (π : L) ^ (m - ramificationIndex K L * addCharConductor ψ) := ⟨_, rfl⟩
    have hw0 : w ≠ 0 := hwdef ▸ zpow_ne_zero _ hπ0
    have hwk : ord w = m - ramificationIndex K L * addCharConductor ψ := by
      rw [hwdef, ord_zpow hπ0, ord_uniformizer hπ, mul_one]
    have hw : w ∈ valBall L (-(differentExponent K L : ℤ)) := by
      rw [← forall_trace_mul_mem_iff K]
      intro z
      have hx : algebraMap K L c * (w * z) ∈ valBall L m := by
        have h1 := mul_mem_valBall (mem_valBall_ord (x := algebraMap K L c))
          (mul_mem_valBall (mem_valBall_ord (x := w)) (mem_valBall_zero_iff.mpr z.2))
        rw [hcL, hwk] at h1
        convert h1 using 2
        ring
      have h2 := h _ hx
      rw [trace_algebraMap_mul] at h2
      have h3 := mul_mem_valBall (mem_valBall_ord (x := c⁻¹)) h2
      rw [ord_inv hc0, hcK, neg_add_cancel, ← mul_assoc, inv_mul_cancel₀ hc0, one_mul] at h3
      exact mem_valBall_zero_iff.mp h3
    rw [mem_valBall_iff_le_ord hw0, hwk] at hw
    linarith
  · intro hm x hx
    obtain ⟨w, hwdef⟩ : ∃ w : L, w = algebraMap K L c⁻¹ * x := ⟨_, rfl⟩
    have hw : w ∈ valBall L (-(differentExponent K L : ℤ)) := by
      have h1 := mul_mem_valBall (mem_valBall_ord (x := algebraMap K L c⁻¹)) hx
      rw [ord_algebraMap, ord_inv hc0, hcK] at h1
      rw [hwdef]
      exact valBall_antitone (by linarith) h1
    have h2 := (forall_trace_mul_mem_iff K w).mpr hw 1
    rw [OneMemClass.coe_one, mul_one] at h2
    have hx' : x = algebraMap K L c * w := by
      rw [hwdef, ← mul_assoc, ← map_mul, mul_inv_cancel₀ hc0, map_one, one_mul]
    rw [hx', trace_algebraMap_mul]
    have := mul_mem_valBall (mem_valBall_ord (x := c)) (mem_valBall_zero_iff.mpr h2)
    rwa [hcK, add_zero] at this

theorem continuous_traceChar : Continuous (traceChar L ψ) :=
  continuous_of_isTrivialOn ((isTrivialOn_traceChar_iff hψ hψ1 _).mpr le_rfl)

theorem traceChar_ne_one : traceChar L ψ ≠ 1 := by
  intro h
  have ht : IsTrivialOn (traceChar L ψ)
      ((ramificationIndex K L : ℤ) * addCharConductor ψ - differentExponent K L - 1) := by
    rw [h]
    intro x _
    exact AddChar.one_apply x
  have := (isTrivialOn_traceChar_iff hψ hψ1 _).mp ht
  linarith

theorem addCharConductor_traceChar :
    addCharConductor (traceChar L ψ) =
      (ramificationIndex K L : ℤ) * addCharConductor ψ - differentExponent K L := by
  have hc := continuous_traceChar (L := L) hψ hψ1
  have hne := traceChar_ne_one (L := L) hψ hψ1
  apply le_antisymm
  · exact (isTrivialOn_iff hc hne _).mp ((isTrivialOn_traceChar_iff hψ hψ1 _).mpr le_rfl)
  · exact (isTrivialOn_traceChar_iff hψ hψ1 _).mp (isTrivialOn_addCharConductor hc hne)

theorem addCharConductor_traceChar_of_eq_zero (h0 : addCharConductor ψ = 0) :
    addCharConductor (traceChar L ψ) = -(differentExponent K L : ℤ) := by
  rw [addCharConductor_traceChar hψ hψ1, h0, mul_zero, zero_sub]

end TraceChar

end GroundTheory.LocalField
