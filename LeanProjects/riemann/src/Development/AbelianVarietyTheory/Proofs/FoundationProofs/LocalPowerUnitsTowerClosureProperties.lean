import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.EigenOfTwoStep
open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ

namespace GlobalTheory.KZ.UnClosure

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ}

theorem one_mem (X : Tower Ω ε) (m : ℕ) : 1 ∈ X.Un m := by
  intro W _
  exact ⟨1, by simp⟩

theorem mul_mem (X : Tower Ω ε) (m : ℕ) (f g : X.Kˣ) (hf : f ∈ X.Un m) (hg : g ∈ X.Un m) :
    f * g ∈ X.Un m := by
  intro W hW
  obtain ⟨a, ha⟩ := hf W hW
  obtain ⟨b, hb⟩ := hg W hW
  refine ⟨a * b, ?_⟩
  have e : ((f * g : X.Kˣ) : X.K) / ((a * b : X.Kˣ) : X.K) ^ m
      = ((f : X.K) / (a : X.K) ^ m) * ((g : X.K) / (b : X.K) ^ m) := by
    push_cast; rw [mul_pow]; field_simp
  rw [e, map_mul, ha, hb, one_mul]

theorem inv_mem (X : Tower Ω ε) (m : ℕ) (f : X.Kˣ) (hf : f ∈ X.Un m) : f⁻¹ ∈ X.Un m := by
  intro W hW
  obtain ⟨a, ha⟩ := hf W hW
  refine ⟨a⁻¹, ?_⟩
  have e : ((f⁻¹ : X.Kˣ) : X.K) / ((a⁻¹ : X.Kˣ) : X.K) ^ m = ((f : X.K) / (a : X.K) ^ m)⁻¹ := by
    push_cast; rw [inv_pow]; field_simp
  rw [e, map_inv₀, ha, inv_one]

theorem pow_mem_self (X : Tower Ω ε) (m : ℕ) (g : X.Kˣ) : g ^ m ∈ X.Un m := by
  intro W _
  refine ⟨g, ?_⟩
  have e : ((g ^ m : X.Kˣ) : X.K) / (g : X.K) ^ m = 1 := by
    push_cast; exact div_self (pow_ne_zero _ g.ne_zero)
  rw [e, map_one]

theorem mem_of_mem_mul (X : Tower Ω ε) (m k : ℕ) (f : X.Kˣ) (hf : f ∈ X.Un (m * k)) : f ∈ X.Un m := by
  intro W hW
  obtain ⟨a, ha⟩ := hf W hW
  refine ⟨a ^ k, ?_⟩
  have e : ((a ^ k : X.Kˣ) : X.K) ^ m = (a : X.K) ^ (m * k) := by
    push_cast; rw [← pow_mul, mul_comm]
  rw [e]; exact ha

theorem pow_mem (X : Tower Ω ε) (m k : ℕ) (f : X.Kˣ) (hf : f ∈ X.Un m) : f ^ k ∈ X.Un m := by
  intro W hW
  obtain ⟨a, ha⟩ := hf W hW
  refine ⟨a ^ k, ?_⟩
  have e : ((f ^ k : X.Kˣ) : X.K) / ((a ^ k : X.Kˣ) : X.K) ^ m = ((f : X.K) / (a : X.K) ^ m) ^ k := by
    push_cast; rw [div_pow, ← pow_mul, ← pow_mul, mul_comm m k]
  rw [e, map_pow, ha, one_pow]

theorem val_eq_one_of_pow {K : Type} [Field K] (W : ValuationSubring K) (x : K) (m : ℕ) (hm : 0 < m)
    (h : W.valuation (x ^ m) = 1) : W.valuation x = 1 := by
  rw [map_pow] at h
  exact (pow_eq_one_iff.1 h).resolve_right hm.ne'

theorem mem_of_pow_mem (X : Tower Ω ε) (m k : ℕ) (g : X.Kˣ) (hm : 0 < m) (hg : g ^ m ∈ X.Un (m * k)) :
    g ∈ X.Un k := by
  intro W hW
  obtain ⟨a, ha⟩ := hg W hW
  refine ⟨a, val_eq_one_of_pow W _ m hm ?_⟩
  have e : ((g : X.K) / (a : X.K) ^ k) ^ m = ((g ^ m : X.Kˣ) : X.K) / (a : X.K) ^ (m * k) := by
    push_cast; rw [div_pow, ← pow_mul, mul_comm k m]
  rw [e]; exact ha

end GlobalTheory.KZ.UnClosure

namespace GlobalTheory.KZ.UnClosure

theorem un_closure : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε),
    Function.Injective ε → (∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ Hs ∧ X.an X.jK = (φ : Mero)) →
    ∀ (m : ℕ), 1 ∈ X.Un m ∧ (∀ f g, f ∈ X.Un m → g ∈ X.Un m → f * g ∈ X.Un m) ∧ (∀ f, f ∈ X.Un m → f⁻¹ ∈ X.Un m) ∧
      (∀ g : X.Kˣ, g ^ m ∈ X.Un m) ∧ (∀ (k : ℕ) f, f ∈ X.Un (m * k) → f ∈ X.Un m) ∧
      (∀ (k : ℕ) f, f ∈ X.Un m → f ^ k ∈ X.Un m) ∧
      ∀ (k : ℕ) (g : X.Kˣ), 0 < m → g ^ m ∈ X.Un (m * k) → g ∈ X.Un k := by
  intro Ω _ _ _ ε X _ _ m
  exact ⟨one_mem X m, mul_mem X m, inv_mem X m, pow_mem_self X m, fun k f hf => mem_of_mem_mul X m k f hf,
    fun k f hf => pow_mem X m k f hf, fun k g hm hg => mem_of_pow_mem X m k g hm hg⟩

end GlobalTheory.KZ.UnClosure
