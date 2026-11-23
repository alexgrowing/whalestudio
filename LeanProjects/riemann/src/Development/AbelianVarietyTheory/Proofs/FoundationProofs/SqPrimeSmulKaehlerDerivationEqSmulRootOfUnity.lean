import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MemCycAlgOfPow
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.AlmostDualTraceDerivationMemSpanValues
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DerivationOnAdjoinMemSpanImage
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsAlmostDualTraceDataCyclotomicAlgebraStatement
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.RecOne GlobalTheory.AlmostEt
open scoped Matrix NNReal

namespace GlobalTheory.RecOne

section Gen

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω]

def evMul (l : ℕ) (A : ValuationSubring Ω) : Submodule A (KaehlerDifferential (fixA A) A) where
  carrier := {ω | ∃ N₀ : ℕ, ∀ N, N₀ ≤ N → ∀ z : A, IsPrimitiveRoot (z : Ω) (l ^ N) →
    ω ∈ Submodule.span A {dA A z}}
  add_mem' := by
    rintro a b ⟨N₁, h₁⟩ ⟨N₂, h₂⟩
    exact ⟨max N₁ N₂, fun N hN z hz =>
      add_mem (h₁ N (le_trans (le_max_left _ _) hN) z hz) (h₂ N (le_trans (le_max_right _ _) hN) z hz)⟩
  zero_mem' := ⟨0, fun _ _ _ _ => zero_mem _⟩
  smul_mem' := by
    rintro c a ⟨N₁, h₁⟩
    exact ⟨N₁, fun N hN z hz => Submodule.smul_mem _ c (h₁ N hN z hz)⟩

theorem dA_mem_evMul (l : ℕ) [Fact l.Prime] (A : ValuationSubring Ω) {x : A} {n : ℕ}
    (hx : x ^ (l ^ n) = 1) : dA A x ∈ evMul l A := by
  refine ⟨n, fun N hN z hz => ?_⟩
  have : NeZero (l ^ N) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  have h1 : (x : Ω) ^ (l ^ N) = 1 := by
    obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hN
    have h0 : (x : Ω) ^ (l ^ n) = 1 := by
      have := congrArg (fun t : A => (t : Ω)) hx
      simpa using this
    rw [pow_add, pow_mul, h0, one_pow]
  obtain ⟨i, -, hi⟩ := hz.eq_pow_of_pow_eq_one h1
  have h2 : x = z ^ i := by
    apply Subtype.ext
    rw [SubmonoidClass.coe_pow, hi]
  rw [h2, Derivation.leibniz_pow]
  exact Submodule.smul_of_tower_mem _ _
    (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))

end Gen

theorem l_sq_smul_dA_eq_smul : ∀ (l : ℕ) [Fact l.Prime], l ≠ 2 → ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (A : ValuationSubring Ω), OverL l A → ∀ v : A, ∃ N₀ : ℕ, ∀ N, N₀ ≤ N → ∀ z : A, IsPrimitiveRoot (z : Ω) (l ^ N) → ∃ y : A, ((l : A) ^ 2) • dA A v = y • dA A z := by
  intro l _ hl2 Ω _ _ _ A hA v
  have hder : ∀ B : Subalgebra (fixA A) A, IsDerOn B (fun x => dA A x) := fun B =>
    ⟨fun x _ y _ => map_add (dA A) x y, fun x _ y _ => Derivation.leibniz (dA A) x y,
      fun a => (dA A).map_algebraMap a⟩
  obtain ⟨C, tr, k, a, b, hF, htr⟩ := GlobalTheory.T.exists_almostDualTraceData_cyclotomicAlgebra l hl2 Ω A hA {v}
  have h1 := GlobalTheory.AlmostEt.derOn_mem_span_of_trData (fixA A) A _ (cycAlg l A) C tr k a b _ htr
    (fun x => dA A x) (hder C) v (hF (by simp))
  have h2 : Submodule.span A ((fun x => dA A x) '' (cycAlg l A : Set A)) ≤ evMul l A := by
    rw [Submodule.span_le]
    rintro _ ⟨x, hx, rfl⟩
    have h3 := GlobalTheory.AlmostEt.derOn_adjoin_mem_span (fixA A) A _ {z : A | ∃ n : ℕ, z ^ (l ^ n) = 1}
      (fun x => dA A x) (hder _) x hx
    refine Submodule.span_le.2 ?_ h3
    rintro _ ⟨y, ⟨n, hn⟩, rfl⟩
    exact dA_mem_evMul l A hn
  obtain ⟨N₀, h⟩ := h2 h1
  refine ⟨N₀, fun N hN z hz => ?_⟩
  obtain ⟨y, hy⟩ := Submodule.mem_span_singleton.1 (h N hN z hz)
  exact ⟨y, by rw [pow_two]; exact hy.symm⟩

end GlobalTheory.RecOne
