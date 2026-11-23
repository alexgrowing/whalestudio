import Mathlib
import Development.AutomorphicArithmetic.CyclotomicBounds.TraceDuality.TraceForm
import Development.AutomorphicArithmetic.CyclotomicBounds.TraceDuality.DualFamily
import Development.AutomorphicArithmetic.CyclotomicBounds.TraceDuality.EmbSum
open NumberField
open scoped TensorProduct NNReal
open Classical

theorem UpperTheory.WildB.casimir :
    ∀ (E : Type) [Field E] [NumberField E] (d : 𝓞 E) (m : ℕ), d ∈ differentIdeal ℤ (𝓞 E) → d ≠ 0 → (∀ a ∈ differentIdeal ℤ (𝓞 E), d ∣ (m : 𝓞 E) * a) → ∃ (n : ℕ) (a b : Fin n → 𝓞 E) (lam : 𝓞 E →+ ℤ), (∀ x : 𝓞 E, ∑ j, lam (b j * x) • a j = (m : 𝓞 E) * x) ∧ (∀ x : 𝓞 E, ∃ M : Fin n → Fin n → ℤ, (∀ j, x * a j = ∑ i, M i j • a i) ∧ ∀ i, x * b i = ∑ j, M i j • b j) ∧ ∀ (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (φ ψ : E →+* C), ∑ j, φ (a j : E) * ψ (b j : E) = if ψ = φ then φ (d : E) else 0 := by
  intro E _ _ d m hd hd0 hm
  obtain ⟨lam, hlam⟩ := UpperTheory.WildB.traceForm E d m hd0 hm
  obtain ⟨n, a, b, h1, h2, h3⟩ := UpperTheory.WildB.dualFamily E d hd hd0
  have hs : ∀ (z : Fin n → ℤ) (c : Fin n → 𝓞 E),
      algebraMap (𝓞 E) E (∑ j, z j • c j) = ∑ j, (z j : ℚ) • (c j : E) := by
    intro z c
    rw [map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_zsmul, Int.cast_smul_eq_zsmul]
  refine ⟨n, a, b, lam, fun x => ?_, fun x => ?_,
    fun C _ _ _ φ ψ => UpperTheory.WildB.embSum E d hd0 n a b h1 C φ ψ⟩
  · apply RingOfIntegers.coe_injective
    rw [hs, map_mul, map_natCast, ← h1 ((m : E) * algebraMap (𝓞 E) E x)]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hlam]
    congr 2
    change (m : E) * ((b j : E) * (x : E)) / (d : E) = (m : E) * (x : E) * (b j : E) / (d : E)
    ring
  · choose M hM using h3 x
    refine ⟨M, fun j => ?_, fun i => ?_⟩
    · apply RingOfIntegers.coe_injective
      rw [hs (fun i => M i j), map_mul, ← h1 (algebraMap (𝓞 E) E x * algebraMap (𝓞 E) E (a j))]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hM]
    · apply RingOfIntegers.coe_injective
      rw [hs (fun j => M i j), map_mul, ← h2 (algebraMap (𝓞 E) E x * algebraMap (𝓞 E) E (b i))]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [hM, mul_right_comm]
