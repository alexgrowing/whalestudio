import Mathlib
open scoped TensorProduct
universe u

namespace GlobalTheory

theorem exists_idem_local_of_character :
    ∀ (k : Type) [Field k] (A : Type) [CommRing A] [Algebra k A] [FiniteDimensional k A]
      (φ : A →ₐ[k] k), ∃ e : A, IsIdempotentElem e ∧ φ e = 1 ∧
        ∀ a, φ a = 0 → IsNilpotent (e * a) := by
  intro k _ A _ _ _ φ
  haveI : IsArtinianRing A := IsArtinianRing.of_finite k A
  set m : Ideal A := RingHom.ker φ with hm
  obtain ⟨n, hn⟩ := IsArtinian.monotone_stabilizes (R := A) (M := A)
    ⟨fun n => OrderDual.toDual (m ^ n), fun _ _ h => Ideal.pow_le_pow_right h⟩
  have hst : ∀ j, n ≤ j → m ^ n = m ^ j := fun j hj => hn j hj
  set N := n + 1 with hN
  have hI : IsIdempotentElem (m ^ N) := by
    show m ^ N * m ^ N = m ^ N
    rw [← pow_add, ← hst (N + N) (by omega), hst N (by omega)]
  have hfg : (m ^ N).FG := IsNoetherian.noetherian _
  obtain ⟨f, hf, hIf⟩ := (Ideal.isIdempotentElem_iff_of_fg _ hfg).1 hI
  refine ⟨1 - f, hf.one_sub, ?_, ?_⟩
  · have hfm : f ∈ m := by
      have : f ∈ m ^ N := by rw [hIf]; exact Ideal.subset_span rfl
      exact Ideal.pow_le_self (by omega) this
    have : φ f = 0 := hfm
    simp [this]
  · intro a ha
    have ham : a ∈ m := ha
    have haN : a ^ N ∈ m ^ N := Ideal.pow_mem_pow ham N
    rw [hIf, Ideal.mem_span_singleton'] at haN
    obtain ⟨y, hy⟩ := haN
    refine ⟨N, ?_⟩
    rw [mul_pow, hf.one_sub.pow_succ_eq n, ← hy]
    have : (1 - f) * f = 0 := by rw [sub_mul, one_mul, hf.eq, sub_self]
    calc (1 - f) * (y * f) = y * ((1 - f) * f) := by ring
      _ = 0 := by rw [this, mul_zero]

end GlobalTheory
