import Mathlib
open Pointwise

namespace GlobalTheory

theorem length_quotient_span_pow_le (O : Type) [CommRing O] (p : O) (n : ℕ) :
    Module.length O (O ⧸ Ideal.span {p ^ n}) ≤ (n : ℕ∞) * Module.length O (O ⧸ Ideal.span {p}) := by
  induction n with
  | zero =>
    rw [pow_zero, Ideal.span_singleton_one]
    haveI : Subsingleton (O ⧸ (⊤ : Ideal O)) := Ideal.Quotient.subsingleton_iff.mpr rfl
    rw [Module.length_eq_zero]
    exact bot_le
  | succ n ih =>
    set S : Submodule O O := Ideal.span {p ^ (n + 1)} with hS
    set T : Submodule O O := Ideal.span {p ^ n} with hT
    have hST : S ≤ T := Ideal.span_singleton_le_span_singleton.mpr (pow_dvd_pow p n.le_succ)
    let v : O ⧸ S := S.mkQ (p ^ n)
    have hker : (Ideal.span {p} : Submodule O O) ≤ LinearMap.ker (LinearMap.toSpanSingleton O (O ⧸ S) v) := by
      intro x hx
      obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp hx
      rw [LinearMap.mem_ker, LinearMap.toSpanSingleton_apply]
      simp only [v, Submodule.mkQ_apply, ← Submodule.Quotient.mk_smul, smul_eq_mul]
      rw [Submodule.Quotient.mk_eq_zero, hS, Ideal.mem_span_singleton']
      exact ⟨c, by ring⟩
    let ψ : (O ⧸ (Ideal.span {p} : Submodule O O)) →ₗ[O] O ⧸ S :=
      (Ideal.span {p} : Submodule O O).liftQ (LinearMap.toSpanSingleton O (O ⧸ S) v) hker
    let N : Submodule O (O ⧸ S) := LinearMap.range ψ
    have hN : N = T.map S.mkQ := by
      simp only [N, ψ, Submodule.range_liftQ, hT, Ideal.span, Submodule.map_span, Set.image_singleton]
      rw [← LinearMap.span_singleton_eq_range]
    have h1 := Module.length_eq_add_of_exact N.subtype N.mkQ N.injective_subtype N.mkQ_surjective
      (LinearMap.exact_subtype_mkQ N)
    have hle : Module.length O N ≤ Module.length O (O ⧸ Ideal.span {p}) :=
      Module.length_le_of_surjective ψ.rangeRestrict ψ.surjective_rangeRestrict
    have heq : Module.length O ((O ⧸ S) ⧸ N) = Module.length O (O ⧸ Ideal.span {p ^ n}) := by
      rw [hN]
      exact (Submodule.quotientQuotientEquivQuotient S T hST).length_eq
    change Module.length O (O ⧸ S) ≤ _
    rw [h1, heq]
    calc Module.length O N + Module.length O (O ⧸ Ideal.span {p ^ n})
        ≤ Module.length O (O ⧸ Ideal.span {p}) + (n : ℕ∞) * Module.length O (O ⧸ Ideal.span {p}) :=
          add_le_add hle ih
      _ = ((n + 1 : ℕ) : ℕ∞) * Module.length O (O ⧸ Ideal.span {p}) := by
          push_cast; ring

theorem main : ∀ (O : Type) [CommRing O] (p : O) (n : ℕ),
    Module.length O (O ⧸ Ideal.span {p ^ n}) ≤ (n : ℕ∞) * Module.length O (O ⧸ Ideal.span {p}) :=
  fun O _ p n => length_quotient_span_pow_le O p n

end GlobalTheory
