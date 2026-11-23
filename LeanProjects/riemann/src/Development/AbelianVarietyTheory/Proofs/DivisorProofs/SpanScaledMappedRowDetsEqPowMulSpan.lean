import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.PointShiftSt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Dets
open NumberField

open Pointwise
namespace GlobalTheory

theorem twistDet_rows {E K : Type} [Field E] [Field K] (τE : E →+* K) {p : ℕ}
    (β : Fin p → K) (c : Fin p → Fin p → E) :
    (Matrix.of fun i => β i • fun a => τE (c i a)).det = (∏ i, β i) * τE (Matrix.of c).det := by
  have h : (Matrix.of fun i => β i • fun a => τE (c i a)) =
      Matrix.diagonal β * (Matrix.of c).map τE := by
    ext i j
    simp [Matrix.diagonal_mul]
  rw [h, Matrix.det_mul, Matrix.det_diagonal, RingHom.map_det]
  rfl

theorem pow_eq_span_prod_set {K : Type} [Field K] [NumberField K] (p : ℕ) (𝔟 : Submodule (𝓞 K) K) :
    𝔟 ^ p = Submodule.span (𝓞 K) (∏ _i ∈ (Finset.univ : Finset (Fin p)), (𝔟 : Set K)) := by
  rw [← Submodule.prod_span]
  simp [Finset.prod_const, Finset.card_fin]

theorem span_twistDets_eq {E K : Type} [Field E] [NumberField E] [Field K] [NumberField K]
    (τ : 𝓞 E →+* 𝓞 K) (τE : E →+* K) (hτ : ∀ x : 𝓞 E, τE x = ((τ x : 𝓞 K) : K)) (p : ℕ)
    (𝔟 : Submodule (𝓞 K) K) (Λ : Submodule (𝓞 E) (Fin p → E)) :
    Submodule.span (𝓞 K) {d | ∃ y : Fin p → Fin p → K,
        (∀ i, y i ∈ {x : Fin p → K | ∃ β ∈ 𝔟, ∃ c ∈ Λ, x = β • fun a => τE (c a)}) ∧ d = (Matrix.of y).det} =
      𝔟 ^ p * Submodule.span (𝓞 K) (τE '' GlobalTheory.IdxTensor.dets E p Λ) := by
  set S : Set K := {d | ∃ y : Fin p → Fin p → K,
        (∀ i, y i ∈ {x : Fin p → K | ∃ β ∈ 𝔟, ∃ c ∈ Λ, x = β • fun a => τE (c a)}) ∧ d = (Matrix.of y).det}
    with hS
  have hpow := pow_eq_span_prod_set p 𝔟
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro d ⟨y, hy, rfl⟩
    choose β hβ c hc hyc using hy
    have hy' : y = fun i => β i • fun a => τE (c i a) := funext hyc
    subst hy'
    rw [twistDet_rows]
    refine Submodule.mul_mem_mul ?_ ?_
    · rw [hpow]
      refine Submodule.subset_span ?_
      rw [Set.mem_finset_prod]
      exact ⟨β, fun {i} _ => hβ i, rfl⟩
    · exact Submodule.subset_span ⟨_, Submodule.subset_span ⟨c, hc, rfl⟩, rfl⟩
  · rw [Submodule.mul_le]

    have key : ∀ c : Fin p → Fin p → E, (∀ i, c i ∈ Λ) →
        ∀ m ∈ 𝔟 ^ p, m * τE (Matrix.of c).det ∈ Submodule.span (𝓞 K) S := by
      intro c hc m hm
      rw [hpow] at hm
      induction hm using Submodule.span_induction with
      | mem x hx =>
        rw [Set.mem_finset_prod] at hx
        obtain ⟨β, hβ, rfl⟩ := hx
        refine Submodule.subset_span ⟨fun i => β i • fun a => τE (c i a), fun i => ?_, ?_⟩
        · exact ⟨β i, hβ (Finset.mem_univ i), c i, hc i, rfl⟩
        · rw [twistDet_rows]
      | zero => simp
      | add x y _ _ hx hy => rw [add_mul]; exact add_mem hx hy
      | smul r x _ hx => rw [smul_mul_assoc]; exact Submodule.smul_mem _ r hx
    have key2 : ∀ e ∈ GlobalTheory.IdxTensor.dets E p Λ, ∀ m ∈ 𝔟 ^ p,
        m * τE e ∈ Submodule.span (𝓞 K) S := by
      intro e he
      induction he using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨c, hc, rfl⟩ := hx
        exact key c hc
      | zero => intro m _; simp
      | add x y _ _ hx hy =>
        intro m hm; rw [map_add, mul_add]; exact add_mem (hx m hm) (hy m hm)
      | smul a x _ hx =>
        intro m hm
        rw [Algebra.smul_def, map_mul]
        have : τE (algebraMap (𝓞 E) E a) = ((τ a : 𝓞 K) : K) := hτ a
        rw [this, mul_left_comm, ← Algebra.smul_def (τ a)]
        · exact Submodule.smul_mem _ (τ a) (hx m hm)
    intro m hm n hn
    induction hn using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨e, he, rfl⟩ := hx
      exact key2 e he m hm
    | zero => simp
    | add x y _ _ hx hy => rw [mul_add]; exact add_mem hx hy
    | smul r x _ hx => rw [mul_smul_comm]; exact Submodule.smul_mem _ r hx

end GlobalTheory
