import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.GlobAut

open Formalism.MainNotions.S NumberField
open scoped InnerProductSpace ComplexOrder MatrixOrder

namespace GlobalTheory

theorem exists_gram_factor {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] {k : ℕ}
    (x : Fin k → E) : ∃ C : Fin k → Fin k → ℂ, ∀ l l',
      ⟪x l, x l'⟫_ℂ = ∑ r, (starRingEnd ℂ) (C r l) * C r l' := by
  have h := (Matrix.posSemidef_gram ℂ x).nonneg
  obtain ⟨C, hC⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp h
  refine ⟨fun r l => C r l, fun l l' => ?_⟩
  have := congrFun (congrFun hC l) l'
  simpa [Matrix.gram_apply, Matrix.mul_apply, Matrix.star_apply] using this

theorem exists_normSq_tens_update {ι : Type} [Fintype ι] [DecidableEq ι] {H : ι → Type}
    [∀ v, NormedAddCommGroup (H v)] [∀ v, InnerProductSpace ℂ (H v)]
    {Hs : Type} [NormedAddCommGroup Hs] [InnerProductSpace ℂ Hs] (tens : (∀ v, H v) → Hs)
    (ht : ∀ x y, ⟪tens x, tens y⟫_ℂ = ∏ v, ⟪x v, y v⟫_ℂ) (v₀ : ι) {k : ℕ}
    (u : Fin k → ∀ v, H v) :
    ∃ C : ({v // v ≠ v₀} → Fin k) → Fin k → ℂ, ∀ a : Fin k → H v₀,
      ‖∑ l, tens (Function.update (u l) v₀ (a l))‖ ^ 2 = ∑ r, ‖∑ l, C r l • a l‖ ^ 2 := by
  choose D hD using fun v : {v // v ≠ v₀} => exists_gram_factor (fun l => u l v.1)
  refine ⟨fun r l => ∏ v, D v (r v) l, fun a => ?_⟩
  have key : ∀ l l', ⟪tens (Function.update (u l) v₀ (a l)),
      tens (Function.update (u l') v₀ (a l'))⟫_ℂ =
      ∑ r : {v // v ≠ v₀} → Fin k,
        ⟪(∏ v, D v (r v) l) • a l, (∏ v, D v (r v) l') • a l'⟫_ℂ := by
    intro l l'
    rw [ht, Fintype.prod_eq_mul_prod_subtype_ne _ v₀]
    simp only [Function.update_self]
    have h1 : ∏ v : {v // v ≠ v₀}, ⟪Function.update (u l) v₀ (a l) v.1,
        Function.update (u l') v₀ (a l') v.1⟫_ℂ =
        ∏ v : {v // v ≠ v₀}, ∑ r, (starRingEnd ℂ) (D v r l) * D v r l' := by
      refine Finset.prod_congr rfl fun v _ => ?_
      rw [Function.update_of_ne v.2, Function.update_of_ne v.2, hD]
    rw [h1, Fintype.prod_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [inner_smul_left, inner_smul_right, Finset.prod_mul_distrib, map_prod]
    ring
  have hc : ((‖∑ l, tens (Function.update (u l) v₀ (a l))‖ ^ 2 : ℝ) : ℂ) =
      ((∑ r : {v // v ≠ v₀} → Fin k, ‖∑ l, (∏ v, D v (r v) l) • a l‖ ^ 2 : ℝ) : ℂ) := by
    have hn : ∀ {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] (z : E),
        ((‖z‖ ^ 2 : ℝ) : ℂ) = ⟪z, z⟫_ℂ := by
      intro E _ _ z
      rw [inner_self_eq_norm_sq_to_K]
      simp
    rw [Complex.ofReal_sum, hn]
    simp only [hn, sum_inner, inner_sum, key]
    symm
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [Finset.sum_comm]
  exact_mod_cast hc

theorem sum_normSq_tens_update_le :
    ∀ (B : RowsAut) (v₀ : InfinitePlace B.I.F) (S : ∀ v, Submodule ℂ (B.H v)) (m : ℕ) (L : Fin m → (S v₀ →ₗ[ℂ] B.H v₀)) (β : ℝ), (∀ y : S v₀, ∑ i, ‖L i y‖ ^ 2 ≤ β * ‖y‖ ^ 2) → ∀ (k : ℕ) (u : Fin k → ∀ v, S v), open Classical in ∑ i, ‖∑ l, B.tens (Function.update (fun v => (u l v : B.H v)) v₀ (L i (u l v₀)))‖ ^ 2 ≤ β * ‖∑ l, B.tens (fun v => (u l v : B.H v))‖ ^ 2 := by
  classical
  intro B v₀ S m L β hL k u
  obtain ⟨C, hC⟩ := exists_normSq_tens_update B.tens B.tens_spec.1 v₀
    (fun l v => (u l v : B.H v))
  have h0 := hC (fun l => (u l v₀ : B.H v₀))
  have hu : ∀ l, Function.update (fun v => (u l v : B.H v)) v₀ (u l v₀ : B.H v₀) =
      fun v => (u l v : B.H v) := fun l => Function.update_eq_self v₀ _
  simp only [hu] at h0
  rw [h0, Finset.mul_sum]
  have h1 : ∀ i, _ := fun i => hC (fun l => L i (u l v₀))
  simp only [h1]
  rw [Finset.sum_comm]
  refine Finset.sum_le_sum fun r _ => ?_
  have := hL (∑ l, C r l • u l v₀)
  simp only [map_sum, map_smul] at this
  refine this.trans_eq ?_
  rw [← Submodule.norm_coe]
  simp

end GlobalTheory
