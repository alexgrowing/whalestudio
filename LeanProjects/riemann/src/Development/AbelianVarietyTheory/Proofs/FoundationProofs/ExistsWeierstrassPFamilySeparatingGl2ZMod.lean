import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ZetaActRefl
import Development.AbelianVarietyTheory.Definitions.Foundations.MemRingOfInR
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModQPrin
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModJTau
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.EqOrEqNegOfWeierstrassPTorsionEqStatement
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

namespace GlobalTheory.FNSep

theorem finite_nat_roots (a b c : ℂ) (h : ¬ (a = 0 ∧ b = 0 ∧ c = 0)) :
    {n : ℕ | a + (n : ℂ) * b + (n : ℂ) ^ 2 * c = 0}.Finite := by
  set P : Polynomial ℂ := Polynomial.C a + Polynomial.C b * Polynomial.X + Polynomial.C c * Polynomial.X ^ 2 with hPdef
  have hP : P ≠ 0 := by
    intro h0
    apply h
    have e0 := congrArg (fun q => q.coeff 0) h0
    have e1 := congrArg (fun q => q.coeff 1) h0
    have e2 := congrArg (fun q => q.coeff 2) h0
    simp [P, Polynomial.coeff_X_pow, Polynomial.coeff_C, Polynomial.coeff_X] at e0 e1 e2
    exact ⟨e0, e1, e2⟩
  have hf := (Polynomial.finite_setOf_isRoot hP).preimage (f := (Nat.cast : ℕ → ℂ)) Nat.cast_injective.injOn
  refine hf.subset ?_
  intro n hn
  simp only [Set.mem_setOf_eq, Set.mem_preimage] at hn ⊢
  rw [Polynomial.IsRoot.def]
  simp only [P, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_pow]
  linear_combination hn

theorem vmul_apply {N : ℕ} (a b : ZMod N) (α : GL (Fin 2) (ZMod N)) (j : Fin 2) :
    vmul ![a, b] α j = a * (α : Matrix (Fin 2) (Fin 2) (ZMod N)) 0 j + b * (α : Matrix (Fin 2) (Fin 2) (ZMod N)) 1 j := by
  simp [vmul, Matrix.vecMul, dotProduct, Fin.sum_univ_two]

theorem vmul_ne_zero {N : ℕ} (x : Fin 2 → ZMod N) (α : GL (Fin 2) (ZMod N)) (hx : x ≠ 0) : vmul x α ≠ 0 := by
  intro h
  apply hx
  have : Matrix.vecMul (vmul x α) ((α⁻¹ : GL (Fin 2) (ZMod N)) : Matrix (Fin 2) (Fin 2) (ZMod N)) = x := by
    rw [vmul, Matrix.vecMul_vecMul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.vecMul_one]
  rw [← this, h, Matrix.zero_vecMul]

end GlobalTheory.FNSep

namespace GlobalTheory.FNSep

theorem eq_or_eq_neg_of_rows {N : ℕ} (α β : GL (Fin 2) (ZMod N))
    (h0 : vmul ![1, 0] α = vmul ![1, 0] β ∨ vmul ![1, 0] α = -vmul ![1, 0] β)
    (h1 : vmul ![0, 1] α = vmul ![0, 1] β ∨ vmul ![0, 1] α = -vmul ![0, 1] β)
    (h2 : vmul ![1, 1] α = vmul ![1, 1] β ∨ vmul ![1, 1] α = -vmul ![1, 1] β) :
    α = β ∨ α = -β := by
  rcases h0 with h0 | h0 <;> rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2 <;>
  · have E0 : ∀ j, _ := fun j => congrFun h0 j
    have E1 : ∀ j, _ := fun j => congrFun h1 j
    have E2 : ∀ j, _ := fun j => congrFun h2 j
    simp only [Pi.neg_apply, vmul_apply] at E0 E1 E2
    first
    | (left; apply Units.ext; ext i j; fin_cases i <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.isValue] <;> first | linear_combination E0 j | linear_combination E1 j | linear_combination E2 j - E0 j | linear_combination E2 j - E1 j)
    | (right; apply Units.ext; ext i j; rw [Units.val_neg, Matrix.neg_apply]; fin_cases i <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.isValue] <;> first | linear_combination E0 j | linear_combination E1 j | linear_combination E2 j - E0 j | linear_combination E2 j - E1 j)

theorem sep_family : ∀ (N : ℕ) [NeZero N], ∃ c₁ c₂ : ℕ, ∀ α β : GL (Fin 2) (ZMod N), (fun τ => wp N (vmul ![1, 0] α) τ + (c₁ : ℂ) * wp N (vmul ![0, 1] α) τ + (c₂ : ℂ) * wp N (vmul ![1, 1] α) τ) = (fun τ => wp N (vmul ![1, 0] β) τ + (c₁ : ℂ) * wp N (vmul ![0, 1] β) τ + (c₂ : ℂ) * wp N (vmul ![1, 1] β) τ) → α = β ∨ α = -β := by
  intro N _
  classical
  let u : GL (Fin 2) (ZMod N) × GL (Fin 2) (ZMod N) → (Fin 2 → ZMod N) → ℍ → ℂ :=
    fun p e τ => wp N (vmul e p.1) τ - wp N (vmul e p.2) τ
  let S : Set ℕ := ⋃ p : GL (Fin 2) (ZMod N) × GL (Fin 2) (ZMod N),
    {n : ℕ | ¬ (∀ τ, u p ![1, 0] τ = 0 ∧ u p ![0, 1] τ = 0 ∧ u p ![1, 1] τ = 0) ∧
      ∀ τ, u p ![1, 0] τ + (n : ℂ) * u p ![0, 1] τ + (n : ℂ) ^ 2 * u p ![1, 1] τ = 0}
  have hfin : Finite (GL (Fin 2) (ZMod N)) :=
    Finite.of_injective (fun a : GL (Fin 2) (ZMod N) => (a : Matrix (Fin 2) (Fin 2) (ZMod N))) fun a b h => Units.ext h
  have hS : S.Finite := by
    refine Set.finite_iUnion fun p => ?_
    by_cases hz : ∀ τ, u p ![1, 0] τ = 0 ∧ u p ![0, 1] τ = 0 ∧ u p ![1, 1] τ = 0
    · exact Set.finite_empty.subset fun n hn => absurd hz hn.1
    · obtain ⟨τ, hτ⟩ := not_forall.mp hz
      exact (finite_nat_roots _ _ _ hτ).subset fun n hn => hn.2 τ
  obtain ⟨n, hn⟩ := hS.infinite_compl.nonempty
  refine ⟨n, n ^ 2, fun α β hfun => ?_⟩
  have hroot : ∀ τ, u (α, β) ![1, 0] τ + (n : ℂ) * u (α, β) ![0, 1] τ + (n : ℂ) ^ 2 * u (α, β) ![1, 1] τ = 0 := by
    intro τ
    have := congrFun hfun τ
    push_cast at this
    simp only [u]
    linear_combination this
  have hz : ∀ τ, u (α, β) ![1, 0] τ = 0 ∧ u (α, β) ![0, 1] τ = 0 ∧ u (α, β) ![1, 1] τ = 0 := by
    by_contra hz
    exact hn (Set.mem_iUnion.mpr ⟨(α, β), hz, hroot⟩)
  rcases Nat.lt_or_ge 1 N with hN | hN
  · haveI : Fact (1 < N) := ⟨hN⟩
    obtain ⟨z0, z1, z2⟩ := hz UpperHalfPlane.I
    have ne0 : (![1, 0] : Fin 2 → ZMod N) ≠ 0 := by
      intro h; have := congrFun h 0; simp at this
    have ne1 : (![0, 1] : Fin 2 → ZMod N) ≠ 0 := by
      intro h; have := congrFun h 1; simp at this
    have ne2 : (![1, 1] : Fin 2 → ZMod N) ≠ 0 := by
      intro h; have := congrFun h 0; simp at this
    exact eq_or_eq_neg_of_rows α β
      (GlobalTheory.T.eq_or_eq_neg_of_weierstrassP_torsion_eq N UpperHalfPlane.I _ _ (vmul_ne_zero _ α ne0) (vmul_ne_zero _ β ne0) (sub_eq_zero.mp z0))
      (GlobalTheory.T.eq_or_eq_neg_of_weierstrassP_torsion_eq N UpperHalfPlane.I _ _ (vmul_ne_zero _ α ne1) (vmul_ne_zero _ β ne1) (sub_eq_zero.mp z1))
      (GlobalTheory.T.eq_or_eq_neg_of_weierstrassP_torsion_eq N UpperHalfPlane.I _ _ (vmul_ne_zero _ α ne2) (vmul_ne_zero _ β ne2) (sub_eq_zero.mp z2))
  · have h1 : N = 1 := le_antisymm hN (Nat.pos_of_ne_zero (NeZero.ne N))
    subst h1
    left
    apply Units.ext
    ext i j
    exact Subsingleton.elim _ _

end GlobalTheory.FNSep
