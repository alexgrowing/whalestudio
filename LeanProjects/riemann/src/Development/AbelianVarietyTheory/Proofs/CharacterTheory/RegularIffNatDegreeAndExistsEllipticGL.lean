import Mathlib
import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.AbByPOfComm
import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.InvariantSubspaceMobiusInverseRecEqOfFinrankLt
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI

namespace GlobalTheory.CuspGL

theorem pow_card_pow_eq_iff_natDegree_minpoly_dvd (F : Type) [Field F] [Finite F]
    (α : AlgebraicClosure F) (e : ℕ) :
    α ^ Nat.card F ^ e = α ↔ (minpoly F α).natDegree ∣ e := by
  classical
  have := Fintype.ofFinite F
  have hx : IsIntegral F α := Algebra.IsIntegral.isIntegral α
  have : FiniteDimensional F (IntermediateField.adjoin F {α}) := IntermediateField.adjoin.finiteDimensional hx
  have : Finite (IntermediateField.adjoin F {α}) := Module.finite_of_finite F
  have hgen : ∀ m : ℕ, (FiniteField.frobeniusAlgEquivOfAlgebraic F (IntermediateField.adjoin F {α}) ^ m)
      (IntermediateField.AdjoinSimple.gen F α) =
      IntermediateField.AdjoinSimple.gen F α ^ (Fintype.card F ^ m) := by
    intro m
    rw [AlgEquiv.coe_pow, FiniteField.coe_frobeniusAlgEquivOfAlgebraic_iterate]
  rw [← IntermediateField.adjoin.finrank hx,
    ← FiniteField.orderOf_frobeniusAlgEquivOfAlgebraic F (IntermediateField.adjoin F {α}), orderOf_dvd_iff_pow_eq_one,
    Nat.card_eq_fintype_card]
  constructor
  · intro h
    apply AlgEquiv.coe_toAlgHom_injective
    apply (IntermediateField.adjoin.powerBasis hx).algHom_ext
    rw [IntermediateField.adjoin.powerBasis_gen hx]
    simp only [AlgEquiv.coe_toAlgHom, AlgEquiv.one_apply]
    rw [hgen]
    apply Subtype.ext
    simpa using h
  · intro h
    have key := congrArg (fun f => ((f (IntermediateField.AdjoinSimple.gen F α) : (IntermediateField.adjoin F {α})) :
      AlgebraicClosure F)) h
    simp only [hgen, AlgEquiv.one_apply] at key
    simpa using key

theorem exists_GL_charpoly_eq_minpoly (F K : Type) [Field F] [Field K] [Algebra F K]
    (α : K) (hx : IsIntegral F α) (h0 : α ≠ 0) (n : ℕ) (hn : (minpoly F α).natDegree = n) :
    ∃ x : GL (Fin n) F, Matrix.charpoly (x : Matrix (Fin n) (Fin n) F) = minpoly F α := by
  subst hn
  have hdim : (IntermediateField.adjoin.powerBasis hx).dim = (minpoly F α).natDegree :=
    IntermediateField.adjoin.powerBasis_dim hx
  have hg : (IntermediateField.adjoin.powerBasis hx).gen ≠ 0 := by
    rw [IntermediateField.adjoin.powerBasis_gen hx]
    intro h
    apply h0
    have := congrArg (algebraMap (IntermediateField.adjoin F {α}) K) h
    simpa using this
  let f : (IntermediateField.adjoin F {α}) →ₐ[F] Matrix (Fin (minpoly F α).natDegree) (Fin (minpoly F α).natDegree) F :=
    (Matrix.reindexAlgEquiv F F (finCongr hdim)).toAlgHom.comp
      (Algebra.leftMulMatrix (IntermediateField.adjoin.powerBasis hx).basis)
  refine ⟨Units.map (f : (IntermediateField.adjoin F {α}) →* Matrix _ _ F) (Units.mk0 _ hg), ?_⟩
  rw [Units.coe_map, Units.val_mk0]
  change (Matrix.reindexAlgEquiv F F (finCongr hdim)
      (Algebra.leftMulMatrix (IntermediateField.adjoin.powerBasis hx).basis
        (IntermediateField.adjoin.powerBasis hx).gen)).charpoly = _
  rw [Matrix.coe_reindexAlgEquiv, Matrix.charpoly_reindex, charpoly_leftMulMatrix,
    IntermediateField.adjoin.powerBasis_gen, IntermediateField.minpoly_gen]

theorem regular_iff_natDegree_and_exists_elliptic :
    ∀ (F : Type) [Field F] [Finite F] (n : ℕ), 0 < n → ∀ α ∈ {α : AlgebraicClosure F | α ^ (Nat.card F ^ n - 1) = 1}, ((∀ e : ℕ, 0 < e → e < n → α ^ Nat.card F ^ e ≠ α) ↔ (minpoly F α).natDegree = n) ∧ ((minpoly F α).natDegree = n → ∃ x : GL (Fin n) F, Matrix.charpoly (x : Matrix (Fin n) (Fin n) F) = minpoly F α) := by
  intro F _ _ n hn α hα
  have hα' : α ^ (Nat.card F ^ n - 1) = 1 := hα
  have hx : IsIntegral F α := Algebra.IsIntegral.isIntegral α
  have hq : 1 < Nat.card F ^ n := Nat.one_lt_pow hn.ne' Finite.one_lt_card
  have h0 : α ≠ 0 := by
    rintro rfl
    rw [zero_pow (Nat.sub_ne_zero_of_lt hq)] at hα'
    exact zero_ne_one hα'
  have hfix : α ^ Nat.card F ^ n = α := by
    have hsplit : Nat.card F ^ n = (Nat.card F ^ n - 1) + 1 := (Nat.sub_add_cancel hq.le).symm
    rw [hsplit, pow_succ, hα', one_mul]
  have hdvd := (pow_card_pow_eq_iff_natDegree_minpoly_dvd F α n).1 hfix
  have hdpos : 0 < (minpoly F α).natDegree := minpoly.natDegree_pos hx
  refine ⟨⟨fun h => ?_, fun h e he1 he2 heq => ?_⟩,
    fun h => exists_GL_charpoly_eq_minpoly F (AlgebraicClosure F) α hx h0 n h⟩
  · by_contra hne
    have hlt : (minpoly F α).natDegree < n := lt_of_le_of_ne (Nat.le_of_dvd hn hdvd) hne
    exact h _ hdpos hlt ((pow_card_pow_eq_iff_natDegree_minpoly_dvd F α _).2 dvd_rfl)
  · have hd := (pow_card_pow_eq_iff_natDegree_minpoly_dvd F α e).1 heq
    rw [h] at hd
    exact absurd (Nat.le_of_dvd he1 hd) (not_le.2 he2)

end GlobalTheory.CuspGL
