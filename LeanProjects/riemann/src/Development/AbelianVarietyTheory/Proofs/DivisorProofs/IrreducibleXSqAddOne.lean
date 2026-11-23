import Mathlib

open NumberField Polynomial

noncomputable section

namespace GlobalTheory.GaussExt

variable (F : Type) [Field F] [NumberField F] [IsTotallyReal F]

theorem irreducible_X_sq_add_one : Irreducible (X ^ 2 + 1 : F[X]) := by
  have hdeg : (X ^ 2 + 1 : F[X]).natDegree = 2 := by compute_degree!
  refine (Polynomial.irreducible_iff_roots_eq_zero_of_degree_le_three (by rw [hdeg]) (by rw [hdeg]; norm_num)).2 ?_
  refine Multiset.eq_zero_of_forall_notMem fun r hr => ?_
  rw [mem_roots (Monic.ne_zero (by monicity!)), IsRoot, eval_add, eval_pow, eval_X, eval_one] at hr
  obtain ⟨τ⟩ : Nonempty (F →+* ℝ) := by
    obtain ⟨φ⟩ := (inferInstance : Nonempty (F →+* ℂ))
    exact ⟨(IsTotallyReal.complexEmbedding_isReal φ).embedding⟩
  have := congrArg τ hr
  simp at this
  nlinarith [sq_nonneg (τ r)]

instance : Fact (Irreducible (X ^ 2 + 1 : F[X])) := ⟨irreducible_X_sq_add_one F⟩

abbrev Ext : Type := AdjoinRoot (X ^ 2 + 1 : F[X])

instance : Module.Finite F (Ext F) :=
  (AdjoinRoot.powerBasis (Monic.ne_zero (by monicity!) : (X ^ 2 + 1 : F[X]) ≠ 0)).finite

instance : NumberField (Ext F) where
  to_charZero := charZero_of_injective_algebraMap (algebraMap F (Ext F)).injective
  to_finiteDimensional := Module.Finite.trans F (Ext F)

def ii : Ext F := AdjoinRoot.root _

theorem ii_sq : ii F ^ 2 = -1 := by
  have h := AdjoinRoot.eval₂_root (X ^ 2 + 1 : F[X])
  simp only [eval₂_add, eval₂_pow, eval₂_X, eval₂_one] at h
  rw [ii]; linear_combination h

def gEmb (p : F × F) : Ext F := algebraMap F (Ext F) p.1 + algebraMap F (Ext F) p.2 * ii F

end GlobalTheory.GaussExt
