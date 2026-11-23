import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeCharExponentOfInfinityType

noncomputable section

open NumberField Formalism.L2.Host GlobalTheory.HeckeGal GlobalTheory.CuspRep GlobalTheory.CuspRep.InfType

namespace GlobalTheory.CuspRep.AlgExpo

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E]

theorem dchi_atEmb (χ : HChar E) (τ : E →+* ℂ) (z : ℂ) :
    dchi χ (atEmb τ z) = expo χ τ * z + expo χ (ComplexEmbedding.conjugate τ) * starRingEnd ℂ z := by
  have e : atEmb τ (-Complex.I) = -atEmb τ Complex.I := by
    rw [atEmb_eq]; simp
  rw [atEmb_eq, map_add, map_smul, map_smul]
  simp only [expo, atEmb_conj, map_one, Complex.conj_I, e, map_neg, Complex.real_smul]
  conv_rhs => rw [← Complex.re_add_im z]
  simp only [map_add, map_mul, Complex.conj_ofReal, Complex.conj_I]
  linear_combination (z.im * dchi χ (atEmb τ Complex.I)) * Complex.I_mul_I

theorem dchi_eq_sum (χ : HChar E) (x : Cinf E) : dchi χ x = ∑ φ : E →+* ℂ, expo χ φ * coord φ x := by
  classical
  have hx : x = ∑ w : InfinitePlace E, atEmb w.embedding (x w) := by
    conv_lhs => rw [← Finset.univ_sum_single x]
    refine Finset.sum_congr rfl fun w _ => ?_
    unfold atEmb
    rw [InfinitePlace.mk_embedding, if_pos rfl]
  rw [hx, map_sum]
  simp only [map_sum, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [dchi_atEmb]
  simp only [coord_atEmb', mul_add, Finset.sum_add_distrib, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
    if_true]

theorem chiInf_eq_prod (χ : HChar E) (n : (E →+* ℂ) → ℤ) (hn : ∀ τ, expo χ τ = n τ) (u : (Cinf E)ˣ) :
    ((chiInf χ u : ℂˣ) : ℂ) = ∏ φ : E →+* ℂ, coord φ (u : Cinf E) ^ n φ := by
  rw [← expU_log u, chiInf_expU, dchi_eq_sum, Complex.exp_sum]
  refine Finset.prod_congr rfl fun φ _ => ?_
  rw [coord_expU, hn, ← Complex.exp_int_mul]

theorem isAlgPos_of_expo : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (χ : HChar E)
    (n : (E →+* ℂ) → ℤ), (∀ τ, expo χ τ = n τ) → IsAlgPos χ n := by
  intro E _ _ _ χ n hn k _
  have e := chiInf_eq_prod χ n hn (Units.map (diagInf E).toMonoidHom k)
  rw [HChar.inf, MonoidHom.comp_apply, infDiag_eq]
  refine e.trans (Finset.prod_congr rfl fun φ _ => ?_)
  exact congrArg (· ^ n φ) (coord_algebraMap φ (k : E))

end GlobalTheory.CuspRep.AlgExpo
