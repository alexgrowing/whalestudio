import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExpoConjOfIsCsd

open NumberField IsDedekindDomain MeasureTheory Formalism.L2.Host GlobalTheory.CuspRep

namespace GlobalTheory.CuspRep

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}

theorem commute_cap_of_commute_Eop (τ : E →+* ℂ) (u : ℂ) (z : Module.End ℂ (Sm E a))
    (h : ∀ i j, Commute (Eop τ i j) z) : Commute (cap τ u) z := by
  let S : Subalgebra ℂ (Module.End ℂ (Sm E a)) := Subalgebra.centralizer ℂ {z}
  have hS : ∀ x, x ∈ S ↔ Commute x z := fun x => by
    simp only [S, Subalgebra.mem_centralizer_iff, Set.mem_singleton_iff, forall_eq]
    exact ⟨fun h => h.symm, fun h => h.symm⟩
  have hE : ∀ i j, Eop τ i j ∈ S := fun i j => (hS _).2 (h i j)
  refine (hS _).1 ?_
  refine S.sum_mem fun σ _ => S.mul_mem (intCast_mem S _) (S.list_prod_mem fun x hx => ?_)
  obtain ⟨k, rfl⟩ := List.mem_ofFn.1 hx
  refine S.add_mem ?_ (hE _ _)
  split_ifs
  · exact S.algebraMap_mem _
  · exact S.zero_mem

theorem commute_cap_Eop (τ τ' : E →+* ℂ) (u : ℂ) (i j : Fin a) : Commute (cap τ u) (Eop τ' i j) := by
  by_cases h : τ = τ'
  · subst h; exact cap_comm τ u i j
  · exact commute_cap_of_commute_Eop τ u _ fun k l => Eop_comm h k l i j

theorem lieS_atEmb_one (τ : E →+* ℂ) (i j : Fin a) :
    lieS E a i j (atEmb τ 1) = Eop τ i j + Eop (ComplexEmbedding.conjugate τ) i j := by
  have e : atEmb τ (-Complex.I) = -atEmb τ Complex.I := by
    rw [atEmb_eq]; simp
  simp only [Eop, atEmb_conj, map_one, Complex.conj_I, e, map_neg]
  match_scalars <;> ring

theorem lieS_atEmb_I (τ : E →+* ℂ) (i j : Fin a) :
    lieS E a i j (atEmb τ Complex.I) = Complex.I • (Eop τ i j - Eop (ComplexEmbedding.conjugate τ) i j) := by
  have e : atEmb τ (-Complex.I) = -atEmb τ Complex.I := by
    rw [atEmb_eq]; simp
  simp only [Eop, atEmb_conj, map_one, Complex.conj_I, e, map_neg]
  match_scalars <;> ring_nf <;> simp

theorem commute_cap_lieS (τ : E →+* ℂ) (u : ℂ) (i j : Fin a) (x : Cinf E) : Commute (cap τ u) (lieS E a i j x) := by
  classical
  have hx : x = ∑ w : InfinitePlace E, atEmb w.embedding (x w) := by
    conv_lhs => rw [← Finset.univ_sum_single x]
    refine Finset.sum_congr rfl fun w _ => ?_
    unfold atEmb
    rw [InfinitePlace.mk_embedding, if_pos rfl]
  rw [hx, map_sum]
  refine Commute.sum_right _ _ _ fun w _ => ?_
  rw [atEmb_eq, map_add, map_smul, map_smul, lieS_atEmb_one, lieS_atEmb_I]
  exact (((commute_cap_Eop τ _ u i j).add_right (commute_cap_Eop τ _ u i j)).smul_right _).add_right
    ((((commute_cap_Eop τ _ u i j).sub_right (commute_cap_Eop τ _ u i j)).smul_right _).smul_right _)

theorem commute_cap_lie (τ : E →+* ℂ) (u : ℂ) (X : Lie E a) : Commute (cap τ u) (lie E a X) := by
  have hX : lie E a X = ∑ i, ∑ j, lieS E a i j (X i j) := by
    simp only [lieS_apply, ← map_sum]
    exact congrArg _ (Matrix.matrix_eq_sum_single (Matrix.of X))
  rw [hX]
  exact Commute.sum_right _ _ _ fun i _ => Commute.sum_right _ _ _ fun j _ => commute_cap_lieS τ u i j _

theorem commute_cap_finRep (τ : E →+* ℂ) (u : ℂ) (k : GL (Fin a) (Af E)) : Commute (cap τ u) (finRep E a k) := by
  have h : ∀ i j x, Commute (lieS E a i j x) (finRep E a k) := fun i j x => lie_rt_fin _ k
  exact commute_cap_of_commute_Eop τ u _ fun i j =>
    ((h i j _).sub_left ((h i j _).smul_left _)).smul_left _

end GlobalTheory.CuspRep
