import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasLenOfLatLen

open Formalism.UG GlobalTheory.SatakeWeyl GlobalTheory.InertZeta

namespace GlobalTheory.CompanionTheory.InertZeta

private theorem mem_range_bc_of_entries_mem_intL {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {n : ℕ}
    (g : GL (Fin n) L) (h1 : ∀ i j, (g : Matrix (Fin n) (Fin n) L) i j ∈ Formalism.UG.intL L)
    (h2 : ∀ i j, ((g⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i j ∈ Formalism.UG.intL L) :
    g ∈ (Formalism.UG.bc (Formalism.UG.intL L).subtype).range := by
  let M : Matrix (Fin n) (Fin n) (Formalism.UG.intL L) := fun i j => ⟨_, h1 i j⟩
  let M' : Matrix (Fin n) (Fin n) (Formalism.UG.intL L) := fun i j => ⟨_, h2 i j⟩
  have hM : (Formalism.UG.intL L).subtype.mapMatrix M = g := by ext i j; rfl
  have hM' : (Formalism.UG.intL L).subtype.mapMatrix M' = ((g⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) := by
    ext i j; rfl
  have inj : Function.Injective
      ((Formalism.UG.intL L).subtype.mapMatrix : Matrix (Fin n) (Fin n) (Formalism.UG.intL L) → Matrix (Fin n) (Fin n) L) :=
    fun A B h => Matrix.ext fun i j => Subtype.ext (by simpa [RingHom.mapMatrix_apply] using congrFun (congrFun h i) j)
  refine ⟨⟨M, M', inj ?_, inj ?_⟩, Units.ext hM⟩
  · rw [map_mul, map_one, hM, hM']
    exact g.mul_inv
  · rw [map_mul, map_one, hM, hM']
    exact g.inv_mul

private theorem entry_lemma_2 {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {σ : L →+* L}
    (hv : ∀ x, Valued.v (σ x) = Valued.v x) (g : Formalism.UG.GU σ 1) (i j : Fin 1) :
    ((g : GL (Fin 1) L) : Matrix (Fin 1) (Fin 1) L) i j ∈ Formalism.UG.intL L := by
  have hg : Formalism.UG.cT σ ((g : GL (Fin 1) L) : Matrix (Fin 1) (Fin 1) L) * Formalism.UG.antiJ L 1 *
      ((g : GL (Fin 1) L) : Matrix (Fin 1) (Fin 1) L) = Formalism.UG.antiJ L 1 := g.2
  rw [Subsingleton.elim i 0, Subsingleton.elim j 0]
  set x := ((g : GL (Fin 1) L) : Matrix (Fin 1) (Fin 1) L) 0 0 with hx
  have e : σ x * x = 1 := by
    have := congrFun (congrFun hg 0) 0
    simpa [Matrix.mul_apply, Formalism.UG.cT, Formalism.UG.antiJ, hx] using this
  have e2 : Valued.v x ^ 2 = 1 := by
    rw [sq]
    nth_rewrite 1 [← hv x]
    rw [← map_mul, e, map_one]
  refine (Valuation.mem_integer_iff _ _).mpr ?_
  exact (pow_le_one_iff two_ne_zero).mp e2.le

theorem smallRank : SmallRank := by
  intro L _ _ ϖ σ q n hσ hn g
  rw [Formalism.UG.KU, Subgroup.mem_subgroupOf, Formalism.UG.intPts, Subgroup.mem_inf]
  refine ⟨g.2, ?_⟩
  interval_cases n
  · exact mem_range_bc_of_entries_mem_intL _ (fun i => i.elim0) (fun i => i.elim0)
  · exact mem_range_bc_of_entries_mem_intL _ (entry_lemma_2 hσ.2.1 g) (entry_lemma_2 hσ.2.1 g⁻¹)

end GlobalTheory.CompanionTheory.InertZeta
