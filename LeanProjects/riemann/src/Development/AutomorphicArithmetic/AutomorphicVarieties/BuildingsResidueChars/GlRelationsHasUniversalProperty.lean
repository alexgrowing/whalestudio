import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.CuspidalFiniteness.HasUnivOfStep
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.CenterEnvelopingGLLeAdjoinQuantumDet

open GroundTheory.Automorphic.HarishChandra

attribute [local instance 100] LieRing.ofAssociativeRing

namespace UpperTheory.V.Af.CuspFin.One

private noncomputable def lin {A : Type} [Ring A] [Algebra ℂ A] {n : ℕ} (F : Fin n → Fin n → A) :
    gl n →ₗ[ℂ] A where
  toFun X := ∑ a : Fin n × Fin n, X a.1 a.2 • F a.1 a.2
  map_add' X Y := by simp [add_smul, Finset.sum_add_distrib]
  map_smul' c X := by simp [Finset.smul_sum, mul_smul]

private theorem lin_E {A : Type} [Ring A] [Algebra ℂ A] {n : ℕ} (F : Fin n → Fin n → A) (a : Fin n × Fin n) :
    lin F (E a) = F a.1 a.2 := by
  obtain ⟨i, j⟩ := a
  show ∑ b : Fin n × Fin n, (E (i, j)) b.1 b.2 • F b.1 b.2 = F i j
  rw [Finset.sum_eq_single (i, j)]
  · simp [E]
  · rintro ⟨k, l⟩ _ hb
    have : ¬ (i = k ∧ j = l) := fun h => hb (by rw [h.1, h.2])
    simp [E, Matrix.single_apply, this]
  · simp

private theorem lin_lie {A : Type} [Ring A] [Algebra ℂ A] {n : ℕ} (F : Fin n → Fin n → A)
    (hF : Formalism.REAL.GlRel F) (X Y : gl n) : lin F ⁅X, Y⁆ = ⁅lin F X, lin F Y⁆ := by
  have hE : ∀ a b : Fin n × Fin n, lin F ⁅E a, E b⁆ = ⁅lin F (E a), lin F (E b)⁆ := by
    intro a b
    rw [LieRing.of_associative_ring_bracket, LieRing.of_associative_ring_bracket, E_mul_sub_mul, lin_E, lin_E,
      hF, map_sub]
    congr 1 <;> split_ifs <;> simp_all [lin_E]
  rw [eq_sum_E X, eq_sum_E Y]
  simp only [sum_lie, lie_sum, smul_lie, lie_smul, map_sum, map_smul, hE]

private noncomputable def lie {A : Type} [Ring A] [Algebra ℂ A] {n : ℕ} (F : Fin n → Fin n → A)
    (hF : Formalism.REAL.GlRel F) : gl n →ₗ⁅ℂ⁆ A :=
  { lin F with map_lie' := fun {X Y} => lin_lie F hF X Y }

end UpperTheory.V.Af.CuspFin.One

open UpperTheory.V.Af.CuspFin UpperTheory.V.Af.CuspFin.One in
theorem UpperTheory.glRelations_hasUniversalProperty :
    ∀ n : ℕ, UpperTheory.V.Af.CuspFin.HasUniv Unit n := by
  intro n
  refine ⟨U n, inferInstance, inferInstance, fun _ i j => e (i, j), ⟨fun _ => ?_, fun v v' h => (h rfl).elim⟩,
    ?_, fun A _ _ E' hE => ?_, ?_⟩
  · intro i j k l
    rw [e_mul_sub_mul]
  · refine eq_top_iff.2 fun u hu => ?_
    clear hu
    induction u using U.induction with
    | halg r => exact Subalgebra.algebraMap_mem _ r
    | hι X =>
      rw [ι_eq_sum_e]
      refine Subalgebra.sum_mem _ fun a _ => Subalgebra.smul_mem _ (Algebra.subset_adjoin ?_) _
      exact ⟨(), a.1, a.2, rfl⟩
    | hmul a b ha hb => exact Subalgebra.mul_mem _ ha hb
    | hadd a b ha hb => exact Subalgebra.add_mem _ ha hb
  · refine ⟨UniversalEnvelopingAlgebra.lift ℂ (lie (E' ()) (hE.1 ())), fun v i j => ?_⟩
    rw [e, UniversalEnvelopingAlgebra.lift_ι_apply]
    exact lin_E (E' ()) (i, j)
  · refine (UpperTheory.center_envelopingGL_le_adjoin_quantumDet n).trans (Algebra.adjoin_mono ?_)
    rintro _ ⟨u, rfl⟩
    exact ⟨(), u, rfl⟩
