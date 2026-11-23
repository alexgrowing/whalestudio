import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.FormsFiniteness.OrderedCechToCatCochainsOneApplyValueAtSubset

open NumberField NumberField.mixedEmbedding Matrix MeasureTheory GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm UpperTheory.V.Af.Fin
open scoped TensorProduct
attribute [local instance 100] LieRing.ofAssociativeRing

private theorem aeval_preserves_invariant_submodule {M : Type} [AddCommGroup M] [Module ℂ M] (T : Module.End ℂ M)
    (N : Submodule ℂ M) (hN : ∀ x ∈ N, T x ∈ N) (p : Polynomial ℂ) :
    ∀ x ∈ N, Polynomial.aeval T p x ∈ N := by
  intro x hx
  have hpow : ∀ n : ℕ, ∀ y ∈ N, (T ^ n) y ∈ N := by
    intro n
    induction n with
    | zero =>
      intro y hy
      simpa using hy
    | succ n ih =>
      intro y hy
      rw [pow_succ', Module.End.mul_apply]
      exact hN _ (ih y hy)
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    rw [map_add, LinearMap.add_apply]
    exact N.add_mem hp hq
  | monomial n a =>
    rw [Polynomial.aeval_monomial, Module.End.mul_apply, Module.algebraMap_end_apply]
    exact N.smul_mem a (hpow n x hx)

theorem UpperTheory.finiteDimensional_inf_ker_aeval_monic :
    ∀ (M : Type) [AddCommGroup M] [Module ℂ M] (T : Module.End ℂ M) (N : Submodule ℂ M), (∀ x ∈ N, T x ∈ N) → (∀ c : ℂ, FiniteDimensional ℂ ↥(N ⊓ T.eigenspace c)) → ∀ p : Polynomial ℂ, p.Monic → FiniteDimensional ℂ ↥(N ⊓ LinearMap.ker (Polynomial.aeval T p)) := by
  intro M _ _ T N hN hE p hp
  have key : ∀ s : Multiset ℂ, FiniteDimensional ℂ ↥(N ⊓ LinearMap.ker
      (Polynomial.aeval T (s.map (fun a => Polynomial.X - Polynomial.C a)).prod)) := by
    intro s
    induction s using Multiset.induction_on with
    | empty =>
      rw [Multiset.map_zero, Multiset.prod_zero, map_one]
      have h1 : LinearMap.ker (1 : Module.End ℂ M) = ⊥ := LinearMap.ker_id
      rw [h1, inf_bot_eq]
      infer_instance
    | cons a s ih =>
      set q := (s.map (fun a => Polynomial.X - Polynomial.C a)).prod with hq
      rw [Multiset.map_cons, Multiset.prod_cons]
      rw [← Submodule.fg_iff_finiteDimensional] at ih ⊢
      apply Submodule.fg_of_fg_map_of_fg_inf_ker (f := Polynomial.aeval T q)
      · have hle : (N ⊓ LinearMap.ker (Polynomial.aeval T ((Polynomial.X - Polynomial.C a) * q))).map
            (Polynomial.aeval T q) ≤ N ⊓ T.eigenspace a := by
          rintro _ ⟨x, ⟨hxN, hxk⟩, rfl⟩
          refine ⟨aeval_preserves_invariant_submodule T N hN q x hxN, ?_⟩
          show _ ∈ T.eigenspace a
          rw [Module.End.mem_eigenspace_iff]
          change x ∈ LinearMap.ker _ at hxk
          rw [LinearMap.mem_ker, map_mul, Module.End.mul_apply, map_sub, Polynomial.aeval_X,
            Polynomial.aeval_C, LinearMap.sub_apply, Module.algebraMap_end_apply, sub_eq_zero] at hxk
          exact hxk
        haveI := hE a
        rw [Submodule.fg_iff_finiteDimensional]
        exact Submodule.finiteDimensional_of_le hle
      · apply Submodule.FG.of_le ih
        rintro x ⟨⟨hxN, -⟩, hxq⟩
        exact ⟨hxN, hxq⟩
  have hsplit := Polynomial.prod_multiset_X_sub_C_of_monic_of_roots_card_eq hp IsAlgClosed.card_roots_eq_natDegree
  rw [← hsplit]
  exact key p.roots
