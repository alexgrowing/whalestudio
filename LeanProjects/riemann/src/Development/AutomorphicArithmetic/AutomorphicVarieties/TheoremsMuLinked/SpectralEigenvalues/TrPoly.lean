import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.TraceIntegralSubringExtension

open IsLocalRing Polynomial

theorem UpperTheory.V.Th.Sp.trp :
    ∀ (O : Type) [CommRing O] [IsDomain O] (n : ℕ) (A : Matrix (Fin n) (Fin n) O) (α : Fin n → O) (p : O[X]), A.charpoly = ∏ i, (X - C (α i)) → (aeval A p).trace = ∑ i, p.eval (α i) := by
  intro O _ _ n A α p h
  let K := AlgebraicClosure (FractionRing O)
  let f : O →+* K := (algebraMap (FractionRing O) K).comp (algebraMap O (FractionRing O))
  have hf : Function.Injective f :=
    (algebraMap (FractionRing O) K).injective.comp (IsFractionRing.injective O (FractionRing O))
  apply hf
  have htr : ∀ M : Matrix (Fin n) (Fin n) O, f M.trace = (M.map f).trace := by
    intro M
    simp [Matrix.trace, map_sum]
  have haeval : (aeval A p).map f = aeval (A.map f) (p.map f) := by
    have := Polynomial.map_aeval_eq_aeval_map (φ := f) (ψ := f.mapMatrix) ?_ p A
    · simpa using this
    · ext c i j
      simp [Matrix.algebraMap_matrix_apply]
      split_ifs <;> simp
  have hchar : (A.map f).charpoly = ((Finset.univ.val.map fun i => f (α i)).map fun a => X - C a).prod := by
    rw [Matrix.charpoly_map, h, Polynomial.map_prod]
    simp [Finset.prod_eq_multiset_prod, Multiset.map_map, Function.comp_def]
  rw [htr, haeval, GlobalTheory.CompanionTheory.TraceSpec.trace_aeval_matrix, hchar, Polynomial.roots_multiset_prod_X_sub_C, map_sum]
  simp [Multiset.map_map, Finset.sum_eq_multiset_sum, Function.comp_def]
