import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.FinDefs
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.UniversalOrdinaryDeterminantRing
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.UGenApprox
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.DGext
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.DGmap
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.PairMap

open TensorProduct IsLocalRing Polynomial UpperTheory.V.W UpperTheory.V.Alg UpperTheory.V.CA

theorem UpperTheory.V.CA.exists_adjoin_coeff_character_sub_mem_maximalIdeal_pow :
    ∀ {l : ℕ} [Fact l.Prime] {F : GFrame l} {O : Type} [CommRing O] [IsLocalRing O] [IsNoetherianRing O] [IsAdicComplete (maximalIdeal O) O] [Finite (ResidueField O)] [CharP (ResidueField O) l] [Algebra ℤ_[l] O] {n : ℕ} (r : Resid F O n) (B : UniversalOrdinaryDeterminantRing r) (N : ℕ) (x : B.B), ∃ y ∈ Algebra.adjoin O ({a | ∃ (i : ℕ) (g : F.G₀), 1 ≤ i ∧ i ≤ n ∧ a = B.u.D.lam i (MonoidAlgebra.single g 1)} ∪ {a | ∃ v i g, a = ((B.u.ψ v i g : B.Bˣ) : B.B)}), x - y ∈ maximalIdeal B.B ^ N := by
  intro l _ F O _ _ _ _ _ _ _ n r B N x
  refine u_gen O B.B _ ?_ N x
  intro R' _ _ _ f f' h
  obtain ⟨p, hp⟩ := pair_map r B.u f
  refine (B.univ R' p).unique hp ⟨?_, fun v i => ?_⟩
  · rw [← hp.1]
    refine d_gext _ _ fun g i h1 h2 => ?_
    have e : ∀ φ : B.B →+* R', (B.u.D.map φ).lam i (MonoidAlgebra.single g 1) =
        φ (B.u.D.lam i (MonoidAlgebra.single g 1)) := fun φ => by
      have := ((d_gmap B.u.D).2.2.1 φ (MonoidAlgebra.single g 1)).2 i
      rwa [MonoidAlgebra.mapRingHom_single, map_one] at this
    rw [e, e]
    exact (h _ (Or.inl ⟨i, g, h1, h2, rfl⟩)).symm
  · rw [← hp.2 v i]
    ext g
    exact (h _ (Or.inr ⟨v, i, g, rfl⟩)).symm
