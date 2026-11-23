import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.CrystallineTowers.LocTower
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.SplitsBasic

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC GlobalTheory.GalV UpperTheory.Gal.Int.Geo TensorProduct

theorem UpperTheory.exists_algEquiv_restrict_hom_of_algebraMap_compat :
    ∀ (k K Ω Ω' : Type) [Field k] [Field K] [Field Ω] [Field Ω'] [Algebra k Ω] [IsAlgClosure k Ω] [Algebra K Ω'] (τ : k →+* K) (j : Ω →+* Ω'), (∀ x, j (algebraMap k Ω x) = algebraMap K Ω' (τ x)) → ∃ r : (Ω' ≃ₐ[K] Ω') →* (Ω ≃ₐ[k] Ω), ∀ σ' x, σ' (j x) = j (r σ' x) := by
  intro k K Ω Ω' _ _ _ _ _ _ _ τ j hj
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed k
  have key : ∀ (s : Ω' ≃ₐ[K] Ω') (x : Ω), ∃ y, s (j x) = j y := by
    intro s x
    have hint : IsIntegral k x := Algebra.IsIntegral.isIntegral x
    have hP : ((minpoly k x).map (algebraMap k Ω)).Splits := IsAlgClosed.splits _
    have hPm : ((minpoly k x).map (algebraMap k Ω)).map j = ((minpoly k x).map τ).map (algebraMap K Ω') := by
      rw [Polynomial.map_map, Polynomial.map_map]
      congr 1
      ext c
      exact hj c
    have hne : ((minpoly k x).map (algebraMap k Ω)).map j ≠ 0 :=
      Polynomial.map_ne_zero (Polynomial.map_ne_zero (minpoly.ne_zero hint))
    have h0 : (((minpoly k x).map (algebraMap k Ω)).map j).eval (j x) = 0 := by
      rw [Polynomial.eval_map, Polynomial.eval₂_hom, Polynomial.eval_map_algebraMap, minpoly.aeval, map_zero]
    have hroot : s (j x) ∈ (((minpoly k x).map (algebraMap k Ω)).map j).roots := by
      rw [Polynomial.mem_roots hne]
      show Polynomial.eval _ _ = 0
      rw [hPm, Polynomial.eval_map_algebraMap,
        show s (j x) = (s : Ω' →ₐ[K] Ω') (j x) from rfl, Polynomial.aeval_algHom_apply,
        ← Polynomial.eval_map_algebraMap, ← hPm, h0, map_zero]
    rw [hP.roots_map_of_ne_zero hne, Multiset.mem_map] at hroot
    obtain ⟨y, -, hy⟩ := hroot
    exact ⟨y, hy.symm⟩
  choose g hg using key
  have hji : Function.Injective j := j.injective
  let gA : (Ω' ≃ₐ[K] Ω') → (Ω →ₐ[k] Ω) := fun s =>
    { toFun := g s
      map_one' := hji (by rw [← hg]; simp only [map_one])
      map_mul' := fun a b => hji (by rw [← hg]; simp only [map_mul, hg])
      map_zero' := hji (by rw [← hg]; simp only [map_zero])
      map_add' := fun a b => hji (by rw [← hg]; simp only [map_add, hg])
      commutes' := fun c => hji (by rw [← hg, hj, AlgEquiv.commutes]) }
  let r : (Ω' ≃ₐ[K] Ω') → (Ω ≃ₐ[k] Ω) := fun s => (Algebra.IsAlgebraic.algEquivEquivAlgHom k Ω).symm (gA s)
  have hr : ∀ s x, r s x = g s x := fun s x => rfl
  refine ⟨{ toFun := r, map_one' := ?_, map_mul' := ?_ }, ?_⟩
  · ext x
    apply hji
    rw [hr, ← hg]
    simp
  · intro s t
    ext x
    apply hji
    rw [hr, ← hg, AlgEquiv.mul_apply, AlgEquiv.mul_apply, hr, hr]
    simp only [hg]
  · intro s x
    show s (j x) = j (r s x)
    rw [hr, hg]
