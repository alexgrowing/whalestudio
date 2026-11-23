import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.NilpotentLevelLowering.ActUVariableEqPow
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N ValuativeRel IsLocalRing
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil
open UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Hi UpperTheory.V.AlgebraTools UpperTheory.V.Pa UpperTheory.V.Pa.Lev
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem prod_pairs_dvd {A : Type} [CommRing A] {n : ℕ} (u : Fin n → A) (c : A) :
    ∏ p ∈ Hk.pairs n, (u p.2 - c * u p.1) ∣ ∏ i, ∏ i' ∈ Finset.univ.erase i, (u i - u i') * (u i - c * u i') := by
  have h1 : ∏ p ∈ Hk.pairs n, (u p.2 - c * u p.1) =
      ∏ i, ∏ i' ∈ Finset.univ.filter (fun i' => i' < i), (u i - c * u i') := by
    unfold Hk.pairs
    rw [Finset.prod_filter, ← Finset.univ_product_univ, Finset.prod_product_right]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [Finset.prod_filter]
  rw [h1]
  refine Finset.prod_dvd_prod_of_dvd _ _ fun i _ => ?_
  refine (Finset.prod_dvd_prod_of_subset _ (Finset.univ.erase i) _ ?_).trans
    (Finset.prod_dvd_prod_of_dvd _ _ fun i' _ => dvd_mul_left _ _)
  intro i' hi'
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi'
  simp [hi'.ne]

private theorem twoMaps_of_dvd {R B M V : Type} [CommRing R] [CommRing B] [AddCommGroup M] [Module B M] [AddCommGroup V]
    [Module R V] {q n : ℕ} (β : R →+* B) (P : Fin q → Polynomial B) (act : PU R q n →ₐ[R] Module.End R V) {f g : PU R q n}
    (hfg : f ∣ g) (h : TwoMaps (M := M) β P act f) : TwoMaps (M := M) β P act g := by
  obtain ⟨c, rfl⟩ := hfg
  obtain ⟨φ, ψ, h1, h2, h3, h4⟩ := h
  refine ⟨φ, ψ.comp (act c).toAddMonoidHom, h1, fun t v => ?_, fun v => ?_, fun z => ?_⟩
  · show ψ (act c (act t v)) = _ • ψ (act c v)
    rw [← h2, ← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul, mul_comm]
  · show φ (ψ (act c v)) = _
    rw [h3, map_mul, Module.End.mul_apply]
  · show ψ (act c (φ z)) = _
    rw [h2, h4, mul_comm f c, map_mul, map_mul, mul_smul]

theorem UpperTheory.V.Pa.Lev.twoMul :
    ∀ (O R B M V : Type) [CommRing O] [CommRing R] [Algebra O R] [CommRing B] [AddCommGroup M] [Module B M] [AddCommGroup V] [Module R V] (q n : ℕ) (β : R →+* B) (P : Fin q → Polynomial B) (act : PU R q n →ₐ[R] Module.End R V) (Nq : Fin q → ℕ), TwoMaps (M := M) β P act (∏ j, emb O R j (Hk.NN n (Nq j : O))) → TwoMaps (M := M) β P act (fEl Nq fun j i => MvPolynomial.X (j, i)) := by
  intro O R B M V _ _ _ _ _ _ _ _ q n β P act Nq h
  refine twoMaps_of_dvd β P act ?_ h
  unfold fEl
  refine Finset.prod_dvd_prod_of_dvd _ _ fun j _ => ?_
  have e : emb O R j (Hk.NN n (Nq j : O)) = ∏ p ∈ Hk.pairs n,
      ((MvPolynomial.X (j, p.2) : PU R q n) - (Nq j : PU R q n) * MvPolynomial.X (j, p.1)) := by
    unfold Hk.NN
    rw [map_prod]
    refine Finset.prod_congr rfl fun p _ => ?_
    simp [emb]
  rw [e]
  exact prod_pairs_dvd (fun i => (MvPolynomial.X (j, i) : PU R q n)) _
