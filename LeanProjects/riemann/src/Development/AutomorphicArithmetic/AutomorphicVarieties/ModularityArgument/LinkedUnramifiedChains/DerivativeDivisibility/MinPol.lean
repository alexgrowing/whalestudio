import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.CmpPrime

open Polynomial TensorProduct

namespace UpperTheory.V.J

private lemma aeval_actL {O Λ B : Type} [CommRing O] [CommRing Λ] [CommRing B] [Algebra O Λ] [Algebra O B]
    (lam : Λ →ₐ[O] B) (M : Type) [AddCommGroup M] [Module B M] [Module Λ M]
    (hs : ∀ (a : Λ) (m : M), a • m = lam a • m) (t : B) (p : Λ[X]) (m : M) :
    (aeval (actL lam M hs t) p) m = (p.eval₂ (lam : Λ →+* B) t) • m := by
  induction p using Polynomial.induction_on generalizing m with
  | C a =>
    rw [aeval_C, eval₂_C, Module.algebraMap_end_apply]
    exact hs a m
  | add p q hp hq =>
    rw [map_add, LinearMap.add_apply, hp, hq, eval₂_add, add_smul]
  | monomial n a ih =>
    have e : (C a * X ^ (n + 1) : Λ[X]) = (C a * X ^ n) * X := by rw [pow_succ, mul_assoc]
    rw [e, map_mul, aeval_X, Module.End.mul_apply, ih, eval₂_mul (p := C a * X ^ n) (q := X), eval₂_X, mul_smul]
    rfl

private lemma dvd_of_aeval {Λ M : Type} [CommRing Λ] [IsDomain Λ] [AddCommGroup M] [Module Λ M]
    [Module.Free Λ M] [Module.Finite Λ M] (T : Module.End Λ M) (g q : Λ[X]) (hm : g.Monic)
    (hi : Irreducible (g.map (algebraMap Λ (FractionRing Λ)))) (hd : g ∣ T.charpoly) (N : ℕ)
    (h : aeval T (q ^ N) = 0) : g ∣ q := by
  let F := FractionRing Λ
  let L := AlgebraicClosure F
  have hinj : Function.Injective (algebraMap Λ F) := IsFractionRing.injective Λ F
  rw [← Polynomial.map_dvd_map (algebraMap Λ F) hinj hm]
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_aeval_eq_zero L (g.map (algebraMap Λ F)) (degree_pos_of_irreducible hi).ne'
  have hzg : aeval z g = 0 := by rwa [aeval_map_algebraMap] at hz
  have hroot : (T.baseChange L).charpoly.IsRoot z := by
    rw [LinearMap.charpoly_baseChange, IsRoot.def, eval_map_algebraMap]
    obtain ⟨r, hr⟩ := hd
    rw [hr, map_mul, hzg, zero_mul]
  have hev : Module.End.HasEigenvalue (T.baseChange L) z :=
    Module.End.hasEigenvalue_iff_isRoot_charpoly _ _ |>.2 hroot
  obtain ⟨v, hv⟩ := hev.exists_hasEigenvector
  have hbc : (aeval T (q ^ N)).baseChange L = aeval (T.baseChange L) (q ^ N) :=
    (aeval_algHom_apply (Module.End.baseChangeHom Λ L M) T (q ^ N)).symm
  have hq : aeval z q = 0 := by
    have h1 : (aeval (T.baseChange L) (q ^ N)) v = (aeval z (q ^ N)) • v := by
      rw [← aeval_map_algebraMap L, Module.End.aeval_apply_of_hasEigenvector hv, eval_map_algebraMap]
    rw [← hbc, h, LinearMap.baseChange_zero, LinearMap.zero_apply, map_pow] at h1
    rcases smul_eq_zero.1 h1.symm with h2 | h2
    · exact (pow_eq_zero_iff (n := N) (by rintro rfl; simp at h2)).1 h2
    · exact absurd h2 hv.2
  have hint : IsIntegral F z := Algebra.IsIntegral.isIntegral z
  have hmin : minpoly F z ∣ g.map (algebraMap Λ F) := minpoly.dvd F z hz
  have hmq : minpoly F z ∣ q.map (algebraMap Λ F) := minpoly.dvd F z (by rwa [aeval_map_algebraMap])
  exact ((minpoly.irreducible hint).dvd_symm hi hmin).trans hmq

theorem minPol : MinPol := by
  intro O Λ B _ _ _ _ _ _ lam J M _ _ _ _ _ h t s g m hf
  have hJrad : J ≤ (Module.annihilator B M).radical := by
    rw [Ideal.radical_eq_sInf]
    refine le_sInf ?_
    rintro p ⟨hp, hprime⟩
    exact (h.supp p hprime).1 hp
  have hann : Module.annihilator B M ≤ J := by
    rw [← h.rad.radical, Ideal.radical_eq_sInf]
    refine le_sInf ?_
    rintro p ⟨hp, hprime⟩
    exact (h.supp p hprime).2 hp
  have hχ : (actL lam M h.hs t).charpoly.eval₂ (lam : Λ →+* B) t ∈ J := by
    refine hann (Module.mem_annihilator.2 fun x => ?_)
    rw [← aeval_actL lam M h.hs t, LinearMap.aeval_self_charpoly, LinearMap.zero_apply]
  refine ⟨?_, ?_⟩
  · have hdvd : (actL lam M h.hs t).charpoly ∣ (∏ i, g i) ^ (∑ i, m i) := by
      rw [hf.prod, ← Finset.prod_pow]
      exact Finset.prod_dvd_prod_of_dvd _ _ fun i _ =>
        pow_dvd_pow _ (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i))
    obtain ⟨r, hr⟩ := hdvd
    refine h.rad ⟨∑ i, m i, ?_⟩
    rw [← eval₂_pow, hr, eval₂_mul]
    exact J.mul_mem_right _ hχ
  · intro q hq i
    obtain ⟨N, hN⟩ := hJrad hq
    have hzero : aeval (actL lam M h.hs t) (q ^ N) = 0 := by
      refine LinearMap.ext fun x => ?_
      rw [aeval_actL, eval₂_pow, LinearMap.zero_apply]
      exact Module.mem_annihilator.1 hN x
    have hd : g i ∣ (actL lam M h.hs t).charpoly := by
      rw [hf.prod]
      exact (dvd_pow_self _ (by have := hf.pos i; omega)).trans
        (Finset.dvd_prod_of_mem (fun j => g j ^ m j) (Finset.mem_univ i))
    exact dvd_of_aeval _ (g i) q (hf.monic i) (hf.irr i) hd N hzero

end UpperTheory.V.J
