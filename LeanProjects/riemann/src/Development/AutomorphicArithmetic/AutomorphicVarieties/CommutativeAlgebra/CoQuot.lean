import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ResMapBijective

open IsLocalRing MvPowerSeries UpperTheory.V.Alg

private theorem prec_of_surj {R R' : Type} [CommRing R] [CommRing R'] (p : R →+* R')
    (hp : Function.Surjective p) (I : Ideal R) [IsPrecomplete I R] : IsPrecomplete (I.map p) R' := ⟨fun f hf => by
  have hd : ∀ n, ∃ d ∈ I ^ n, p d = f (n + 1) - f n := fun n => by
    have h := (hf (Nat.le_succ n)).symm
    rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, ← Ideal.map_pow] at h
    exact (Ideal.mem_map_iff_of_surjective p hp).1 h
  choose d hdI hd using hd
  obtain ⟨x, hx⟩ := hp (f 0)
  have hg : ∀ n, p (x + ∑ i ∈ Finset.range n, d i) = f n := fun n => by
    induction n with
    | zero => simpa using hx
    | succ n ih => rw [Finset.sum_range_succ, ← add_assoc, map_add, ih, hd]; ring
  obtain ⟨L, hL⟩ := IsPrecomplete.prec' (I := I) (fun n => x + ∑ i ∈ Finset.range n, d i) (fun {m n} hmn => by
    apply SModEq.symm
    rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, add_sub_add_left_eq_sub, ← Finset.sum_Ico_eq_sub _ hmn]
    exact Ideal.sum_mem _ fun i hi => Ideal.pow_le_pow_right (Finset.mem_Ico.1 hi).1 (hdI i))
  refine ⟨p L, fun n => ?_⟩
  have h := hL n
  rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top] at h ⊢
  rw [← hg n, ← map_sub, ← Ideal.map_pow]
  exact Ideal.mem_map_of_mem p h⟩

theorem UpperTheory.V.Alg.co_quot :
    ∀ (O : Type) [CommRing O] [IsLocalRing O] (R : Type) [CommRing R] [Algebra O R] [IsCO O R] (R' : Type) [CommRing R'] [Algebra O R'] [Nontrivial R'] (p : R →ₐ[O] R'), Function.Surjective p → IsCO O R' := by
  intro O _ _ R _ _ _ R' _ _ _ p hp
  have hp' : Function.Surjective (p : R →+* R') := hp
  haveI hL : IsLocalRing R' := IsLocalRing.of_surjective' (p : R →+* R') hp'
  haveI hN : IsNoetherianRing R' := isNoetherianRing_of_surjective R R' (p : R →+* R') hp'
  haveI hH : IsLocalHom (p : R →+* R') := IsLocalHom.of_surjective _ hp'
  have hm : (maximalIdeal R).map (p : R →+* R') = maximalIdeal R' :=
    IsLocalRing.map_maximalIdeal_of_surjective _ hp'
  have hP : IsPrecomplete (maximalIdeal R') R' := hm ▸ prec_of_surj (p : R →+* R') hp' (maximalIdeal R)
  refine { complete := { toIsHausdorff := inferInstance, toIsPrecomplete := hP }
           isLocalHom := ⟨fun a ha => ?_⟩
           res_surj := fun y => ?_ }
  · rw [← p.commutes] at ha
    exact IsLocalHom.map_nonunit (f := algebraMap O R) a (IsLocalHom.map_nonunit (f := (p : R →+* R')) _ ha)
  · obtain ⟨x, rfl⟩ := hp y
    obtain ⟨a, ha⟩ := IsCO.res_surj (O := O) x
    refine ⟨a, ?_⟩
    rw [← p.commutes, ← map_sub, ← hm]
    exact Ideal.mem_map_of_mem _ ha
