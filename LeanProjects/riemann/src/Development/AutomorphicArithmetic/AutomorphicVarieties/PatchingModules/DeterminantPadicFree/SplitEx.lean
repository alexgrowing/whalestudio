import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DeterminantPadicFree.FrameWith
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.CaDvrIc

open Matrix IsLocalRing UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa

private theorem exists_injective_roots_in_integral_closure {A L : Type} [CommRing A] [Field L] [Algebra A L] {n : ℕ} (p : Polynomial A)
    (hm : p.Monic) (hn : (p.map (algebraMap A L)).natDegree = n) (hsep : (p.map (algebraMap A L)).Separable)
    (hs : (p.map (algebraMap A L)).Splits) :
    ∃ al : Fin n → integralClosure A L, Function.Injective al ∧
      p.map (algebraMap A (integralClosure A L)) = ∏ b, (Polynomial.X - Polynomial.C (al b)) := by
  classical
  set pL := p.map (algebraMap A L) with hpL
  have hmL : pL.Monic := hm.map _
  have hroots : pL = (pL.roots.map fun x => Polynomial.X - Polynomial.C x).prod :=
    hs.eq_prod_roots_of_monic hmL
  have hnd : pL.roots.Nodup := Polynomial.nodup_roots hsep
  set s := pL.roots.toFinset with hsdef
  have hcard : s.card = n := by
    rw [hsdef, Multiset.toFinset_card_of_nodup hnd, ← hs.natDegree_eq_card_roots, hn]
  have hint : ∀ x ∈ s, x ∈ integralClosure A L := by
    intro x hx
    rw [hsdef, Multiset.mem_toFinset, Polynomial.mem_roots hmL.ne_zero, Polynomial.IsRoot,
      hpL, Polynomial.eval_map] at hx
    exact ⟨p, hm, hx⟩
  let e : Fin n ≃ s := (s.equivFin.trans (finCongr hcard)).symm
  refine ⟨fun b => ⟨(e b : L), hint _ (e b).2⟩, ?_, ?_⟩
  · intro b b' h
    have h2 := congrArg Subtype.val h
    exact e.injective (Subtype.ext h2)
  · apply Polynomial.map_injective (integralClosure A L).val.toRingHom Subtype.val_injective
    rw [Polynomial.map_map, Polynomial.map_prod]
    have h1 : ((integralClosure A L).val.toRingHom).comp (algebraMap A (integralClosure A L)) =
        algebraMap A L := by
      ext a
      rfl
    rw [h1]
    change pL = _
    simp only [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C]
    rw [hroots]
    have h3 : ∏ b : Fin n, (Polynomial.X - Polynomial.C ((e b : L))) =
        ∏ x ∈ s, (Polynomial.X - Polynomial.C x) := by
      rw [Equiv.prod_comp e (fun x : s => Polynomial.X - Polynomial.C (x : L))]
      exact Finset.prod_coe_sort s (fun x => Polynomial.X - Polynomial.C x)
    convert h3.symm using 1
    · rw [Finset.prod_eq_multiset_prod, hsdef, Multiset.toFinset_val, hnd.dedup]
    · rfl

theorem UpperTheory.V.Pa.Det.splitEx :
    ∀ (l : ℕ) [Fact l.Prime] {K : Type} [Field K] [Finite K] [CharP K l] {q n : ℕ} (P : Fin q → Polynomial (PowerSeries K)), (∀ a, (P a).Monic ∧ (P a).natDegree = n ∧ ((P a).map (algebraMap (PowerSeries K) (FractionRing (PowerSeries K)))).Separable) → ∃ (A' : Type) (_ : CommRing A') (_ : IsDomain A') (_ : IsDiscreteValuationRing A') (_ : IsEqDVR l A') (j : PowerSeries K →+* A') (al : Fin q → Fin n → A'), Function.Injective j ∧ IsLocalHom j ∧ j.Finite ∧ ∀ a, Function.Injective (al a) ∧ (P a).map j = ∏ b, (Polynomial.X - Polynomial.C (al a b)) := by
  intro l _ K _ _ _ q n P hP
  classical
  have hQ0 : (∏ a, (P a).map (algebraMap (PowerSeries K) (FractionRing (PowerSeries K)))) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun a _ => ((hP a).1.map _).ne_zero
  haveI hsepE : Algebra.IsSeparable (FractionRing (PowerSeries K)) (Polynomial.SplittingField (∏ a, (P a).map (algebraMap (PowerSeries K) (FractionRing (PowerSeries K))))) := by
    rw [← IntermediateField.isSeparable_top,
      ← (isSplittingField_iff_intermediateField.mp
        (inferInstance : Polynomial.IsSplittingField (FractionRing (PowerSeries K)) (Polynomial.SplittingField (∏ a, (P a).map (algebraMap (PowerSeries K) (FractionRing (PowerSeries K))))) (∏ a, (P a).map (algebraMap (PowerSeries K) (FractionRing (PowerSeries K)))))).2,
      IntermediateField.isSeparable_adjoin_iff_isSeparable]
    intro x hx
    have h0 := Polynomial.aeval_eq_zero_of_mem_rootSet hx
    rw [map_prod, Finset.prod_eq_zero_iff] at h0
    obtain ⟨a, _, ha⟩ := h0
    exact (hP a).2.2.of_dvd (minpoly.dvd (FractionRing (PowerSeries K)) x ha)
  haveI hcA : IsAdicComplete (IsLocalRing.maximalIdeal (PowerSeries K)) (PowerSeries K) := by
    rw [PowerSeries.maximalIdeal_eq_span_X]
    infer_instance
  have hfinA : Finite (IsLocalRing.ResidueField (PowerSeries K)) :=
    Finite.of_equiv K (PowerSeries.residueFieldOfPowerSeries).symm.toEquiv
  set_option synthInstance.maxHeartbeats 400000 in
  obtain ⟨hfin, _, _, hdvr, hcB, hloc, hres⟩ :=
    UpperTheory.V.AlgebraTools.integralClosure_complete_dvr (PowerSeries K) (FractionRing (PowerSeries K)) (Polynomial.SplittingField (∏ a, (P a).map (algebraMap (PowerSeries K) (FractionRing (PowerSeries K))))) ↥(integralClosure (PowerSeries K) (Polynomial.SplittingField (∏ a, (P a).map (algebraMap (PowerSeries K) (FractionRing (PowerSeries K))))))
  have hinjAE : Function.Injective (algebraMap (PowerSeries K) (Polynomial.SplittingField (∏ a, (P a).map (algebraMap (PowerSeries K) (FractionRing (PowerSeries K)))))) := by
    rw [IsScalarTower.algebraMap_eq (PowerSeries K) (FractionRing (PowerSeries K)) (Polynomial.SplittingField (∏ a, (P a).map (algebraMap (PowerSeries K) (FractionRing (PowerSeries K)))))]
    exact (algebraMap (FractionRing (PowerSeries K)) (Polynomial.SplittingField (∏ a, (P a).map (algebraMap (PowerSeries K) (FractionRing (PowerSeries K)))))).injective.comp (IsFractionRing.injective (PowerSeries K) (FractionRing (PowerSeries K)))
  have hj : Function.Injective (algebraMap (PowerSeries K) ↥(integralClosure (PowerSeries K) (Polynomial.SplittingField (∏ a, (P a).map (algebraMap (PowerSeries K) (FractionRing (PowerSeries K))))))) := by
    intro x y h
    apply hinjAE
    exact congrArg Subtype.val h
  haveI hcharA : CharP (PowerSeries K) l := charP_of_injective_ringHom (PowerSeries.C (R := K)).injective l
  haveI hcharB : CharP ↥(integralClosure (PowerSeries K) (Polynomial.SplittingField (∏ a, (P a).map (algebraMap (PowerSeries K) (FractionRing (PowerSeries K)))))) l := charP_of_injective_ringHom hj l
  have hal : ∀ a, ∃ al : Fin n → ↥(integralClosure (PowerSeries K) (Polynomial.SplittingField (∏ a, (P a).map (algebraMap (PowerSeries K) (FractionRing (PowerSeries K)))))), Function.Injective al ∧
      (P a).map (algebraMap (PowerSeries K) ↥(integralClosure (PowerSeries K) (Polynomial.SplittingField (∏ a, (P a).map (algebraMap (PowerSeries K) (FractionRing (PowerSeries K))))))) = ∏ b, (Polynomial.X - Polynomial.C (al b)) := by
    intro a
    have hdeg : ((P a).map (algebraMap (PowerSeries K) (Polynomial.SplittingField (∏ a, (P a).map (algebraMap (PowerSeries K) (FractionRing (PowerSeries K))))))).natDegree = n := by
      rw [(hP a).1.natDegree_map]
      exact (hP a).2.1
    have hmapE : (P a).map (algebraMap (PowerSeries K) (Polynomial.SplittingField (∏ a, (P a).map (algebraMap (PowerSeries K) (FractionRing (PowerSeries K)))))) =
        ((P a).map (algebraMap (PowerSeries K) (FractionRing (PowerSeries K)))).map (algebraMap (FractionRing (PowerSeries K)) (Polynomial.SplittingField (∏ a, (P a).map (algebraMap (PowerSeries K) (FractionRing (PowerSeries K)))))) := by
      rw [Polynomial.map_map, ← IsScalarTower.algebraMap_eq]
    have hsepa : ((P a).map (algebraMap (PowerSeries K) (Polynomial.SplittingField (∏ a, (P a).map (algebraMap (PowerSeries K) (FractionRing (PowerSeries K))))))).Separable := by
      rw [hmapE]
      exact (hP a).2.2.map
    have hspl : ((P a).map (algebraMap (PowerSeries K) (Polynomial.SplittingField (∏ a, (P a).map (algebraMap (PowerSeries K) (FractionRing (PowerSeries K))))))).Splits := by
      rw [hmapE]
      refine Polynomial.Splits.of_dvd (Polynomial.SplittingField.splits (∏ a, (P a).map (algebraMap (PowerSeries K) (FractionRing (PowerSeries K)))))
        (Polynomial.map_ne_zero hQ0) ?_
      exact Polynomial.map_dvd _ (Finset.dvd_prod_of_mem _ (Finset.mem_univ a))
    exact exists_injective_roots_in_integral_closure (P a) (hP a).1 hdeg hsepa hspl
  choose al hal1 hal2 using hal
  exact ⟨↥(integralClosure (PowerSeries K) (Polynomial.SplittingField (∏ a, (P a).map (algebraMap (PowerSeries K) (FractionRing (PowerSeries K)))))), inferInstance, inferInstance, hdvr, ⟨hcB, hres hfinA, hcharB⟩, algebraMap (PowerSeries K) ↥(integralClosure (PowerSeries K) (Polynomial.SplittingField (∏ a, (P a).map (algebraMap (PowerSeries K) (FractionRing (PowerSeries K)))))), al,
    hj, hloc, RingHom.finite_algebraMap.mpr hfin, fun a => ⟨hal1 a, hal2 a⟩⟩
