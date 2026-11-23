import Mathlib
import ReciprocityTheory.CommutativeAlgebra.ChainConnInDim
import ReciprocityTheory.CommutativeAlgebra.SaturatedChains.IsSaturatedChain
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.ConnectedPrimeFields.IsWeaklyRegularPairModOneLeft

open IsLocalRing UpperTheory.V.AlgebraTools.Conn

private theorem UpperTheory.V.AlgebraTools.Conn.drop_one {R : Type} [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R] (I : Ideal R) (y : R) (hy : y ∈ maximalIdeal R)
    (hn : ∀ p ∈ I.minimalPrimes, y ∉ p) :
    ringKrullDim (R ⧸ (I ⊔ Ideal.span {y})) + 1 = ringKrullDim (R ⧸ I) := by
  have hy' : y ∈ (Module.annihilator R (R ⧸ I)).jacobson := by
    rw [Ideal.annihilator_quotient]
    exact (IsLocalRing.maximalIdeal_le_jacobson _) hy
  have hn' : ∀ p ∈ (Module.annihilator R (R ⧸ I)).minimalPrimes, y ∉ p := by
    rw [Ideal.annihilator_quotient]
    exact hn
  have key := Module.supportDim_quotSMulTop_succ_eq_of_notMem_minimalPrimes_of_mem_jacobson hn' hy'
  rw [Module.supportDim_quotient_eq_ringKrullDim] at key
  rw [← key, ← Module.supportDim_quotient_eq_ringKrullDim]
  have hs : Module.support R (R ⧸ (I ⊔ Ideal.span {y})) = Module.support R (QuotSMulTop y (R ⧸ I)) := by
    rw [Module.support_quotSMulTop, Module.support_eq_zeroLocus, Module.support_eq_zeroLocus,
      Ideal.annihilator_quotient, Ideal.annihilator_quotient, PrimeSpectrum.zeroLocus_sup,
      PrimeSpectrum.zeroLocus_span]
  simp only [Module.supportDim]
  rw [hs]

private theorem UpperTheory.V.AlgebraTools.Conn.max_notMem_minimalPrimes {R : Type} [CommRing R] [IsLocalRing R]
    (I : Ideal R) (h : 0 < ringKrullDim (R ⧸ I)) : maximalIdeal R ∉ I.minimalPrimes := by
  intro hm
  rw [ringKrullDim_quotient, Order.krullDim_pos_iff] at h
  obtain ⟨a, b, hab⟩ := h
  have ha : I ≤ a.1.asIdeal := a.2
  have hma : maximalIdeal R ≤ a.1.asIdeal :=
    hm.2 ⟨a.1.isPrime, ha⟩ (IsLocalRing.le_maximalIdeal a.1.isPrime.ne_top)
  have hbm : b.1.asIdeal ≤ maximalIdeal R := IsLocalRing.le_maximalIdeal b.1.isPrime.ne_top
  have hlt : a.1.asIdeal < b.1.asIdeal := hab
  exact absurd (hbm.trans hma) (not_le_of_gt hlt)

theorem UpperTheory.V.AlgebraTools.Conn.drop :
    ∀ {A R : Type} [CommRing A] [IsLocalRing A] [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [Algebra A R]
      [Algebra.IsIntegral A R] (S : Finset (Ideal R)), (∀ I ∈ S, 0 < ringKrullDim (R ⧸ I)) →
      ∃ x ∈ maximalIdeal A, ∀ I ∈ S, ringKrullDim (R ⧸ (I ⊔ Ideal.span {algebraMap A R x})) + 1 = ringKrullDim (R ⧸ I) := by
  intro A R _ _ _ _ _ _ _ S hS
  classical
  let T : Set (Ideal A) := ⋃ I ∈ S, (Ideal.comap (algebraMap A R)) '' I.minimalPrimes
  have hT : T.Finite := Set.Finite.biUnion S.finite_toSet
    (fun I _ => (Ideal.finite_minimalPrimes_of_isNoetherianRing R I).image _)
  have memT : ∀ q, q ∈ T ↔ ∃ I ∈ S, ∃ p ∈ I.minimalPrimes, Ideal.comap (algebraMap A R) p = q := by
    intro q
    simp only [T, Set.mem_iUnion, Set.mem_image, exists_prop]
  have hmA : Ideal.comap (algebraMap A R) (maximalIdeal R) = maximalIdeal A :=
    IsLocalRing.eq_maximalIdeal (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal _)
  have hTprime : ∀ q ∈ T, q.IsPrime := by
    intro q hq
    obtain ⟨I, _, p, hp, rfl⟩ := (memT q).mp hq
    haveI := hp.1.1
    infer_instance
  have hnot : ¬ ∃ q ∈ hT.toFinset, maximalIdeal A ≤ id q := by
    rintro ⟨q, hq, hle⟩
    obtain ⟨I, hI, p, hp, rfl⟩ := (memT _).mp (hT.mem_toFinset.mp hq)
    haveI := hp.1.1
    have heq : maximalIdeal A = Ideal.comap (algebraMap A R) p :=
      (IsLocalRing.maximalIdeal.isMaximal A).eq_of_le Ideal.IsPrime.ne_top' hle
    haveI : (Ideal.comap (algebraMap A R) p).IsMaximal := heq ▸ IsLocalRing.maximalIdeal.isMaximal A
    have hpm : p = maximalIdeal R :=
      IsLocalRing.eq_maximalIdeal (Ideal.isMaximal_of_isIntegral_of_isMaximal_comap p this)
    exact UpperTheory.V.AlgebraTools.Conn.max_notMem_minimalPrimes I (hS I hI) (hpm ▸ hp)
  have hsub := (Ideal.subset_union_prime (s := hT.toFinset) (f := id) ⊥ ⊥
    (fun q hq _ _ => hTprime q (hT.mem_toFinset.mp hq)) (I := maximalIdeal A)).not.mpr hnot
  obtain ⟨x, hxm, hx⟩ := Set.not_subset.mp hsub
  refine ⟨x, hxm, fun I hI => UpperTheory.V.AlgebraTools.Conn.drop_one I _ ?_ ?_⟩
  · have hx' : x ∈ Ideal.comap (algebraMap A R) (maximalIdeal R) := hmA ▸ hxm
    exact hx'
  · intro p hp hxp
    apply hx
    simp only [Set.mem_iUnion, id]
    exact ⟨Ideal.comap (algebraMap A R) p, hT.mem_toFinset.mpr ((memT _).mpr ⟨I, hI, p, hp, rfl⟩), hxp⟩
