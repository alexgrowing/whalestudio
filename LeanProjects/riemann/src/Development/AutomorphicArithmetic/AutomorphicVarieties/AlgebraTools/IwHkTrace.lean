import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.HeckePairTop
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.IwHkApply
open ValuativeRel Matrix GlobalTheory.SmGL GlobalTheory.SplitWeil UpperTheory.V.Hi UpperTheory.V.AlgebraTools

private theorem double_coset_operator_sum {A G M : Type} [CommRing A] [Group G] [AddCommGroup M] [Module A M] (ρ : Representation A G M)
    (K K' : Subgroup G) (x : G) (h : (MulAction.orbit K (x : G ⧸ K')).Finite) (v : fixd ρ K') :
    (hk2 ρ K K' x v : M) = ∑ q ∈ Set.Finite.toFinset h, ρ q.out v := by
  rw [(hkApply A G M ρ K K' x h).1 v, dc,
    finsum_set_coe_eq_finsum_mem (f := fun q : G ⧸ K' => ρ q.out), finsum_mem_eq_finite_toFinset_sum _ h,
    LinearMap.sum_apply]

private theorem mem_orb {G : Type} [Group G] (K K' : Subgroup G) (x g : G) :
    (g : G ⧸ K') ∈ MulAction.orbit K (x : G ⧸ K') ↔ ∃ a ∈ K, ∃ b ∈ K', g = a * x * b := by
  constructor
  · rintro ⟨a, ha⟩
    have ha' : (((a : G) * x : G) : G ⧸ K') = g := ha
    exact ⟨a, a.2, _, QuotientGroup.eq.1 ha', by group⟩
  · rintro ⟨a, ha, b, hb, rfl⟩
    refine ⟨⟨a, ha⟩, ?_⟩
    change ((a * x : G) : G ⧸ K') = _
    exact (QuotientGroup.mk_mul_of_mem _ hb).symm

theorem UpperTheory.V.AlgebraTools.hkTrace :
    ∀ (A G M : Type) [CommRing A] [Group G] [AddCommGroup M] [Module A M] (ρ : Representation A G M) (I K : Subgroup G) (h : I ≤ K) (ι : Type) [Fintype ι] (w : ι → G), HeckePair I → (∀ i, w i ∈ K) → (∀ g ∈ K, ∃! i, ∃ a ∈ I, ∃ b ∈ I, g = a * w i * b) → FinOrb K I 1 ∧ ∑ i, hk ρ I (w i) = inc ρ h ∘ₗ trc ρ K I ∧ ∀ v : fixd ρ K, trc ρ K I (inc ρ h v) = (I.relIndex K : A) • v := by
  intro A G M _ _ _ _ ρ I K h ι _ w hI hw hu
  classical
  replace hI : ∀ x : G, (MulAction.orbit I (x : G ⧸ I)).Finite := hI
  have hK : ∀ g : G, (g : G ⧸ I) ∈ MulAction.orbit K ((1 : G) : G ⧸ I) ↔ g ∈ K := fun g => by
    rw [mem_orb]
    exact ⟨fun ⟨a, ha, b, hb, e⟩ => e ▸ mul_mem (mul_mem ha (one_mem _)) (h hb),
      fun hg => ⟨g, hg, 1, one_mem _, by simp⟩⟩
  have hU : MulAction.orbit K ((1 : G) : G ⧸ I) = ⋃ i, MulAction.orbit I (w i : G ⧸ I) := by
    ext q
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
    simp only [Set.mem_iUnion, hK, mem_orb]
    exact ⟨fun hg => (hu g hg).exists,
      fun ⟨i, a, ha, b, hb, e⟩ => e ▸ mul_mem (mul_mem (h ha) (hw i)) (h hb)⟩
  have hF : (MulAction.orbit K ((1 : G) : G ⧸ I)).Finite := by
    rw [hU]
    exact Set.finite_iUnion fun i => hI (w i)
  refine ⟨hF, ?_, fun v => ?_⟩
  · ext v
    change _ = (hk2 ρ K I 1 v : M)
    rw [LinearMap.sum_apply, Submodule.coe_sum, double_coset_operator_sum ρ K I 1 hF]
    have e : Set.Finite.toFinset hF = Finset.univ.biUnion fun i => Set.Finite.toFinset (hI (w i)) := by
      ext q
      simp [hU]
    rw [e, Finset.sum_biUnion]
    · exact Finset.sum_congr rfl fun i _ => double_coset_operator_sum ρ I I (w i) (hI _) v
    · intro i _ j _ hij
      rw [Function.onFun, Finset.disjoint_left]
      intro q hi hj
      obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
      rw [Set.Finite.mem_toFinset] at hi hj
      have hg : g ∈ K := (hK g).1 (hU ▸ Set.mem_iUnion.2 ⟨i, hi⟩)
      exact hij ((hu g hg).unique ((mem_orb _ _ _ _).1 hi) ((mem_orb _ _ _ _).1 hj))
  · ext
    change (hk2 ρ K I 1 (inc ρ h v) : M) = _
    rw [double_coset_operator_sum ρ K I 1 hF, Finset.sum_congr rfl (g := fun _ => (v : M))]
    · have hs : MulAction.stabilizer K ((1 : G) : G ⧸ I) = I.subgroupOf K := by
        ext k
        rw [MulAction.mem_stabilizer_iff, Subgroup.mem_subgroupOf]
        change (((k : G) * 1 : G) : G ⧸ I) = _ ↔ _
        rw [eq_comm, QuotientGroup.eq]
        simp
      rw [Finset.sum_const, ← Set.ncard_eq_toFinset_card _ hF, ← MulAction.index_stabilizer, hs,
        Submodule.coe_smul, Nat.cast_smul_eq_nsmul]
      rfl
    · intro q hq
      rw [Set.Finite.mem_toFinset, ← q.out_eq'] at hq
      exact v.2 _ ((hK _).1 hq)
