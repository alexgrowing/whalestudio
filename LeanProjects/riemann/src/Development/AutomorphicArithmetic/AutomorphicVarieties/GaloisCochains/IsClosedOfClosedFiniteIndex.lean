import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisCochains.GLinkQuot
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ExistsLocallyConstantDOneEqCocycleOfTameInertia

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module UpperTheory.V UpperTheory.V.Fr UpperTheory.V.GC

private theorem isClosed_of_closed_finite_index {Γ : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    (I J : Subgroup Γ) (hJI : J ≤ I) (hJ : IsClosed (J : Set Γ)) (h : J.relIndex I ≠ 0) : IsClosed (I : Set Γ) := by
  haveI : (J.subgroupOf I).FiniteIndex := ⟨h⟩
  have e : (I : Set Γ) = ⋃ q : I ⧸ J.subgroupOf I, (fun g : Γ => ((q.out : I) : Γ)⁻¹ * g) ⁻¹' (J : Set Γ) := by
    ext g
    simp only [Set.mem_iUnion, Set.mem_preimage, SetLike.mem_coe]
    constructor
    · intro hg
      refine ⟨(QuotientGroup.mk (⟨g, hg⟩ : I)), ?_⟩
      have := QuotientGroup.eq.1 (QuotientGroup.out_eq' (QuotientGroup.mk (⟨g, hg⟩ : I) : I ⧸ J.subgroupOf I))
      exact Subgroup.mem_subgroupOf.1 this
    · rintro ⟨q, hq⟩
      have := I.mul_mem (q.out : I).2 (hJI hq)
      rwa [mul_inv_cancel_left] at this
  rw [e]
  exact isClosed_iUnion_of_finite fun q => hJ.preimage (by fun_prop)

theorem UpperTheory.V.GC.H2_unramified_inflation :
    ∀ (l : ℕ) [Fact l.Prime] (Γ : Type) [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ] [T2Space Γ] [TotallyDisconnectedSpace Γ] (k : Type) [Field k] [Finite k] [CharP k l] (M : Type) [AddCommGroup M] [Module k M] [Module.Finite k M] [TopologicalSpace M] [DiscreteTopology M] (ρ : Representation k Γ M), ContAction ρ → ∀ (I J : Subgroup Γ) [I.Normal] [J.Normal] (φ : Γ), J ≤ I → IsClosed (J : Set Γ) → ¬ l ∣ J.relIndex I → (∀ j ∈ J, ρ j = 1) →
    (I ⊔ Subgroup.zpowers φ).topologicalClosure = ⊤ → (∀ n : ℕ, 0 < n → ∃ d : Γ →* Multiplicative (ZMod n), IsLocallyConstant d ∧ (∀ s ∈ I, d s = 1) ∧ d φ = Multiplicative.ofAdd 1) →
    ∀ z : Z2 ρ, (∀ s t, ∀ j ∈ J, ∀ j' ∈ J, z.1 (s * j, t * j') = z.1 (s, t)) → ∃ b : Γ → M, IsLocallyConstant b ∧ (∀ s, ∀ j ∈ J, b (s * j) = b s) ∧ ∀ s t, z.1 (s, t) = ρ s (b t) - b (s * t) + b s := by
  intro l hl Γ _ _ _ _ _ _ k _ _ _ M _ _ _ _ _ ρ hρ I J _ _ φ hJI hJ hidx hJρ hφ hd z hz
  haveI : Finite M := Module.finite_of_finite k
  have hker : IsOpen (ρ.ker : Set Γ) := by
    have e : (ρ.ker : Set Γ) = ⋂ m : M, (fun g : Γ => ρ g m) ⁻¹' {m} := by
      ext g
      simp only [SetLike.mem_coe, MonoidHom.mem_ker, Set.mem_iInter, Set.mem_preimage, Set.mem_singleton_iff]
      exact ⟨fun h m => by rw [h]; rfl, fun h => LinearMap.ext h⟩
    rw [e]
    exact isOpen_iInter_of_finite fun m =>
      (isOpen_discrete _).preimage (Continuous.comp hρ (Continuous.prodMk_left m))
  have hI : IsClosed (I : Set Γ) := isClosed_of_closed_finite_index I J hJI hJ (fun h => hidx (h ▸ dvd_zero l))
  obtain ⟨a, ha1, ha2, ha3⟩ := UpperTheory.V.Alg.exists_locallyConstant_dOne_eq_cocycle_of_tame_inertia l k Γ M ρ hker I J hI hJ hJI (fun j hj => hJρ j hj) hidx ⟨φ, hφ⟩
    (by
      intro n
      obtain ⟨d, hd1, hd2, hd3⟩ := hd (l ^ n) (pow_pos hl.out.pos n)
      haveI : NeZero (l ^ n) := ⟨(pow_pos hl.out.pos n).ne'⟩
      refine ⟨d.ker, hd1.isOpen_fiber 1, fun s hs => hd2 s hs, ?_⟩
      have hs : d.range = ⊤ := by
        rw [eq_top_iff]
        intro x _
        refine ⟨φ ^ (Multiplicative.toAdd x).val, ?_⟩
        rw [map_pow, hd3, ← ofAdd_nsmul, nsmul_eq_mul, mul_one, ZMod.natCast_zmod_val, ofAdd_toAdd]
      rw [Subgroup.index_ker, hs, Subgroup.card_top, Nat.card_congr Multiplicative.toAdd, Nat.card_zmod])
    z.1 ((IsLocallyConstant.iff_continuous _).2 z.2.1)
    (by
      intro s t u
      have e := z.2.2 s t u
      rw [← sub_eq_zero, ← e]
      abel) hz
  refine ⟨a, ha1, ha2, fun s t => ?_⟩
  rw [← ha3]
  simp only [UpperTheory.V.Alg.dOne]
  abel
