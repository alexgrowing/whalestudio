import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.ConjStableShaFam
import ReciprocityTheory.GroupCohomology.ImportsAlt

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base

namespace UpperTheory.V.Base

open ReciprocityTheory.Coh

section

variable {R Γ M : Type} [CommRing R] [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [AddCommGroup M]
  [Module R M] [TopologicalSpace M] [IsTopologicalAddGroup M] [ContinuousConstSMul R M]

private theorem transg_cont (σ : Representation R Γ M) (hσ : ContAction σ) (N : Subgroup Γ) [N.Normal] :
    ContAction (σ.quotientToInvariants N) := by
  unfold ReciprocityTheory.Gal.ContAction
  have hq := (QuotientGroup.isOpenQuotientMap_mk (N := N)).prodMap
    (IsOpenQuotientMap.id (X := Representation.invariants (σ.comp N.subtype)))
  rw [← hq.continuous_comp_iff]
  refine continuous_induced_rng.2 ?_
  exact hσ.comp (f := fun p : Γ × Representation.invariants (σ.comp N.subtype) => (p.1, (p.2 : M)))
    (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))

private theorem transg_top [DiscreteTopology M] [CompactSpace Γ] [T2Space Γ] [TotallyDisconnectedSpace Γ]
    (σ : Representation R Γ M) (hσ : ContAction σ) (N : Subgroup Γ) [N.Normal] (hN : IsClosed (N : Set Γ)) :
    ∃ tg : (conjRep σ N).invariants →ₗ[R] H2 (σ.quotientToInvariants N),
      ∀ x, tg x = 0 ↔ x.1 ∈ LinearMap.range (resH1 σ N.subtype continuous_subtype_val) := by
  let A : TRep R Γ := { V := M, rho := σ, cont := hσ }
  let Q : TRep R (Γ ⧸ N) :=
    { V := Representation.invariants (σ.comp N.subtype), rho := σ.quotientToInvariants N, cont := transg_cont σ hσ N }
  let P : Pair Q A := ⟨QuotientGroup.mk' N, Submodule.subtype _, QuotientGroup.continuous_mk,
    continuous_subtype_val, fun _ _ => rfl⟩
  have hP : IsInvRep A N Q P := by
    refine ⟨rfl, Topology.IsEmbedding.subtypeVal, fun m => ?_⟩
    show m ∈ LinearMap.range (Submodule.subtype _) ↔ _
    rw [Submodule.range_subtype]
    exact ⟨fun h g hg => h ⟨g, hg⟩, fun h g => h g.1 g.2⟩
  obtain ⟨a₀, a₁, a₂, ha⟩ := exists_isLow A
  obtain ⟨n₀, n₁, n₂, hn⟩ := exists_isLow (A.resSub N)
  obtain ⟨q₀, q₁, q₂, hq⟩ := exists_isLow Q
  haveI : DiscreteTopology A.V := ‹DiscreteTopology M›
  let I : Submodule R ((A.resSub N).H 1) := (conjRep σ N).invariants.comap n₁.toLinearMap
  obtain ⟨tg, htg, -⟩ := fiveTerm_holds R Γ A N hN Q P hP I (by
    intro x
    constructor
    · intro hx s c h1 h2
      apply n₁.injective
      rw [(lowNat_holds R N N _ _ c _ _ _ _ _ _ hn hn).2.1]
      obtain ⟨φ, u, hφ, hu, he⟩ := c
      obtain rfl : φ = conjHom N s := MonoidHom.ext fun g => Subtype.ext (h1 g)
      obtain rfl : u = σ s := LinearMap.ext h2
      exact hx s
    · intro hx s
      let c : Pair (A.resSub N) (A.resSub N) := ⟨conjHom N s, σ s, continuous_conjHom N s,
        continuous_of_discreteTopology (α := M), fun u (m : M) => by
          show σ s (σ (s⁻¹ * u * s) m) = σ u (σ s m)
          rw [← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul]
          simp [mul_assoc]⟩
      have e := congrArg n₁ (hx s c (fun _ => rfl) fun _ => rfl)
      rw [(lowNat_holds R N N _ _ c _ _ _ _ _ _ hn hn).2.1] at e
      exact e)
  let k : (conjRep σ N).invariants →ₗ[R] I :=
    { toFun := fun x => ⟨n₁.symm x.1, fun s => by
        have e := n₁.apply_symm_apply x.1
        exact (congrArg (conjRep σ N s) e).trans ((x.2 s).trans e.symm)⟩
      map_add' := fun x y => Subtype.ext (n₁.symm.map_add x.1 y.1)
      map_smul' := fun r x => Subtype.ext (n₁.symm.map_smul r x.1) }
  refine ⟨q₂.toLinearMap.comp (tg.comp k), fun x => ?_⟩
  have hr := (lowNat_holds R Γ N _ _ (Pair.res A N.subtype continuous_subtype_val) _ _ _ _ _ _ ha hn).2.1
  refine (q₂.map_eq_zero_iff.trans (htg (k x))).trans ⟨?_, ?_⟩
  · rintro ⟨y, hy⟩
    refine ⟨a₁ y, ?_⟩
    have e := congrArg n₁ hy
    rw [hr] at e
    exact e.trans (n₁.apply_symm_apply x.1)
  · rintro ⟨y, hy⟩
    refine ⟨a₁.symm y, n₁.injective ?_⟩
    rw [hr, LinearEquiv.apply_symm_apply]
    exact hy.trans (n₁.apply_symm_apply x.1).symm

end

end UpperTheory.V.Base

theorem UpperTheory.V.Base.transg :
    ∀ (R G M : Type) [CommRing R] [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup M] [Module R M]
      [TopologicalSpace M] [IsTopologicalAddGroup M] [ContinuousConstSMul R M] [DiscreteTopology M] (ρ : Representation R G M) [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G], ContAction ρ → ∀ (U' U : Subgroup G) [U'.Normal] (h : U' ≤ U), IsClosed (U : Set G) → IsClosed (U' : Set G) →
      ∃ tg : resCoker ρ h →ₗ[R] H2 (quotRep ρ U U'), Function.Injective tg := by
  intro R G M _ _ _ _ _ _ _ _ _ _ ρ _ _ _ hρ U' U _ h hU hU'
  haveI : CompactSpace U := isCompact_iff_compactSpace.1 hU.isCompact
  let σ : Representation R U M := ρ.comp U.subtype
  have hσ : ContAction σ := hρ.comp (f := fun p : U × M => ((p.1 : G), p.2))
    ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)
  obtain ⟨tg, htg⟩ := transg_top σ hσ (U'.subgroupOf U) (hU'.preimage continuous_subtype_val)
  let j : H1U ρ U' →ₗ[R] H1U σ (U'.subgroupOf U) :=
    pairH1DecompositionMap _ _ (Subgroup.subgroupOfEquivOfLe h).toMonoidHom
      ((continuous_subtype_val.comp continuous_subtype_val).subtype_mk _) LinearMap.id continuous_id fun _ _ => rfl
  let j' : H1U σ (U'.subgroupOf U) →ₗ[R] H1U ρ U' :=
    pairH1DecompositionMap _ _ (Subgroup.subgroupOfEquivOfLe h).symm.toMonoidHom
      ((continuous_subtype_val.subtype_mk _).subtype_mk _) LinearMap.id continuous_id fun _ _ => rfl
  have h1 : ∀ x, j' (j x) = x := fun x => by
    obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    rfl
  have h2 : ∀ y, j (resU ρ h y) = resH1 σ (U'.subgroupOf U).subtype continuous_subtype_val y := fun x => by
    obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    rfl
  have h3 : ∀ (g : U) x, conjRep σ (U'.subgroupOf U) g (j x) = j (conjRep ρ U' g x) := fun g x => by
    obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    rfl
  let k : invariantsUnderSubgroupH1 ρ U U' →ₗ[R] (conjRep σ (U'.subgroupOf U)).invariants :=
    (j.comp (Submodule.subtype _)).codRestrict _ fun x g => (h3 g x.1).trans (congrArg j (x.2 g))
  have hk : ∀ x : invariantsUnderSubgroupH1 ρ U U', tg (k x) = 0 ↔ x.1 ∈ LinearMap.range (resU ρ h) := fun x => by
    refine (htg (k x)).trans ⟨?_, ?_⟩
    · rintro ⟨y, hy⟩
      exact ⟨y, by rw [← h1 (resU ρ h y), h2, hy]; exact h1 x.1⟩
    · rintro ⟨y, hy⟩
      exact ⟨y, (h2 y).symm.trans (congrArg j hy)⟩
  refine ⟨Submodule.liftQ _ (tg.comp k) fun x hx => (hk x).2 hx, ?_⟩
  rw [← LinearMap.ker_eq_bot]
  exact Submodule.ker_liftQ_eq_bot _ _ _ fun x hx => (hk x).1 hx
