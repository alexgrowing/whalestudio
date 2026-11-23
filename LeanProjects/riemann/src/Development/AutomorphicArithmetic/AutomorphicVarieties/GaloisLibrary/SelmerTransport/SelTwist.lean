import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.RestrictionMemInvariantH1

open ReciprocityTheory.Gal UpperTheory.V.Base

section

variable {R G M : Type} [CommRing R] [Group G] [TopologicalSpace G] [AddCommGroup M] [Module R M]
  [TopologicalSpace M] [IsTopologicalAddGroup M] [ContinuousConstSMul R M]

private noncomputable def h1MapOfAgreeOnSubgroup (ρ ρ' : Representation R G M) (U : Subgroup G)
    (h : ∀ (u : U) m, ρ u m = ρ' u m) : H1U ρ U →ₗ[R] H1U ρ' U :=
  pairH1DecompositionMap _ _ (MonoidHom.id U) continuous_id LinearMap.id continuous_id fun u m => h u m

private theorem sameH1_mk (ρ ρ' : Representation R G M) (U : Subgroup G)
    (h : ∀ (u : U) m, ρ u m = ρ' u m) (z : Z1U ρ U) :
    ∃ z' : Z1U ρ' U, h1MapOfAgreeOnSubgroup ρ ρ' U h (Submodule.Quotient.mk z) = Submodule.Quotient.mk z' ∧
      ∀ u : U, z'.1 u = z.1 u := ⟨_, rfl, fun _ => rfl⟩

private theorem sameH1_involutive (ρ ρ' : Representation R G M) (U : Subgroup G)
    (h : ∀ (u : U) m, ρ u m = ρ' u m) (h' : ∀ (u : U) m, ρ' u m = ρ u m) (x : H1U ρ U) :
    h1MapOfAgreeOnSubgroup ρ' ρ U h' (h1MapOfAgreeOnSubgroup ρ ρ' U h x) = x := by
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rfl

private theorem sameH1_mem_localSelmer (ρ ρ' : Representation R G M) (U : Subgroup G)
    (h : ∀ (u : U) m, ρ u m = ρ' u m) (𝒟 : Set (Subgroup G)) (x : H1U ρ U) (hx : x ∈ LocSel ρ U 𝒟) :
    h1MapOfAgreeOnSubgroup ρ ρ' U h x ∈ LocSel ρ' U 𝒟 := by
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  obtain ⟨z', e, f⟩ := sameH1_mk ρ ρ' U h z
  rw [e]
  rw [mk_mem_locSel] at hx ⊢
  intro D hD
  obtain ⟨m, hm⟩ := hx D hD
  exact ⟨m, fun u hu => by rw [f, hm u hu, h]⟩

private noncomputable def sameSel (ρ ρ' : Representation R G M) (U : Subgroup G)
    (h : ∀ (u : U) m, ρ u m = ρ' u m) (𝒟 : Set (Subgroup G)) : LocSel ρ U 𝒟 ≃ₗ[R] LocSel ρ' U 𝒟 :=
  LinearEquiv.ofLinear ((h1MapOfAgreeOnSubgroup ρ ρ' U h).restrict (sameH1_mem_localSelmer ρ ρ' U h 𝒟))
    ((h1MapOfAgreeOnSubgroup ρ' ρ U fun u m => (h u m).symm).restrict (sameH1_mem_localSelmer ρ' ρ U _ 𝒟))
    (LinearMap.ext fun x => Subtype.ext (sameH1_involutive ρ' ρ U _ h x.1))
    (LinearMap.ext fun x => Subtype.ext (sameH1_involutive ρ ρ' U h _ x.1))

private theorem sameH1_conjugation_scalar [IsTopologicalGroup G] [DiscreteTopology M] (ρ ρ' : Representation R G M)
    (U : Subgroup G) [U.Normal] (h : ∀ (u : U) m, ρ u m = ρ' u m) (g : G) (c : R)
    (hg : ∀ m, ρ g m = c • ρ' g m) (x : H1U ρ U) :
    h1MapOfAgreeOnSubgroup ρ ρ' U h (conjRep ρ U g x) = c • conjRep ρ' U g (h1MapOfAgreeOnSubgroup ρ ρ' U h x) := by
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  obtain ⟨z₁, e₁, f₁⟩ := sameH1_mk ρ ρ' U h z
  obtain ⟨z₂, e₂, f₂⟩ := conjU_mk ρ' U g z₁
  obtain ⟨z₃, e₃, f₃⟩ := conjU_mk ρ U g z
  obtain ⟨z₄, e₄, f₄⟩ := sameH1_mk ρ ρ' U h z₃
  rw [conjRep_apply, conjRep_apply, e₁, e₂, e₃, e₄, ← Submodule.Quotient.mk_smul]
  congr 1
  refine Subtype.ext (funext fun u => ?_)
  show z₄.1 u = c • z₂.1 u
  rw [f₄, f₃, f₂, f₁, hg]

end

theorem UpperTheory.V.Base.selTwist :
    ∀ (R G M : Type) [CommRing R] [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup M] [Module R M]
      [TopologicalSpace M] [IsTopologicalAddGroup M] [ContinuousConstSMul R M] [DiscreteTopology M] (ρ : Representation R G M) (ρ' : Representation R G M) (θ : G →* Rˣ), (∀ g m, ρ g m = ((θ g : Rˣ) : R) • ρ' g m) →
      ∀ (U : Subgroup G) [U.Normal], (∀ u ∈ U, θ u = 1) → ∀ (𝒟 : Set (Subgroup G)) (h𝒟 : ConjStable 𝒟),
      (∃ Φ : LocSel ρ U 𝒟 ≃ₗ[R] LocSel ρ' U 𝒟, ∀ g x, Φ (selRep ρ U h𝒟 g x) = ((θ g : Rˣ) : R) • selRep ρ' U h𝒟 g (Φ x)) ∧
      ∀ (W : Subgroup G) (φ : W →* Rˣ), Module.length R (selEig ρ U h𝒟 W (θ.comp W.subtype * φ)) = Module.length R (selEig ρ' U h𝒟 W φ) := by
  intro R G M _ _ _ _ _ _ _ _ _ _ ρ ρ' θ hθ U _ hU 𝒟 h𝒟
  have h : ∀ (u : U) m, ρ u m = ρ' u m := fun u m => by
    rw [hθ, hU u u.2, Units.val_one, one_smul]
  have hΦ : ∀ g x, sameSel ρ ρ' U h 𝒟 (selRep ρ U h𝒟 g x) =
      ((θ g : Rˣ) : R) • selRep ρ' U h𝒟 g (sameSel ρ ρ' U h 𝒟 x) := fun g x =>
    Subtype.ext (sameH1_conjugation_scalar ρ ρ' U h g _ (hθ g) x.1)
  refine ⟨⟨_, hΦ⟩, fun W φ => ?_⟩
  generalize sameSel ρ ρ' U h 𝒟 = Φ at hΦ
  have key : ∀ x, x ∈ selEig ρ U h𝒟 W (θ.comp W.subtype * φ) ↔ Φ x ∈ selEig ρ' U h𝒟 W φ := by
    intro x
    rw [mem_eig, mem_eig]
    refine forall_congr' fun w => ?_
    show selRep ρ U h𝒟 w x = ((θ w * φ w : Rˣ) : R) • x ↔ selRep ρ' U h𝒟 w (Φ x) = ((φ w : Rˣ) : R) • Φ x
    rw [← Φ.injective.eq_iff, hΦ, map_smul, Units.val_mul, mul_smul]
    exact (Units.isUnit (θ w)).smul_left_cancel
  have hmap : (selEig ρ U h𝒟 W (θ.comp W.subtype * φ)).map (Φ : _ →ₗ[R] _) = selEig ρ' U h𝒟 W φ := by
    ext y
    obtain ⟨x, rfl⟩ := Φ.surjective y
    rw [← key]
    exact ⟨fun ⟨x', hx', e⟩ => Φ.injective e ▸ hx', fun hx => ⟨x, hx, rfl⟩⟩
  exact (Φ.ofSubmodules _ _ hmap).length_eq
