import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.EpsilonEtaMatrices.EpsilonEtaTensorDual

open Matrix Filter NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa

private theorem phi_sub (l : ℕ) {Γ : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    (hΦ : PhiCond Γ l) (H : Subgroup Γ) (hH : IsOpen (H : Set Γ)) : PhiCond H l := by
  intro K hK
  have hK' : IsOpen ((K.map H.subtype : Subgroup Γ) : Set Γ) := by
    rw [Subgroup.coe_map]
    exact hH.isOpenMap_subtype_val _ hK
  haveI := hΦ _ hK'
  let e : K ≃* K.map H.subtype := K.equivMapOfInjective H.subtype H.subtype_injective
  have hc : Continuous (e.symm : K.map H.subtype → K) := by
    have hind : Topology.IsInducing (fun k : K => ((k : H) : Γ)) :=
      Topology.IsInducing.subtypeVal.comp Topology.IsInducing.subtypeVal
    rw [hind.continuous_iff]
    have hfun : (fun k : K => ((k : H) : Γ)) ∘ e.symm = fun γ : K.map H.subtype => (γ : Γ) := by
      funext γ
      have h1 := K.coe_equivMapOfInjective_apply H.subtype H.subtype_injective (e.symm γ)
      simp only [Function.comp_apply]
      rw [← H.coe_subtype, ← h1]
      simp [e]
    rw [hfun]
    exact continuous_subtype_val
  refine Finite.of_injective
    (β := {ψ : (K.map H.subtype) →* Multiplicative (ZMod l) // IsOpen (ψ.ker : Set (K.map H.subtype))})
    (fun φ => ⟨φ.1.comp e.symm.toMonoidHom, ?_⟩) ?_
  · have hk : ((φ.1.comp e.symm.toMonoidHom).ker : Set (K.map H.subtype)) = e.symm ⁻¹' (φ.1.ker : Set K) := by
      ext γ
      exact Iff.rfl
    rw [hk]
    exact φ.2.preimage hc
  · intro φ φ' h
    apply Subtype.ext
    ext k
    have h2 := congrArg (fun ψ => ψ.1 (e k)) h
    simpa using h2

private theorem finite_addMonoidHom_zmod_of_finite (l : ℕ) [Fact l.Prime] (M : Type) [AddCommGroup M] [Finite M] :
    Finite (M →+ ZMod l) := by
  haveI : NeZero l := ⟨(Fact.out : l.Prime).ne_zero⟩
  exact Finite.of_injective (fun f : M →+ ZMod l => (f : M → ZMod l)) DFunLike.coe_injective

private theorem eq_zero_of_forall_hom_zmod_eq_zero_of_l_smul (l : ℕ) [Fact l.Prime] (M : Type) [AddCommGroup M] (hl : ∀ m : M, l • m = 0)
    (m : M) (h : ∀ f : M →+ ZMod l, f m = 0) : m = 0 := by
  letI : Module (ZMod l) M := AddCommGroup.zmodModule hl
  let b := Module.Basis.ofVectorSpace (ZMod l) M
  apply b.repr.injective
  ext i
  have := h (b.coord i).toAddMonoidHom
  rw [LinearEquiv.map_zero, Finsupp.coe_zero, Pi.zero_apply]
  simpa using this

theorem UpperTheory.V.Pa.finZ :
    ∀ (l : ℕ) [Fact l.Prime] (R Γ M : Type) [CommRing R] [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ] [AddCommGroup M] [Module R M] [Finite M] (ρ : Representation R Γ M), PhiCond Γ l → LC ρ → (∀ m : M, l • m = 0) → Finite (Zl ρ) ∧ ∀ H : Subgroup Γ, IsOpen (H : Set Γ) → PhiCond H l := by
  intro l _ R Γ M _ _ _ _ _ _ _ _ ρ hΦ hρ hl
  refine ⟨?_, fun H hH => phi_sub l hΦ H hH⟩
  let N : Subgroup Γ :=
    { carrier := {g | ∀ m, ρ g m = m}
      mul_mem' := by
        intro a b ha hb m
        simp only [Set.mem_setOf_eq] at ha hb
        rw [map_mul, Module.End.mul_apply, hb, ha]
      one_mem' := by
        intro m
        simp
      inv_mem' := by
        intro a ha m
        simp only [Set.mem_setOf_eq] at ha
        have h1 := ha (ρ a⁻¹ m)
        rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply] at h1
        exact h1.symm }
  have hN : IsOpen (N : Set Γ) := by
    have hset : (N : Set Γ) = ⋂ m : M, (fun g => ρ g m) ⁻¹' {m} := by
      ext g
      simp [N]
    rw [hset]
    exact isOpen_iInter_of_finite (fun m => (hρ m).isOpen_fiber m)
  haveI : Finite (Γ ⧸ N) := Subgroup.quotient_finite_of_isOpen N hN
  haveI : Finite (M →+ ZMod l) := finite_addMonoidHom_zmod_of_finite l M
  haveI := hΦ N hN
  have z1 : ∀ z ∈ Zl ρ, z 1 = 0 := by
    intro z hz
    have h := ((mem_Zl ρ).1 hz).2 1 1
    simpa using h
  have zN : ∀ z ∈ Zl ρ, ∀ a b : Γ, a ∈ N → z (a * b) = z a + z b := by
    intro z hz a b ha
    rw [((mem_Zl ρ).1 hz).2, ha]
  refine Finite.of_injective
    (β := (Γ ⧸ N → M) × ((M →+ ZMod l) →
      {φ : N →* Multiplicative (ZMod l) // IsOpen (φ.ker : Set N)}))
    (fun z => (fun q => z.1 q.out, fun f =>
      ⟨⟨⟨fun k => Multiplicative.ofAdd (f (z.1 k)), ?_⟩, ?_⟩, ?_⟩)) ?_
  · show Multiplicative.ofAdd (f (z.1 ((1 : N) : Γ))) = 1
    rw [Subgroup.coe_one, z1 _ z.2, map_zero, ofAdd_zero]
  · intro k k'
    show Multiplicative.ofAdd (f (z.1 ((k * k' : N) : Γ))) =
      Multiplicative.ofAdd (f (z.1 k)) * Multiplicative.ofAdd (f (z.1 k'))
    rw [Subgroup.coe_mul, zN _ z.2 _ _ k.2, map_add, ofAdd_add]
  · have hlc : IsLocallyConstant (fun k : N => Multiplicative.ofAdd (f (z.1 k))) :=
      (((mem_Zl ρ).1 z.2).1.comp_continuous continuous_subtype_val).comp _
    rw [MonoidHom.coe_ker]
    exact hlc.isOpen_fiber 1
  · intro z z' h
    simp only [Prod.mk.injEq] at h
    obtain ⟨h1, h2⟩ := h
    apply Subtype.ext
    funext g
    have key : ∀ k : N, z.1 k = z'.1 k := by
      intro k
      have hf : ∀ f : M →+ ZMod l, f (z.1 k - z'.1 k) = 0 := by
        intro f
        have h3 := congrArg (fun ψ : {φ : N →* Multiplicative (ZMod l) // IsOpen (φ.ker : Set N)} =>
          Multiplicative.toAdd (ψ.1 k)) (congrFun h2 f)
        simp only [MonoidHom.coe_mk, OneHom.coe_mk, toAdd_ofAdd] at h3
        rw [map_sub, h3, sub_self]
      exact sub_eq_zero.1 (eq_zero_of_forall_hom_zmod_eq_zero_of_l_smul l M hl _ hf)
    obtain ⟨k, hk⟩ := QuotientGroup.mk_out_eq_mul N g
    have hg : g = (QuotientGroup.mk g : Γ ⧸ N).out * ((k⁻¹ : N) : Γ) := by
      rw [hk]
      simp [mul_assoc]
    have h1' : z.1 (QuotientGroup.mk g : Γ ⧸ N).out = z'.1 (QuotientGroup.mk g : Γ ⧸ N).out :=
      congrFun h1 (QuotientGroup.mk g)
    rw [hg, ((mem_Zl ρ).1 z.2).2, ((mem_Zl ρ).1 z'.2).2, key, h1']
